import z3
import sys
import ast

# Define a function to parse Python expressions using the ast module
def parse_expression(expr):
    return ast.parse(expr, mode='eval').body

# A language based on a Lark example from:
# https://github.com/lark-parser/lark/wiki/Examples
GRAMMAR = """
?start: sum
  | sum "?" sum ":" sum -> if

?sum: term
  | sum "+" term        -> add
  | sum "-" term        -> sub

?term: item
  | term "*"  item      -> mul
  | term "/"  item      -> div
  | term ">>" item      -> shr
  | term "<<" item      -> shl

?item: NUMBER           -> num
  | "-" item            -> neg
  | CNAME               -> var
  | "(" start ")"

%import common.NUMBER
%import common.WS
%import common.CNAME
%ignore WS
""".strip()


def interp(node, lookup):
    """Evaluate the arithmetic expression.

    Pass a node as an `ast` node for the parsed expression. For
    `lookup`, provide a function for mapping variable names to values.
    """

    if isinstance(node, ast.BinOp):  # Binary operators.
        lhs = interp(node.left, lookup)
        rhs = interp(node.right, lookup)
        if isinstance(node.op, ast.Add):
            return lhs + rhs
        elif isinstance(node.op, ast.Sub):
            return lhs - rhs
        elif isinstance(node.op, ast.Mult):
            return lhs * rhs
        elif isinstance(node.op, ast.Div):
            return lhs / rhs
        elif isinstance(node.op, ast.LShift):
            return lhs << rhs
        elif isinstance(node.op, ast.RShift):
            return lhs >> rhs
    elif isinstance(node, ast.UnaryOp):  # Negation.
        sub = interp(node.operand, lookup)
        if isinstance(node.op, ast.USub):
            return -sub
    elif isinstance(node, ast.Num):  # Literal number.
        return node.n
    elif isinstance(node, ast.Name):  # Variable lookup.
        return lookup(node.id)
    elif isinstance(node, ast.IfExp):  # Conditional.
        cond = interp(node.test, lookup)
        true = interp(node.body, lookup)
        false = interp(node.orelse, lookup)
        return true if cond != 0 else false


def pretty(node, subst={}, paren=False):
    """Pretty-print a tree, with optional substitutions applied.

    If `paren` is true, then loose-binding expressions are
    parenthesized. We simplify boolean expressions "on the fly."
    """

    # Add parentheses?
    if paren:
        def par(s):
            return '({})'.format(s)
    else:
        def par(s):
            return s

    if isinstance(node, ast.BinOp):
        lhs = pretty(node.left, subst, True)
        rhs = pretty(node.right, subst, True)
        c = {
            ast.Add: '+',
            ast.Sub: '-',
            ast.Mult: '*',
            ast.Div: '/',
            ast.LShift: '<<',
            ast.RShift: '>>',
        }[type(node.op)]
        return par('{} {} {}'.format(lhs, c, rhs))
    elif isinstance(node, ast.UnaryOp):
        sub = pretty(node.operand, subst)
        if isinstance(node.op, ast.USub):
            return '-{}'.format(sub)
    elif isinstance(node, ast.Num):
        return str(node.n)
    elif isinstance(node, ast.Name):
        name = node.id
        return str(subst.get(name, name))
    elif isinstance(node, ast.IfExp):
        cond = pretty(node.test, subst)
        true = pretty(node.body, subst)
        false = pretty(node.orelse, subst)
        return par('{} ? {} : {}'.format(cond, true, false))


def run(node, env):
    """Ordinary expression evaluation.

    `env` is a mapping from variable names to values.
    """

    return interp(node, lambda n: env[n])


def z3_expr(node, vars=None):
    """Create a Z3 expression from a tree.

    Return the Z3 expression and a dict mapping variable names to all
    free variables occurring in the expression. All variables are
    represented as BitVecs of width 8. Optionally, `vars` can be an
    initial set of variables.
    """

    vars = dict(vars) if vars else {}

    # Lazily construct a mapping from names to variables.
    def get_var(name):
        if name in vars:
            return vars[name]
        else:
            v = z3.BitVec(name, 8)
            vars[name] = v
            print(f"Added variable: {name} -> {v}")  # Debugging: Log added variables
            return v

    print(f"Processing node: {type(node).__name__}")  # Debugging: Log input node type

    if isinstance(node, ast.BinOp):  # Binary operators.
        lhs, vars = z3_expr(node.left, vars)
        rhs, vars = z3_expr(node.right, vars)
        if isinstance(node.op, ast.Add):
            return lhs + rhs, vars
        elif isinstance(node.op, ast.Sub):
            return lhs - rhs, vars
        elif isinstance(node.op, ast.Mult):
            return lhs * rhs, vars
        elif isinstance(node.op, ast.Div):
            return lhs / rhs, vars
        elif isinstance(node.op, ast.LShift):
            return lhs << rhs, vars
        elif isinstance(node.op, ast.RShift):
            return lhs >> rhs, vars
    elif isinstance(node, ast.UnaryOp):  # Negation.
        sub, vars = z3_expr(node.operand, vars)
        if isinstance(node.op, ast.USub):
            return -sub, vars
    elif isinstance(node, ast.Num):  # Literal number.
        return z3.BitVecVal(node.n, 8), vars
    elif isinstance(node, ast.Name):  # Variable lookup.
        return get_var(node.id), vars
    elif isinstance(node, ast.IfExp):  # Conditional.
        cond, vars = z3_expr(node.test, vars)
        true, vars = z3_expr(node.body, vars)
        false, vars = z3_expr(node.orelse, vars)
        return z3.If(cond != 0, true, false), vars


def solve(phi):
    """Solve a Z3 expression, returning the model.
    """

    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


def model_values(model):
    """Get the values out of a Z3 model.
    """
    return {
        d.name(): model[d]
        for d in model.decls()
    }


def synthesize(tree1, tree2):
    """Given two programs, synthesize the values for holes that make
    them equal.

    `tree1` has no holes. In `tree2`, every variable beginning with the
    letter "h" is considered a hole.
    """

    expr1, vars1 = z3_expr(tree1)
    expr2, vars2 = z3_expr(tree2, vars1)

    # Debugging: Print the contents of vars1 and vars2
    print("vars1:", vars1)
    print("vars2:", vars2)

    # Filter out the variables starting with "h" to get the non-hole
    # variables.
    plain_vars = {k: v for k, v in vars1.items()
                  if not k.startswith('h')}

    # Ensure all variables are correctly initialized as Z3 constants.
    for var in plain_vars.values():
        if not isinstance(var, z3.BitVecRef):
            raise ValueError(f"Invalid variable: {var}")

    # Debugging: Print the contents of plain_vars
    print("plain_vars:", plain_vars)

    # Formulate the constraint for Z3.
    goal = z3.ForAll(
        list(plain_vars.values()),  # For every valuation of variables...
        expr1 == expr2,  # ...the two expressions produce equal results.
    )

    # Solve the constraint.
    return solve(goal)


def ex2(source):
    src1, src2 = source.strip().split('\n')

    tree1 = parse_expression(src1)
    tree2 = parse_expression(src2)

    model = synthesize(tree1, tree2)
    print(pretty(tree1))
    print(pretty(tree2, model_values(model)))


if __name__ == '__main__':
    ex2(sys.stdin.read())