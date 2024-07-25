from typing import List
import ast
import inspect
from z3 import *

MAX_STRING_SIZE = 300

NUL = (1 << 64) - 1

def list_to_array(lst):
    array = K(IntSort(), BitVecVal(NUL, 64))
    for i in range(len(lst)):
        array = Store(array, i, lst[i])
    
    return array

def array_to_list(array):
    lst = []
    i = 0
    while(simplify(Select(array, i) != nul)) :
        lst.append(simplify(Select(array, i)))
        i += 1

    return lst

def list_eq(lst1, lst2):
    if len(lst1) == len(lst2):
        checks = []
        for i, j in zip(lst1, lst2):
            if type(i) == list and type(j) == list:
                checks.append(list_eq(i, j))
            else:
                checks.append(i == j)

        return z3.And(checks)
    else:
        return False

def z3_expr(node, vars=None, debug=False):
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
            v = z3.BitVec(name, 64)
            vars[name] = v
            if debug:
                print(f"Added variable: {name} -> {v}")  # Debugging: Log added variables
            return v
    if debug:
        print(f"Processing node: {type(node).__name__}")  # Debugging: Log input node type

    # Binary operators.
    if isinstance(node, ast.BinOp):  
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
        elif isinstance(node.op, ast.Pow):
            return z3.BitVecVal(lhs.as_long() ** rhs.as_long(), 64), vars
        elif isinstance(node.op, ast.Mod):
            return lhs % rhs, vars
        else:
            raise Exception(f"z3_expr: BinOP {node.op.id} not implemented yet")

    # Negation
    elif isinstance(node, ast.UnaryOp):  
        sub, vars = z3_expr(node.operand, vars)
        if isinstance(node.op, ast.USub):
            return -sub, vars

    # Literal number.
    elif isinstance(node, ast.Num):  
        return z3.BitVecVal(node.n, 64), vars

    # Constant
    elif isinstance(node, ast.Constant):
        if type(node.value) == str:
            return z3.StringVal(node.value), vars
        elif type(node.value) == int:
            return z3.IntVal(node.value), vars
        elif type(node.value) == bool:
            return z3.BoolVal(node.value), vars
        elif type(node.value) == float:
            return z3.RealVal(node.value), vars
        else:
            raise Exception(f"z3_expr: type {type(node.value)} not implemented yet")

    # Variable lookup.
    elif isinstance(node, ast.Name):  
        return get_var(node.id), vars
    
    # Conditional.
    elif isinstance(node, ast.IfExp): 
        cond, vars = z3_expr(node.test, vars)
        true, vars = z3_expr(node.body, vars)
        false, vars = z3_expr(node.orelse, vars)
        return z3.If(cond != 0, true, false), vars

    # Compare
    elif isinstance(node, ast.Compare):
        cmpop_map = {
                ast.Eq: lambda x, y: x == y,
                ast.NotEq: lambda x, y: x != y,
                ast.Lt: lambda x, y: x < y,
                ast.LtE: lambda x, y: x <= y,
                ast.Gt: lambda x, y: x > y,
                ast.GtE: lambda x, y: x >= y,
                ast.In: lambda x, y: x in y,
                ast.NotIn: lambda x, y: x not in y,
            }
        lhs, vars = z3_expr(node.left, vars)
        op = node.ops[0] 
        rhs, vars = z3_expr(node.comparators[0], vars)

        return cmpop_map[type(op)](lhs, array_to_list(rhs)), vars

    # BoolOp
    elif isinstance(node, ast.BoolOp):
        if isinstance(node.op, ast.And):
            cum_res = z3.And(True)
            for v in node.values:
                res, vars = z3_expr(v, vars)
                cum_res = z3.And(cum_res, res)
        elif isinstance(node.op, ast.Or):
            cum_res = z3.Or(False)
            for v in node.values:
                res, vars = z3_expr(v, vars)
                cum_res = z3.Or(cum_res, res)
        else:
            raise Exception("z3_expr: BoolOp not implemented yet")
        return cum_res, vars

    # List
    elif isinstance(node, ast.List):
        elts_list = []
        for elt in node.elts:
            z3_elt, vars = z3_expr(elt, vars)
            elts_list.append(z3_elt)

        return list_to_array(elts_list), vars

    # Function Call
    elif isinstance(node, ast.Call):
        if node.func.id == "sum":
            arg, vars = z3_expr(node.args[0])
            return sum(array_to_list(arg)), vars
        elif node.func.id == "all":
            arg, vars = z3_expr(node.args[0])
            return z3.And(array_to_list(arg)), vars
        else:
            raise Exception(f"z3_expr: function {node.func.id} not implemented")

    # Subscripts
    elif isinstance(node, ast.Subscript):
        
        value, vars = z3_expr(node.value, vars)
        if not isinstance(node.slice, ast.Slice):
            index, vars = z3_expr(node.slice, vars)

            if isinstance(value, z3.SeqRef):
                return value.at(index.as_long()), vars

            else:
                return value[index.as_long()], vars
        else:
            
            upper, vars = z3_expr(node.slice.upper, vars) if node.slice.upper else (z3.IntVal(len(value)) if not isinstance(value, z3.SeqRef) else z3.IntVal(MAX_STRING_SIZE), vars)
            lower, vars = z3_expr(node.slice.lower, vars) if node.slice.lower else (z3.IntVal(0), vars)
            step, vars = z3_expr(node.slice.step, vars) if node.slice.step else (z3.IntVal(1), vars)

            upper = upper.as_long()
            lower = lower.as_long()
            step = step.as_long()

            
            if isinstance(value, z3.SeqRef):
                s = z3.StringVal("")
                i = lower
                while i < upper:
                    s = Concat(s, value.at(i))
                    i += step

                return s, vars

            else:
                return value[lower:upper:step], vars


    else:
        raise Exception(f"z3_expr: python node {type(node)} not implemented yet")


