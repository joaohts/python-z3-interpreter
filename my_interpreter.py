from typing import List
import ast
import inspect
from z3 import *
import sys

sys.setrecursionlimit(1000)

MAX_RECURSIONS = 15

NUL = (1 << 64) - 1

def list_to_seq(lst, sort):
    seq = z3.Empty(SeqSort(sort))
    for i in range(len(lst)):
        seq = z3.Concat(seq, Unit(lst[i]))
    
    return seq

def seq_to_list(seq):
    lst = []
    for i in range(simplify(z3.Length(seq)).as_long()):
        lst.append(simplify(z3.simplify(seq.at(i))[0]))
    return lst

def stride(seq, step, rec_num):
    if simplify(seq) == Empty(seq.sort()) or rec_num >= MAX_RECURSIONS:
        return seq
    else:
        return Concat(seq.at(0), stride(SubString(seq, step, Length(seq)), step, rec_num + 1))

def is_in(seq, subseq, rec_num):
    if simplify(seq) == Empty(seq.sort()) or rec_num >= 15:
        return False
    else:
        return z3.Or(simplify(SubString(seq, 0, Length(subseq))).eq(simplify(subseq)), is_in(SubString(seq, 1, Length(seq) - 1), subseq, rec_num + 1))

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
            v = z3.Int(name)
            vars[name] = v
            if debug:
                print(f"Added variable: {name} -> {v}")  # Debugging: Log added variables
            return v
    if debug:
        print(f"Processing node: {type(node).__name__}")  # Debugging: Log input node type

    # Binary operators.
    if isinstance(node, ast.BinOp):  
        lhs, vars = z3_expr(node.left, vars, debug)
        rhs, vars = z3_expr(node.right, vars, debug)
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
            return z3.IntVal(lhs.as_long() ** rhs.as_long()), vars
        elif isinstance(node.op, ast.Mod):
            return lhs % rhs, vars
        else:
            raise Exception(f"z3_expr: BinOP {node.op.id} not implemented yet")

    # Negation
    elif isinstance(node, ast.UnaryOp):  
        sub, vars = z3_expr(node.operand, vars, debug)
        if isinstance(node.op, ast.USub):
            return -sub, vars

    # Literal number.
    elif isinstance(node, ast.Num):  
        return z3.IntVal(node.n), vars

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
        cond, vars = z3_expr(node.test, vars, debug)
        true, vars = z3_expr(node.body, vars, debug)
        false, vars = z3_expr(node.orelse, vars, debug)
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
            }
        lhs, vars = z3_expr(node.left, vars, debug)
        op = node.ops[0]
        rhs, vars = z3_expr(node.comparators[0], vars, debug)
        
        
        if (isinstance(op, ast.In)):
            cum_res = False
            for elt in seq_to_list(rhs):
                cum_res = z3.Or(cum_res, elt == lhs)
            return cum_res, vars
        else:
            return cmpop_map[type(op)](lhs, rhs), vars


    # BoolOp
    elif isinstance(node, ast.BoolOp):
        if isinstance(node.op, ast.And):
            cum_res = z3.And(True)
            for v in node.values:
                res, vars = z3_expr(v, vars, debug)
                cum_res = z3.And(cum_res, res)
        elif isinstance(node.op, ast.Or):
            cum_res = z3.Or(False)
            for v in node.values:
                res, vars = z3_expr(v, vars, debug)
                cum_res = z3.Or(cum_res, res)
        else:
            raise Exception("z3_expr: BoolOp not implemented yet")
        return cum_res, vars

    # List
    elif isinstance(node, ast.List):
        
        elts_list = []
        for elt in node.elts:
            z3_elt, vars = z3_expr(elt, vars, debug)
            elts_list.append(z3_elt)
            sort = z3_elt.sort()


        return list_to_seq(elts_list, sort), vars

    # Function Call
    elif isinstance(node, ast.Call):
        if node.func.id == "sum":
            arg, vars = z3_expr(node.args[0], vars, debug)
            return sum(seq_to_list(arg)), vars
        elif node.func.id == "all":
            
            arg, vars = z3_expr(node.args[0], vars, debug)

            return z3.And(seq_to_list(arg)), vars
        else:
            raise Exception(f"z3_expr: function {node.func.id} not implemented")

    # Subscripts
    elif isinstance(node, ast.Subscript):
        
        value, vars = z3_expr(node.value, vars, debug)
        if not isinstance(node.slice, ast.Slice):
            index, vars = z3_expr(node.slice, vars, debug)

            if value.is_string():
                return value.at(index), vars
            else:
                return value[index], vars
        else:
            
            upper, vars = z3_expr(node.slice.upper, vars, debug) if node.slice.upper else  (z3.Length(value), vars)
            lower, vars = z3_expr(node.slice.lower, vars, debug) if node.slice.lower else (z3.IntVal(0), vars)
            step, vars = z3_expr(node.slice.step, vars, debug) if node.slice.step else (z3.IntVal(1), vars)
            
            
    
            s = z3.SubString(value, lower, (upper-lower))
            s = stride(s, step, 0)

            return s, vars



    else:
        raise Exception(f"z3_expr: python node {type(node)} not implemented yet")


