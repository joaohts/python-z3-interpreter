from z3 import *
import ast
import inspect


y = Int('y')
z = Int('z')

nul = 0b10000000



def list_to_array(lst, sort):
    array = K(sort, 0)
    for i in range(len(lst)):
        array = Store(array, i, lst[i])
    
    return array

def array_to_list(array, length):
    lst = []
    for i in range(length):
        lst.append(simplify(Select(array, i)))

    return lst


# a = Array("w", IntSort(), BitVecSort(8))
# s = Solver()
# s.add(a[10] == 3, a[2] == 2, a[19] == 4)
# s.check()

# m = s.model()
# print(m.decls())
# p = m[m.decls()[0]]

# print(array_to_list(p, 20))
# print(array_to_list(list_to_array([1,2,3,4], IntSort()),10))



def ast_element_finder(sat):
    function_source = inspect.getsource(sat)
    function_ast = ast.parse(function_source)

    # Extract return statement
    return_statement = function_ast.body[0].body[0].value
    print(return_statement.left.slice.step)

def test_str_slice(s: str):
    return s[1:4] == "b"


ast_element_finder(test_str_slice)

print([0,1,2,3,4,5,6,7,8,9][1:-1:2])

s = StringVal("lalala")
print(type(Length(s)))
print(simplify(Length(s)))



