from typing import List
import inspect


def test_prepositional(x: int, y: int):
    return x > 12 and x < 20 and y > 15 and x > y

def test_sum(x: int):
    return sum([1,2,x]) == 6

def test_list_type(x: int):
    return [1,2,x] == [1,2,3]

def test_all(x: int):
    return all([True,True,x == 10])

def test_in(x: int):
    return x in [1,2,3]

def test_str(s: str):
    return s == "Hello World"

def test_str_slice(s: str):
    return s[4] == "b"

def test_index_list(x: int):
    return [1,2,1,x][3] == 3

def test_index_list_nested(x: int):
    return [1,2,1,[1,x]][3][1] == 2

def test_list_slice(x: int):
    return [0,1,2,3,x,5,6,7,8][2:8:2][1] == 10

def test_list_slice_2(x: int):
    return [0,1,2,3,x,5,6,7,8][2::2][1] == 10

def test_string_slice_2(s: str):
    return s[3:5] == "ab"

def test_string_slice_3(s: str):
    return s[3:10:2] == "ab"

def test_string_slice_4(s: str):
    return s[3::2] == "ab"

def test_string_slice_5(s: str):
    return "aaaaaaaa"[3] == s

def test_string_slice_6(s: str):
    return "abcde"[1:3] == s

def test_string_slice_7(s: str):
    return "abcdefgh"[1:6:2] == s

def test_string_slice_8(s: str):
    return "abcdefgh"[1::2] == s



# def test_index_var(x: int):
#     return [1,2,3,4][x] == 4




def study_14(li: List[int], x: str):
    return all([sum(li[:i]) == i + x for i in range(20)])

def study_6(i: int):
    return i % 123 == 4 and i > 10 ** 10






def test_array_type(li: List[int]):
    return li == [1,2,3,4]

info_list = [
    {
        "name": "prepositional_logic",
        "sat": test_prepositional,
        "args": inspect.signature(test_prepositional).parameters,
        "notes": "Tests if prepositional logic converts fine",
        "tags": ["basic"]
    },
    {
        "name": "sum_function",
        "sat": test_sum,
        "args": inspect.signature(test_sum).parameters,
        "notes": "Tests built in sum function from pythoh. Variables can be in the argument.",
        "tags": ["basic", "function"]
    },
    {
        "name": "in_method",
        "sat": test_in,
        "args": inspect.signature(test_in).parameters,
        "notes": "Tests built in 'in' method for fiding elements in lists",
        "tags": ["basic", "list"]
    },
    {
        "name": "all_function",
        "sat": test_all,
        "args": inspect.signature(test_all).parameters,
        "notes": "Tests built in all function from pythoh. Variables can be in the argument.",
        "tags": ["basic", "function"]
    },
    {
        "name": "study_6",
        "sat": study_6,
        "args": inspect.signature(study_6).parameters,
        "notes": "Find an integer greater than 10^10 which is 4 mod 123..",
        "tags": ["math", "list", "study", "ppp"]
    },
    {
        "name": "study_14",
        "sat": study_14,
        "args": inspect.signature(study_14).parameters,
        "notes": "Find a list of integers such that the sum of the first i integers is i, for i=0, 1, 2, ..., 19.",
        "tags": ["math", "list", "study", "ppp"]
    },
    {
        "name": "string_type",
        "sat": test_str,
        "args": inspect.signature(test_str).parameters,
        "notes": "Tests simple solves with str type",
        "tags": ["basic", "string"]
    },
    {
        "name": "string_slice",
        "sat": test_str_slice,
        "args": inspect.signature(test_str_slice).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "string", "slice"]
    },
    {
        "name": "index_list",
        "sat": test_index_list,
        "args": inspect.signature(test_index_list).parameters,
        "notes": "Tests indexed lists",
        "tags": ["basic", "index", "list"]
    },
    {
        "name": "index_list_nested",
        "sat": test_index_list_nested,
        "args": inspect.signature(test_index_list_nested).parameters,
        "notes": "Tests indexed lists",
        "tags": ["basic", "index", "list"]
    },
    {
        "name": "list_slice",
        "sat": test_list_slice,
        "args": inspect.signature(test_list_slice).parameters,
        "notes": "Tests indexed lists",
        "tags": ["basic", "index", "list", "slice"]
    },
    {
        "name": "list_slice_2",
        "sat": test_list_slice_2,
        "args": inspect.signature(test_list_slice_2).parameters,
        "notes": "Tests indexed lists",
        "tags": ["basic", "index", "list", "slice"]
    },
    # {
    #     "name": "index_var",
    #     "sat": test_index_var,
    #     "args": inspect.signature(test_index_var).parameters,
    #     "notes": "Tests indexed lists",
    #     "tags": ["basic", "index", "list"]
    # }
    {
        "name": "string_slice_2",
        "sat": test_string_slice_2,
        "args": inspect.signature(test_string_slice_2).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "index", "slice", "string"]
    },
    {
        "name": "string_slice_3",
        "sat": test_string_slice_3,
        "args": inspect.signature(test_string_slice_3).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "index", "slice", "string"]
    },
    {
        "name": "string_slice_4",
        "sat": test_string_slice_4,
        "args": inspect.signature(test_string_slice_4).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "index", "slice", "string"]
    },
    {
        "name": "string_slice_5",
        "sat": test_string_slice_5,
        "args": inspect.signature(test_string_slice_5).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "index", "slice", "string"]
    },
    {
        "name": "string_slice_6",
        "sat": test_string_slice_6,
        "args": inspect.signature(test_string_slice_6).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "index", "slice", "string"]
    },
    {
        "name": "string_slice_7",
        "sat": test_string_slice_7,
        "args": inspect.signature(test_string_slice_7).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "index", "slice", "string"]
    },
    {
        "name": "string_slice_8",
        "sat": test_string_slice_8,
        "args": inspect.signature(test_string_slice_8).parameters,
        "notes": "Tests whether we can slice a string",
        "tags": ["basic", "index", "slice", "string"]
    },
    {
        "name": "list_type",
        "sat": test_list_type,
        "args": inspect.signature(test_list_type).parameters,
        "notes": "Tests list type",
        "tags": ["basic", "list"]
    },
]

