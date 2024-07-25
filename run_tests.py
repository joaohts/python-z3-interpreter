import my_interpreter
from tests import info_list
from typing import List
import ast
import inspect
from z3 import *

from my_interpreter import z3_expr

import sys

class SatTest:
    def __init__(self, info):
        self.name = info["name"]
        self._sat = info["sat"]
        self._args = info["args"]
        self._notes = info["notes"]
        self.tags = info["tags"]

    # Use interpreter to convert from python puzzle to z3 formula
    def __z3_conversion(self, debug=False):
        # Convert to source code and parse using python ast
        function_source = inspect.getsource(self._sat)
        function_ast = ast.parse(function_source)

        # Extract return statement
        return_statement = function_ast.body[0].body[0].value

        # Extract arguments
        vars = {}
        for arg in function_ast.body[0].args.args:
            if arg.annotation.id == "str":
                v = z3.String(arg.arg)
            else:
                v = z3.BitVec(arg.arg, 64)
            vars[arg.arg] = v
        # Generta z3 expression
        if debug:
            for var in vars.keys():
                print(f"{var} - {type(vars[var])}")
        exp, vars = z3_expr(return_statement, vars, debug)
        return exp

    # Try to solve formula and check result
    def run(self, debug=False):
        s = z3.Solver()
        try:
            phi = self.__z3_conversion(debug)
        except Exception as e:
            msg = str(e)[:80]+ "..." if len(str(e)) > 80 else str(e)
            print(f"\033[31mfail :(     - {self.name} -  error interpreting python to z3: '{msg}'\033[0m")
        else:
            s.add(phi)
            try:
                s.check()
                m = s.model()
                args = {}
            except Exception as e:
                msg = str(e)[:80]+ "..." if len(str(e)) > 80 else str(e)
                print(f"\033[31mfail :(     - {self.name} -  error finding solution: '{msg}'\033[0m")
            else:
                for var in m.decls():
                    if str(var) in self._args:
                        
                        if (isinstance(m[var], z3.SeqRef)):
                            args[str(var)] = m[var].as_string()
                        else:
                            args[str(var)] = m[var].as_long()
                        if debug:
                            print("Problem:")
                            print(inspect.getsource(self._sat))
                            print("Solution:")
                            print(f"{str(var)} = {args[str(var)]}")
                
                if self._sat(**args):
                    print(f"\033[32msucess :)   - {self.name} \033[0m")

                else:
                    print(f"\033[33mfail :/     - {self.name} - sat() check failed\033[0m")

def main():
    test_batch = [SatTest(info) for info in info_list]
    if (len(sys.argv) == 1):
        for test in test_batch:
            test.run()

    elif (len(sys.argv) == 2):
        name = sys.argv[1]
        tag_found = False
        for test in test_batch:
            if test.name == name:
                test.run(debug=True)
                return 0

            if name in test.tags:
                test.run()
                tag_found = True

        if tag_found:
            return 0
        else:
            print("\033[33mProblem or tag not found :/\033[0m")
        return 1
    else:
        print("\033[33mInvalid usage :/\033[0m")
        return 1

main()

