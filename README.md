# python-z3-interpreter

Translates PythonProgramming puzzles to z3 to solve them.


### How to use

##### Set up
- Install pyhton

- Create your virtual environment

```python3 -m venv myenv```

- Activate it

```source myenv/bin/activate```

- Install z3-solver using pip

```pip install z3-solver```

##### Usage

- Add new tests in tests.py following the same structure (defining the fucntion and updating the dictionary list)
- To run all tests:

```python run_tests.py```

- To run specific test:

```python run_tests.py TEST_NAME```

- To run tests with specific tag:

```python run_tests.py TAG```






