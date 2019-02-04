# Getting Started
## Requirements
* Python 3.7 (I'm using the new dataclasses extensively)
* `pip`

## Running Testbuilder
1. Clone the repo locally
2. Install [`pipenv`](https://pipenv.readthedocs.io/en/latest/)
3. Install dependencies with `pipenv install`
4. Run `./run.py`, passing it a Python file to generate test cases
   for. Some example files which should be fully supported are in the
   root directory (`clements_example.py`, `complex.py`, `junky.py`,
   `pair.py`, and `simple.py`).

# Notes
I try to keep `master` pretty stable, although it may break from time
to time. The majority of development happens in feature
branches. Typically there is only one branch active at a time, and all
changes go into it.
