# Getting Started
## Requirements
* Python 3.7 (I'm using the new dataclasses extensively)
* `pip`

## Running Testbuilder
1. Clone the repo locally
2. Run `./install`. This will install `pipenv` with `pip`, then install
l the required dependencies using `pipenv`. It will also clone and
build Z3 at the currently-supported version.
3. Run `./run.py`, passing it a Python file to generate test cases
   for. Some example files which should be fully supported are in the
   root directory (`clements_example.py`, `complex.py`, `junky.py`,
   `pair.py`, and `simple.py`).

# Notes
I try to keep `master` pretty stable, although it may break from time
to time. The majority of development happens in feature
branches. Typically there is only one branch active at a time, and all
changes go into it.
