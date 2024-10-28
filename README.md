# Subterm Data

This is a very simple Lean4 executable which does the following:

- It loops through all constants present in the environment when `Mathlib` is imported (ignoring blacklisted ones).
- For each constant, it considers its type as an expression, looks at all of its subexpressions, calculates the constants used by each such subexpression, and stores that data to a file.
- If the constant has a value, it does the analogous process with the expression associated with the value.

Usage:
```
lake exe subterm_data 8 datafile
```
where `8` is the number of threads to use and `datafile` is the file to write the data to.
Data is stored as JSON lines with the following fields:

- `"val" : Bool`, indicating whether or not the expression is the value of the constant.
- `"nm" : String`, the name of the constant under consideration.
- `"mod" : String`, the module in which the constant is defined.
- `"cs" : Array String`, the list of constants used by the subexpression.
