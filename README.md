# Compiler-for-scheme
a working compiler for a sub language of scheme.
There are 4 main modules:
1. Reader - Transforms a string into an S-expression list
2. Tag Parser - Transforms the sexpr list into an exspression list - a list of meaningful expressions in the scheme language
3. Semantic analyzer - Adds more details for each expression if necessary(for optimizations in the code generator)
4. Code Generator - transforms the expressions into assembly language
code-gen.ml is the main program.
prims.ml and pc.ml are helper modules written by the "Compiler Principles" course staff in Ben Gurion University
stlib.scm is a version of the standard scheme library functions
