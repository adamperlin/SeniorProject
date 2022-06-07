# Senior Project: Solver-Aided Program Verification of C0 with Rosette

## Installing Rosette
To install Rosette, use:

`$ raco pkg install rosette`

## Running Examples
There are a few verification examples which can be run. They can be found in `verify_demo.rkt`, which can be run with

`$ racket verify_demo.rkt`

This will print some output about the success/failure of verifying a handful of simple examples. 
If procedure verification succeeds, `'()` (no counterexamples) should be printed. If it fails, then a counterexample in
the form of a Rosette model will be printed. 