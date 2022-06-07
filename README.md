# Senior Project: Solver-Aided Program Verification of C0 with Rosette

## Installing Rosette
To install Rosette, use:
`$ raco pkg install rosette`

## Running Examples
There are a few verification examples which can be run. They can be found in `verify_demo.rkt`.
Running `verify_demo.rkt` will print some output about the success/failure of verifying the examples.
If verification succeeds, `'()` (no counterexamples) should be printed. If it fails, then a counterexample in
the form of a Rosette model will be printed. 

