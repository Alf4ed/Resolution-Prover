# Resolution Proof System in Prolog

This project is a resolution theorem prover implemented in Prolog.

## Overview
The program processes propositional logic formulas and determines whether they can be proven as theorems using the resolution proof system. It supports negation and various primary and secondary logical connectives.

## How It Works
1. Converts propositional formulas into conjunctive normal form (CNF).
2. Applies resolution rules to test if the formula can be proven true.
3. Outputs 'YES' or 'NO' based on whether the formula has a resolution proof.

## How to Run
1. Clone the repository and navigate to the project directory.
2. Run the Prolog program using a Prolog interpreter (e.g., SWI-Prolog):

```bash
swipl -s resolution.pl
```
To test the program, input propositional formulas by calling the `test` function:

```prolog
?- test('your_formula_here').
```
