# imphoare

A simple Hoare Logic proof checker library for an Imp-like toy language.
It uses [Z3](https://github.com/Z3Prover/z3) under the hood for attempting to 
prove some things, so you'll need to install that separately.

## Limitations

- The underlying format for proofs is just a list of statements, with
  the actual references to previous statements removed. This means
  at each step we need to search through all our previously proven
  statements, giving an overall run-time of O(n^2). I doubt this
  will prove particularly problematic, since the size of the input proofs
  is likely small.
- The way we handle exponentation in Z3 is to simply define an uninterpreted
  function and then make some assertions which define it for all natural
  exponents. Whilst this is sufficient to prove a statement (since we just
  negate and check for unsatisfiability) it can't disprove a statement
  because it can't infer a model for the exponentiation function
  itself.
- You can't define your own functions to go inside the preconditions
  and postconditions of a hoare triple. There's no technical reason we
  don't allow this, and it'll probably be added in a later version -
  although it will probably suffer from similar issues as exponentation
  with regards to being unable to disprove a statement.
- It's not particularly well tested, and the test suite is a WIP
