# ky

To use Z3 (disabled at the moment), build and install this version of
Z3: https://github.com/Z3Prover/z3/tree/z3-4.8.1

##### stack build && stack exec ky-exe programs/test1.ky

#### app/

* Main.hs - The main entry point. Contains some code for generating
  random trees as well as reading in and parsing programs.

#### src/

* Datatypes.hs - Generic setup for open recursion style data types.

* Tree.hs - The tree functor, the type of well-founded trees and
  operations on them.

* ListTree.hs - List representation of trees and operations on them,
  e.g., converting to and from the standard representation.

* Nat.hs - Open recursion natural numbers.

* Cotree.hs - The type of potentially infinite trees as the greatest
  fixed point of the tree functor, and some operations on them.

* Sample.hs - State monad sampling of Cotrees.

* Inference.hs - generate histograms and pmfs from samples.

* Sexp.hs - Typeclass for serializing stuff to s-expression format
  (e.g., to visualize trees at
  https://bagnalla.github.io/sexp-trees/).

* Symtab.hs - Contains a type for string-based identifiers (Id) and an
  interface for maps from Id to any value type.

* Util.hs - Miscellaneous utility functions including a debug print
  function.

* Lang.hs - Abstract syntax for the PPL (using GADTs and existential
  packages in the state) and interpretation of commands as tree
  transformers.

* Distributions.hs - Primitive distribution constructions. Uniform,
  Bernoulli, etc.

* Untyped.hs - Untyped abstract syntax to be typechecked and
  elaborated to the GADT representation after parsing from a file.

* Token.hs - Some things used by the parser.

* Parser.hs - Megaparsec parser.

* Tycheck.hs - Typechecking / elaboration from untyped to GADT.

#### programs/

* test.ky - Example test program.

* bernoulli.ky - For testing the built-in Bernoulli distribution.

* fair_coin.ky - Simulating a fair coin using an unfair one.

* flips.ky - Stochastic domination example from Hsu's thesis.

* tricky_coin.ky - Tricky coin inference example.