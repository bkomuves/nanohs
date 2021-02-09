
NanoHaskell: a self-hosting lambda calculus compiler
====================================================

The goal of this experiment is to create a self-hosting lambda calculus
compiler (and interpreter).

The language is (strict) lambda calculus + data constructors + simple
pattern matching. The syntax is chosen so that a program can be also a 
valid Haskell program at the same time (this makes development much easier).

Haskell features like type signatures, data type declarations and imports
are simply ignored.
