
NanoHaskell: a self-hosting lambda calculus compiler
====================================================

The goal of this experiment is to create a self-hosting lambda calculus
compiler (and interpreter).

The language is (strict) lambda calculus + data constructors + simple
pattern matching. The syntax is chosen so that a program can be also a 
valid Haskell program at the same time (this makes development much easier).

Haskell features like type signatures, data type declarations and imports
are parsed, but ignored.

The language
------------

The idea is to write a self-hosting compiler (and interpreter) in
a very small subset of Haskell (basically untyped lambda calculus +
constructors); but with Haskell-compatible syntax, so that the same
program can be also executed by GHC:

* no static type system (untyped lambda calculus)
* na data type declarations (constructors are arbitrary capitalized names)
* no module system - instead, C-style includes
* strict language (if-then-else must be lazy though; "and" + "or" shortcuts too)
* ML-style side effects (but only used for IO, which is then wrapped into a monad)
* only simple pattern matching + default branch (TODO: nested patterns)
* no infix operators
* list construction syntax @[a,b,c]@ is supported
* no indentation syntax (only curly braces), except for top-level blocks
* only line comments, starting at the beginning of the line
* built-in data types: Int, Char, Bool, List, Maybe, etc, those required by the primops
* universal polymorphic equality comparison primop (?)
* no escaping in character \/ string constants (TODO: maybe it's worth to do escaping?)
* basic IO: standard input \/ output, basic file handling, early exit, command line arguments 

We can make the same source file to be accepted by both GHC and
itself by recognizing and ignoring GHC-specific lines (pragmas, imports,
type signatures, datatype declarations, type synonyms). We just put
primops implementations into a PrimGHC module (as imports are ignored).

We can have several backends:

* C99 on 64 bit architectures
* TODO: x86-64 assembly
* TODO: some simple bytecode virtual machine

For bootstrapping purposes it seems to be useful to have a very simple virtual 
machine, for which an interpreter can be very easily written in C or any other 
language.

