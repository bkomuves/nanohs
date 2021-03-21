
NanoHaskell: a self-hosting lambda calculus compiler
====================================================

The goal of this experiment is to create a self-hosting lambda calculus
compiler (and interpreter) in a minimal amount of Haskell-style code.

The language is (strict) lambda calculus + data constructors + simple
pattern matching + recursive lets. The syntax is chosen so that a program can 
be also a valid Haskell program at the same time (this makes development much 
easier).

Haskell features like type signatures, data type declarations and imports
are parsed, but then ignored.


Current status
--------------

* it compiles via GHC, both with and without optimizations
* it self-hosts, both with and without optimizations
* it needs a large C stack (16-32 Mb) + GCC optims (because of the lack of tail call elimination)
* source code: about 1900 "essential" lines + 520 lines of type annotations; C runtime: \~650 lines
  (including some debugging features)
* the interpreter does not work at the moments


Usage
-----

    $ nanohs -c input.hs output.c            # compile with optimizations disabled
    $ nanhos -o input.hs output.c            # compile with optimizations enabled
    $ nanhos -i input.hs [arg1 [arg2 ...]]   # interpret (does not work at the moment)


Haskell imports are ignored, but you can use C-style includes with the pragma

    {-% include "othermodule.hs" %-}


The surface language
--------------------

The idea is to use a subset of Haskell syntax, so that the same program same
program can be also compiled / interpreted by GHC. 

* no static type system (untyped lambda calculus) - but maybe there should be a type checker after all?
* na data type declarations (constructors are arbitrary capitalized names)
* no module system - instead, C-style includes
* strict language (if-then-else must be lazy though; `and` / `or` shortcuts too)
* ML-style side effects (but only used for IO, which is then wrapped into a monad)
* only simple pattern matching + default branch (TODO: nested patterns)
* no infix operators
* list construction syntax `[a,b,c]` is supported
* no indentation syntax (only curly braces), except for top-level blocks
* only line comments, starting at the beginning of the line
* built-in data types: `Int`, `Char`, `Bool`, `List`, `Maybe`, etc - those required by the primops
* universal polymorphic equality comparison primop (?)
* no escaping in character / string constants (TODO: maybe it's worth to do escaping?)
* basic IO: standard input / output, basic file handling, early exit, command line arguments 

We can make the same source files to be accepted by both GHC and
itself by recognizing and ignoring GHC-specific lines (pragmas, imports,
type signatures, datatype declarations, type synonyms). We just put
primops implementations into a PrimGHC module (as imports are ignored).

We could in theory have several backends:

* C99 on 64 bit architectures
* TODO: x86-64 assembly
* TODO: some simple bytecode virtual machine

For bootstrapping philosophy it seems to be useful to have a very simple virtual 
machine, for which an interpreter can be very easily written in C or any other 
language.


Compilation pipeline
--------------------

1. lexer
2. parser
3. partition recursive lets using dependency analysis
4. recognize primops
5. TODO: eliminate pattern matching into simple branching on constructors
6. collect data constructors
7. scope checking & conversion to core language
8. inline small functions + beta reduce + eliminate unused lets
9. closure conversion
10. TODO: compile to some low-level intermediate language
11. final code generation (different backends)


Runtime system
--------------

There is an "enviroment" stack separate from the CPU stack. This makes it
very easy to find GC roots: just walk through the stack. The stack contains
pointers to the heap (with the optimization that small heap objects, fitting
into 61 bits, are not actually allocated).

On the heap there are only two kind of objects, closures and data constructors:
 
* data constructor (needs: tag + arity)
* closure / partial application (needs: static function pointer / index, 
  number of applied arguments, number of remaining arguments)

Heap pointers are also tagged:

* normal heap pointer
* 61 bit literals (int / char)
* nullary constructors
* static function pointers
* foreign pointers (used for file handles in the C runtime)

There are no thunks because we are strict (well currently there are, but that's
temporary).

The garbage collector is a very simple copying (compacting) GC.

