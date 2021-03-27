
NanoHaskell: a self-hosting lambda calculus compiler
====================================================

The goal of this experiment is to create a self-hosting lambda calculus
compiler (and interpreter) in a minimal amount of Haskell-style code.

The language is (strict) lambda calculus + data constructors + simple
pattern matching + recursive lets + IO effects. The syntax is chosen so that 
a program can be also a valid Haskell program at the same time (this makes 
development much easier).

Haskell features like type signatures, data type declarations and imports
are parsed (well, recognized...), but then ignored.


Current status
--------------

* it compiles via GHC, both with and without optimizations
* it self-hosts, both with and without optimizations
* it needs a large C stack (32+ Mb) + GCC optims (because of the lack of tail call elimination)
* source code: about 2000 "essential" lines + 560 lines of type annotations; the C runtime is \~650 lines
  (including some debugging features)
* the interpreter is not working 100% correctly at the moment


Usage
-----

    $ nanohs -c input.hs output.c            # compile with optimizations disabled
    $ nanhos -o input.hs output.c            # compile with optimizations enabled
    $ nanhos -i input.hs [arg1 [arg2 ...]]   # interpret

Or you can just use `runghc`:

    $ runghc Nano.hs -c examples/church.nano tmp.c ; gcc tmp.c ; ./a.out


### Imports

Haskell imports are ignored, but you can use C-style includes with the pragma:

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
11. final code generation (TODO: different backends)


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

* normal heap pointer (closure or data constructor)
* 61 bit literals (int / char)
* nullary constructors
* static function pointers
* foreign pointers (used for file handles in the C runtime)

There are no thunks on the heap because we are strict.

The garbage collector is a very simple copying (compacting) GC.


Implementation details
----------------------

There are some minor tricks you should be aware if you try to read the code.

### Argument order

The order of function arguments on the stack, the captured variables in closures 
and also the order of constructor arguments on heap are all reversed compared to 
the "logical" (source code) order. This makes the implementation of application
much simpler.

    [ Cons_tag    argN ... arg2 arg1 ]                   # data constructor heap object
    [ Closure_tag envK ... env2 env1 ]                   # closure heap object 
    [ ... | argN ... arg1 envK ... env1 | undefined ]    # stack when calling a static function
          ^ BP                          ^ SP

Note: our stack grows "upwards" (unlike the CPU stack which grows "downwards").

### IO monad

There is an IO monad, which in the GHC runtime and the interpreted runtime is
the host's IO monad, while in the compiled code it is encoded with functions
having side effects:

    type IO a = ActionToken -> a

You need to begin your `main` function with an explicit `runIO` call (this is
useful while debugging, as main can be just a simple expression instead).


Organization of source code
---------------------------

    Base.hs          - base library / prelude
    Closure.hs       - closure conversion
    CodeGen.hs       - code generation
    Containers.hs    - container data structures 
    Core.hs          - core language
    DataCon.hs       - data constructors
    Dependency.hs    - reordering lets using the dependency graph
    Eval.hs          - interpreter
    Inliner.hs       - inliner + basic optimizations
    Nano.hs          - main executable
    Parser.hs        - parser
    PrimGHC.hs       - the primops implemented in Haskell (so that GHC can host it) 
    PrimOps.hs       - primops
    ScopeCheck.hs    - scope checking + conversion to core
    Syntax.hs        - surface syntax
    Types.hs         - common types
    rts.c            - the runtime system implemented in C
    bootstrap.sh     - shell script to bootstrap the compiler
    sloc_count.sh    - shell script to measure source code size
 
