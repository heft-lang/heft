# Heft

Heft is a programming language for programming with Higher order EFfecTs.

Currently, we have implemented a parser and an interpreter for the basic languge.
We plan on extending it with a pretty-printer and type checker, and we plan to add more features to the language.

## Build Instructions 

To load Heft's interactive environment, run: 

```
$ cabal run heft -- repl 
```
After which you can type `:<TAB>` to view the available commands. 

Alternatively you can run the interpreter on a chosen file:  

```
$ cabal run heft -- <filepath> 
```
