# Experimental Coq proofs

Theorems about programs, written using the [Coq proof assistant][coq].  The
file `SfLib.v` is an open-source helper library from the book
[Software Foundations][sf].

Like nearly all Coq code, this code is meant to be read interactively using
a tool like [Proof General][] or [CoqIDE][], which can show you the current
hypotheses and proof goal at any point in the code.  It was tested with Coq
8.4pl3, available on Ubuntu 14.04.  As usual, later versions may
occasionally break the more complicated proofs, as various theorems and
solvers in the standard library are improved.

## Installation and getting started

Run the following commands to install a compiler and 

```sh
sudo apt-get install coq
coqc SfLib.v
```

[coq]: https://coq.inria.fr/
[sf]: http://www.cis.upenn.edu/~bcpierce/sf/current/toc.html
[CoqIDE]: https://coq.inria.fr/V8.1/refman/Reference-Manual016.html
[Proof General]: http://proofgeneral.inf.ed.ac.uk/
