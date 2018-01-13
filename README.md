# The Evolution of a Typechecker


This repository is inspired by [The Evolution of a Haskell
Programmer](https://www.willamette.edu/~fruehr/haskell/evolution.html),
which was itself inspired by the folklore joke [The Evolution of a
Programmer](http://www-cs-students.stanford.edu/~dchou/humor/evolution.html).

Our patient zero is a Haskell98-compliant implementation of a
typechecker for the simply-typed λ-calculus. We then improve (and
branch upon) variants of this base program.

**Caution:** bugs have voluntarily been inserted in the various
implementations, unless typing prevents it. In principle, only the
HEAD of `master` is bug-free, because the type system leaves us no
choice.

## Editing

This repository has been tested with Agda 2.5.2 and the Agda standard
library 0.13.


## Contributing

Contributions are more than welcome. In particular, we welcome
exploratory branches (even if unfruitful) and further bike-shedding of
existing branches.

Since the value of this repository lies more in its genotype than the
final product, we are keen on keeping a clean history, even if it
means rewriting history and push-forcing changes to this repository.


## Author

This project has been initiated by [Pierre-Évariste
Dagand](https://pages.lip6.fr/Pierre-Evariste.Dagand/) as part of
[MPRI-2.4](https://gitlab.inria.fr/fpottier/mpri-2.4-public) course
material. It contains a significant amount of
[McBride](http://strictlypositive.org/)-ism (namely: the mantras of
bidirectional typing, canonical & elimination forms, strongly typed
term representation, dissection, etc.) and a pinch of the [Agda
prelude](https://github.com/UlfNorell/agda-prelude) (the do-notation,
taken from Ulf Norell, to wait until the next version of Agda).


[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)