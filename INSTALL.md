Prerequisites
-------------

You will need the Coq proof assistant (>= 8.8) with a Reals theory compiled
in. You will also need the Flocq library (>= 3.0, http://flocq.gforge.inria.fr/)
to be installed. In order to use the `gappa` tactic, Gappa needs to be installed.

The `.tar.gz` file is distributed with a working set of configure files. They
are not in the git repository though. Consequently, if you are building from
git, you will need autoconf (>= 2.59).


Configuring, compiling, and installing
--------------------------------------

Ideally, you should just have to type:

    ./configure && ./remake -j2 && ./remake install

The `COQC` environment variable can be passed to the configure script in order
to set the Coq compiler command. The configure script defaults to `coqc`.
Similarly, `COQDEP` can be used to specify the location of `coqdep`. The
`COQBIN` environment variable can be used to set both variables at once.

The same OCaml environment used for compiling Coq should be used for
compiling the tactic. It is found by calling `$COQC -config`. The `OCAMLFIND`
environment variable can be used to override this choice.

The library files are compiled at the logical location `Gappa`. The
`COQUSERCONTRIB` environment variable can be used to override the
physical location where the `Gappa` directory containing these files will
be installed by `./remake install`. By default, the target directory is
`` `$COQC -where`/user-contrib ``.
