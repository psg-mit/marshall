Dependencies
============

Binary dependencies: rlwrap, mpfr
```
brew install mpfr rlwrap
```

Opam dependencies: menhir, num, mlgmpidl (depends on MPFR)
```
opam install menhir num mlgmpidl
```

Compiling
=========
```
aclocal && autoconf && automake && ./configure
make
```
That first line should be run whenever `Makefile.am` is edited.

The `configure` command accepts standard autoconf options, see `configure --help`.
The compiled executable is called `marshall` and you can run it in place.

## Installation

To install Marshall type

    make install

This will install the Marshall exectuable in `/usr/local/bin` unless you specified
a different location with `configure`. You do not actually have to install Marshall
to run it.

# Old

3. You need [camlidl](http://caml.inria.fr/camlidl/), which is available in GODI
as well.