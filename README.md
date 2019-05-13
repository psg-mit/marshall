Dependencies
============

Binary dependencies: rlwrap, mpfr
```
brew install mpfr rlwrap
```

Installing
==========

## With Opam

```
opam install .
```

## Manually

Opam dependencies: camlidl, menhir, num, mlgmpidl (depends on MPFR)
```
opam install camlidl menhir num mlgmpidl
```

To install Marshall type

    ./configure
    make install

This will install the Marshall exectuable in `/usr/local/bin` unless you specified
a different location with `configure`. You do not actually have to install Marshall
to run it.
The `configure` command accepts standard autoconf options, see `configure --help`.


Notes on compilation/installation
=========
Whenever `Makefile.am` is edited, run
```
aclocal && autoconf && automake && ./configure
```
