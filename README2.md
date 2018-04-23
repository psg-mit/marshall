Compiling
=========
```
aclocal && autoconf && automake && ./configure
make
```
That first line should be run whenever `Makefile.am` is edited.

Using MPFR
==========

First, install MPFR:
`brew install mpfr`

Then, install the Ocaml bindings to it:
`opam install mlgmpidl`

In `src/marshall.ml`, change the code to
```
module Marshall_bignum = Main.Make(Dyadic_mpfr)
```

In `Makefile.am`, add `-pkgs gmp` to `MARSHALLOCAMLBUILD`.
Whenever you edit `Makefile.am`, the next step is then to run
```
aclocal && autoconf && automake && ./configure
```
before running `make`.
