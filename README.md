# CRD -- Cohomology of Root Data

## Summary
These files provide an implementation of the DeConcini-Salvetti resolution in
Sage, which in theory allow the computation of the cohomology of any finitely
generated (possibly infinite) Coxeter group. Moreover, some methods are
provided for computing the cohomology of the coroot lattices of root data.

## Usage
The DeConcini-Salvetti resolution as such is implemented in
`DeConciniSalvetti.py`. To use it, make it available in Sage by running

    load("DeConciniSalvetti.py")

from within the Sage REPL. The you can e.g. run

    W = CoxeterGroup(["E",8])
    CS = DeConciniSalvettiResolution(W)
    d2 = CS.d(2)
    d2.kernel()

If you are specifically interested in computing the cohomology of all
almost-simple semisimple root data up to rank eight, simply run

    make

If you are interested in the cohomology of a specific root datum, e.g. do

    sage main.py D 4
    sage main.py A 2 3

etc.

## Limitations

At the moment, only finite Coxeter groups are supported, even though in
principle all finitely generated Coxeter groups should be supported. 
