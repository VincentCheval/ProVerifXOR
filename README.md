# XOR Extension of ProVerif: ProVerif with Exclusive OR 

ProVerif:
Protocol verifier, copyright INRIA-CNRS, by Bruno Blanchet,
Vincent Cheval, and Marc Sylvestre 2000-2026.

XOR Extension:
Vincent Cheval and Stéphanie Delaune
Copyright (C) INRIA, CNRS 2000-2026
Copytight (C) University of Oxford, 2026

This software can be used to prove secrecy and authenticity properties
of cryptographic protocols.

## INSTALL (under Unix / Mac)

To run this software, you need Objective Caml version 5.2 or
higher. Objective Caml can be downloaded from
	https://ocaml.org

The installation of OCaml is done through Opam. If you have already an older version of Ocaml, you can run the following to update it

	opam update
	opam switch create 5.2.0

 ProVerif requires the dune package which should normally be installed with your opam installation. If it's not the case:

	opam install dune

Download the repository (or clone it) of ProVerif. This will create a directory named proverifXOR. Go into this directory, and build the program:

	cd proverifXOR
	./build

This will create the executable proverif. It is possible that right after downloading the folder, executing `./build` yields a `permission denied: ./build`. In such a case run:

	chmod +x build
	./build

To remove the installed files:

	./build clean

## USAGE

The program proverif takes as input a description of a cryptographic
protocol, and checks whether it satisfies secrecy, authenticity, or
equivalence properties. 

The program uses the same command as Vanilla ProVerif. To run a ProVerif file ending
in .pv, use
	
	./proverif <filename>.pv

The folder examples_distribution contains the files that came from the official distribution
of ProVerif.

The folder examples_XOR contains the examples used to evaluate the extension XOR.

## IMPORTANT NOTE FOR XOR EXTENSION

Contrary to standard input file of ProVerif, the functions used with exclusive OR are
natively encoded in ProVerif and should not be declared. 
The function "xor" can directly be used without being declared. Similarly, the constant "zero"
can be directly used without being declared.

For example, file
	examples_XOR/Ex-false/toy-false1.pv
contains the following code:

```
	free c: channel.

	free s:bitstring [private].
	free n1:bitstring [private].
	free n2:bitstring [private].

	query attacker(s).

	process
		out(c,n1); out(c,xor(n2,n1)); in(c, =n2); out(c,s)
```

## Reproducibility of the results described in the paper:

The models corresponding to the Figures 4 and 5 of the paper are all included in the folder 
`examples_XOR/Ex-protocol`. Specifically the following model:

In Figure 4:
- <b>NSL-xor</b>: nslxor-notag.pv
- <b>NSL-xor fix</b>: nslxor-fix-notag.pv
- <b>RA</b>: ra.pv
- <b>RA fix</b>: ra-fix.pv
- <b>IBM-CCA-0</b>: IBM-CCA_0.pv

In Figure 5:
- <b>CR-xor</b>: CR-xor-dis.pv 
- <b>CH07</b>: CH07-dis.pv
- <b>KCL07</b>: KCL07-dis.pv
- <b>LAK06</b>: LAK06-dis.pv
- <b>MW</b>: MW-dis.pv

All the results in Figure 4 and 5 have been obtained on the most general models. All other models
included in the folder Ex-protocol are more restrictive models.

