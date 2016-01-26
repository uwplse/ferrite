# Crash-Consistency Verification and Synthesis

This directory contains proof-of-concept verification and synthesis tools built using the Ferrite framework, as described in section 6 of [our ASPLOS'16 paper][ferrite].

## Getting Started

These tools are implemented in [Rosette][]. Install the following prerequisites:

* Racket v6.2.1 ([download](http://download.racket-lang.org/racket-v6.2.1.html); v6.3 is not yet supported)
* Java v1.7 or above ([download](http://www.oracle.com/technetwork/java/javase/downloads/index.html))
* Rosette ([instructions on GitHub](https://github.com/emina/rosette))

## Running the tests

The `litmus` directory contains examples of litmus tests from the ASPLOS paper. Run a test using the following command:

	$ raco test litmus/create-rename.rkt

The tests compare their results against those shown in the paper, and will report a test failure if they differ.

Synthesis tests also output the original and synthesized code.


[ferrite]: https://sandcat.cs.washington.edu/ferrite/ferrite-asplos16.pdf
[rosette]: http://github.com/emina/rosette
