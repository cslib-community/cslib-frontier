# Finite-field list-volume theorem

This directory contains the Lean proof used by the element-distinctness circuit lower bound.
The source is OpenAI's *The Matrix Multiplication Exponent is Nine Fourths*, released on
24 November 2026 at revision `3344da59991ed94f9ba711217b29c1d760badfa6`.
[Theorem 2.2](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/obstruction.tex#L40-L55)
and its [Lean proof](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/MatrixExponent/BatchDescent/Hard.lean)
give the lower bound over every finite field.

The included modules are the transitive imports of `BatchDescent.Hard`, `Install.Weight`
and `Transcript.Route.Restore` under `OAI.LinearAlgebra.MatrixExponent`. Together they
provide the volume theorem, the bounded-dependency network construction and the ordering
of bit positions. The port adds Lean 4 module headers and adapts proofs and imports from
the release's Lean 4.34.1 to the toolchain pinned by cslib-frontier. Lake builds these
sources with the same Mathlib as the circuit theorem.

The source is distributed under the [Apache License 2.0](LICENSE).
