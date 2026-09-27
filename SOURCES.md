# Sources and external dependencies

## Target paper

Peter W. O’Hearn and Jon G. Riecke. **Kripke Logical Relations and PCF.**
*Information and Computation* 120(1), 107–116, 1995.
DOI: https://doi.org/10.1006/inco.1995.1103

The mathematical proof specification supplied earlier in this conversation was
used as the immediate plan. `PROOF_MAP.md` records the places where this source
uses an equivalent representation or a different proof decomposition.

## Lean and Mathlib

The only external Lean library import is Mathlib; everything else is a local
`OR` module. The project fixes Mathlib's tag and its matching Lean toolchain:

- https://github.com/leanprover-community/mathlib4/tree/v4.19.0
- https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.19.0/lean-toolchain
- https://github.com/leanprover/lean4/releases/tag/v4.19.0

Pinned source files consulted for the basic interfaces include:

- https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.19.0/Mathlib/Order/CompletePartialOrder.lean
- https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.19.0/Mathlib/Order/Bounds/Basic.lean
- https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.19.0/Mathlib/Data/Finset/Card.lean
- https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.19.0/Mathlib/Data/Set/Finite/Basic.lean

Mathlib documentation was also consulted for finite sets, directed completeness,
and continuous-map interfaces. Documentation may track a newer version than the
pinned dependency, which is one reason actual compilation is still necessary.

## What is not an imported theorem

No external development of O’Hearn–Riecke full abstraction was imported.
The local domain-theory interface, its concrete instances, the sequentiality
characterization, relational exponentials, finite projections, finite
definability, separation, and adequacy all have local proof bodies. Their
correctness remains subject to successful Lean checking.
