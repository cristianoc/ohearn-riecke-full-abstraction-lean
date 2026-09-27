# O’Hearn–Riecke full abstraction for PCF in Lean 4

A complete, kernel-checked Lean 4 formalisation of Peter W. O’Hearn and Jon G. Riecke, [*Kripke Logical Relations and PCF*](paper/OHearn-Riecke-Kripke-Logical-Relations-and-PCF.pdf), Information and Computation 120(1):107–116, 1995 ([doi:10.1006/inco.1995.1103](https://doi.org/10.1006/inco.1995.1103)). The paper builds a model of PCF from Kripke logical relations and proves it inequationally fully abstract; this repository formalises the model, finite definability, full abstraction, and the operational adequacy the paper leaves as a remark.

## Main theorem

```lean
theorem full_abstraction_op {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualOpLE M N ↔ denote M ≤ denote N
```

`ContextualOpLE M N` holds when every closing context of ground type that makes `M` evaluate to a numeral makes `N` evaluate to the same numeral. `denote M ≤ denote N` is the pointwise order in the relational model. Variants: `full_abstraction_den` (the paper's Theorem 14, with observation defined denotationally), `full_abstraction_op_eq` (equality), and `full_abstraction_termination` (observing termination only).

## Status

- `lake build` succeeds with Lean and Mathlib `v4.19.0`; CI rebuilds on every push.
- No `sorry`, `admit`, custom axioms, `unsafe` or `native_decide` (checked by `scripts/static_audit.py`).
- The main theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (checked by `OR/AxiomAudit.lean`).

The formalisation was drafted without a local Lean installation, compiled for the first time in CI and repaired there, then aligned definition by definition with the paper once the PDF was obtained.

## Paper ↔ Lean

Page numbers are the paper's printed pages (PDF page = printed page + 1, because of the repository cover page).

| Paper | p. | Lean |
|---|---|---|
| Definition 1, Proposition 2 (sequentiality relations) | 4 | `Elementary`, `finite_interpolation`, `sequential_iff_primitive_closed` |
| Definition 3 (Kripke relations) | 6 | `KRel` |
| Definitions 4–5, Proposition 6 | 7 | `Test` |
| The category `SR` | 8 | `Obj`, `Uniform`, `Hom`, `Obj.arr` |
| Lemma 7 | 9 | `uniformSupClosed`, the fields of `Obj.arr` |
| Lemma 8 | 9–10 | `Hom.expMap`, `Hom.curry`, `Hom.uncurry` |
| Proposition 9, fixed points | 10 | `Hom.pair`, `Hom.eval`, `le_iff_global`, `Hom.fixMap` |
| PCF and its interpretation | 10–11 | `Ty`, `Tm`, `denote` |
| Lemma 10 (Milner) | 11 | `projection`, `projection_approximates`, `projection_idem` |
| `C_n`, `R_n`, Lemma 11 | 12 | `finiteTest`, `Extension`, `Def` |
| Lemma 12 and the claim in its proof | 12–13 | `finite_definability`, `strong_finite_definability` |
| Definition 13 | 14 | `ContextualDenLE` |
| Theorem 14 | 14 | `full_abstraction_den` |
| Adequacy (a remark in the paper) | 14 | `adequacy`, `full_abstraction_op` |

## Differences from the paper

The construction and the proofs are the paper's; in particular Lemma 12 is proved, as in the paper, through the stronger claim about arbitrary finite worlds that its proof states. The remaining differences are of representation or generality:

- **Worlds.** Tests range over any small concrete category of finite types, not only subcategories of `Finset`. Every such category is a subcategory of `Finset` after relabelling its elements, so `SR` is unchanged; the relabelling argument itself is not formalised.
- **Universes.** `Test : Type 1` while carriers stay in `Type 0`, so hom-sets remain small enough for the next arrow type, without a resizing axiom.
- **`C_n` and `R_n`.** Worlds are typed contexts, elements are finite-level environments, and morphisms are exactly the paper's prefix projections. Tuples in `R_n`, and in the Lemma 12 claim, are represented by open terms `Γ ⊢ τ` instead of closed curried terms.
- **Ground projection term.** Written recursively rather than as the paper's nested `ifz (predᵏ x)`; both denote the cut at `n` (`projection_nat`).
- **Contexts.** Single-hole, with a variable renaming at the hole, which de Bruijn syntax needs to say which binders capture the plugged term. This admits a few contexts without a named counterpart, so the direction "contextually below implies denotationally below" is formally weaker than the paper's. The separating contexts the proof builds are ordinary ones, but that stronger form is not stated as a theorem.
- **Added detail.** The paper proves Theorem 14 in one line ("follows from Lemma 10, Lemma 12, and continuity") and adequacy by reference; Lean constructs the separating context, defines the operational semantics and proves adequacy.
- **Not formalised.** The functor laws of Lemma 8(a), the naturality in Lemma 8(b), and the cpo-enrichment in Proposition 9. Nothing downstream uses them.

## Proof outline

**Model** (`Order`, `Flat`, `Sequential`, `Worlds`, `SR`). Ground values form the flat domain $`\mathbb N_\bot`$. A test is a category of finite worlds with, at each world `w`, a relation on tuples `w → ℕ⊥` that is a sequentiality relation: an intersection of Sieber's relations

```math
S^w_{A,B}(g) \iff \bigl(\exists i\in A.\ g(i)=\bot\bigr) \lor \bigl(\forall i,j\in B.\ g(i)=g(j)\bigr).
```

An object of `SR` is a domain with a Kripke relation for every test; morphisms are continuous maps preserving all of them. Exponentials relate `g` at `w` when, for every world morphism `φ : v → w` and every related `h`, the tuple `i ↦ g(φ i)(h i)` is related at `v`. PCF (`Syntax`, `Interpretation`) is interpreted in this cartesian closed category, with `pred 0 = ⊥`.

**Finite projections** (`Projections`). The PCF terms $`P^n_\tau`$ cut every value to level `n`. Their denotations $`\psi^n_\tau`$ are idempotent, increase with `n` to the identity, and have finite images $`D^n_\tau`$.

**Definability** (`FiniteWorlds`, `Definability`). The test `finiteTest n` has contexts as worlds and relates exactly the tuples defined by PCF terms. By induction on types, a finite-level tuple is related iff it is definable (`strong_finite_definability`); at the empty world this gives Lemma 12: every finite-level element is the denotation of a closed term.

**Separation** (`FullAbstraction`). If $`⟦M⟧ \not\sqsubseteq ⟦N⟧`$, the failure occurs at some environment, and already at a finite projection of it; definability closes the hole with terms for that environment. For closed terms, induction on the type repeatedly picks a finite-level argument where the failure persists and applies both sides to a closed term defining it, until ground type, where the two sides differ at a numeral. The result is a context $`C`$ with $`⟦C[M]⟧ = {\uparrow} q \ne ⟦C[N]⟧`$.

**Adequacy** (`Operational`, `Adequacy`). Call-by-name evaluation is defined independently of the model; a logical relation between values and terms, closed under least fixed points, gives $`M \Downarrow n \iff ⟦M⟧ = {\uparrow} n`$ for closed ground terms, which transfers full abstraction to the operational order.

`Examples` checks, among other things, that parallel-or is not in the model (`no_parallel_or`): the uniform arrow carrier excludes it, as the full Scott function space would not.

## Layout

| Files | Contents |
|---|---|
| `OR.lean` | Root module. |
| `OR/Order.lean`, `OR/Flat.lean` | Directed-complete orders, continuous maps, fixed points, flat naturals. |
| `OR/Sequential.lean`, `OR/Worlds.lean` | Sequentiality relations, finite interpolation, tests and Kripke relations. |
| `OR/SR.lean` | The category `SR`. |
| `OR/Syntax.lean`, `OR/Interpretation.lean` | Intrinsically typed PCF and its interpretation. |
| `OR/Projections.lean`, `OR/FiniteWorlds.lean` | Finite projections and the test `finiteTest`. |
| `OR/Definability.lean`, `OR/Compactness.lean` | Finite definability, compact elements. |
| `OR/FullAbstraction.lean` | Contexts, separation, denotational full abstraction. |
| `OR/Operational.lean`, `OR/Adequacy.lean`, `OR/Observations.lean` | Operational semantics, adequacy, operational full abstraction. |
| `OR/Examples.lean`, `OR/AxiomAudit.lean` | Regression examples; axiom audit. |
| `paper/` | The paper (SURFACE copy). |
| `scripts/` | `check.sh` and the two audit scripts. |

## Build

```sh
bash scripts/check.sh
```

This runs the source audit, fetches the Mathlib cache, builds, and runs the axiom audit, exactly as CI does. On macOS 26 the compiled Mathlib cache tool fails to start; the script falls back to running it through the Lean interpreter.
