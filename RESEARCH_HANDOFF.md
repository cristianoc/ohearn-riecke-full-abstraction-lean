# Research handoff: explicit ordinary-vs-Kripke counterexample

This file is for the next implementation-capable research agent.  It deliberately contains
details that do not belong in the PR description.  Read `SIEBER.md`,
`gpu/REPORT.md`, and `GPU_SEARCH.md` first.

## 1. Stable results and status

### Lean-checked before this research branch

The parent PR/branch `sieber-not-universal` contains the checked `OR/Sieber/`
development.  In particular its endpoints establish, under explicit external hypotheses:

* `sieber_not_universal`: non-universality of the ordinary Boolean Sieber model, assuming
  `Loader`.
* `natural_sieber_not_inequationally_fully_abstract`: failure of inequational full
  abstraction for the direct ordinary natural Sieber model $`D^N`$, assuming `Loader`,
  `NS.MilnerPlotkin` and `MullerGameTermTheorem`.

The hypotheses, exactly (details in `SIEBER.md` §6 and §4.1):

* `Loader` is non-computability of `ObsEquivCode`, observational equivalence on term codes
  defined through values in the standard set-theoretic model.  That this agrees with
  Loader's operational equivalence (normal form = standard-model value) is argued only in
  the module docstring of `OR/Sieber/Standard.lean`.
* `NS.MilnerPlotkin` is Milner's theorem instantiated at $`D^N`$ alone; its premises
  other than full abstraction are proved and discharged.
* `MullerGameTermTheorem` is Müller's Theorem 4.12 at grade 1 only, transcribed into the
  repository's PCF.  Equivalence there is observed by call-by-name head reduction, while
  Müller uses unrestricted reduction; the agreement is a standardisation argument outside
  Lean.

The O'Hearn--Riecke Kripke development, including `finiteTest`, is also kernel checked.

### Mathematical/source-audited on this branch, not newly Lean-checked

`SIEBER.md` §4.6–4.7 records order-local consequences, with a dependency audit in §4.7.5:

* Lemma 13: assuming Loader's order-3 equation lemma (cited via Ong--Tzevelekos), the
  Boolean model $`D^B`$ has a non-definable element at some type of order at most 3.
* Theorem C, part 1: assuming in addition Müller's Game Term Theorem and an order-local
  reading of Stoughton's compact-definability proof (Streicher, Lemma 13.2; the order
  bookkeeping is a reading of the proof, not a cited theorem), equational full abstraction
  of $`D^N`$ fails at some type of order at most 4.
* Lower bounds, conditional: Sieber's 1992 results concern invariant elements of the
  standard/continuous hierarchy, which `SIEBER.md` does not identify with $`D^B`$/$`D^N`$
  (§4.1, hypotheses (I) and (I') in §4.7).  Under (I), universality of $`D^B`$ holds
  through order 2, so the first non-universal order is exactly 3 (Theorem U).  Under (I'),
  which also needs O'Hearn--Riecke's "rank three" convention read as order at most 3, the
  first equational failure of $`D^N`$ is exactly order 4 (Theorem C, part 2).  A proof
  that the direct models coincide with Sieber's presentation at those orders, or a direct
  proof of the positive results for $`D^B`$/$`D^N`$, discharges them.
* inequational failure propagates to every higher exact order by a definable retract
  (Lemma 12);
* Loader's guaranteed order-3 obstruction can be localized to an explicit family
  `T_|W0| -> U1 -> U2 -> U3 -> B^(2n+2) -> B` using a fixed three-rule accessibility
  system.

These are mathematical arguments using published Loader/Ong--Tzevelekos,
Sieber/Stoughton/Müller results, under the hypotheses above, plus the checked
infrastructure.  Do not describe these as
Lean theorems unless they are separately formalized.

### Computational discoveries on this branch

The `gpu/` programs are independently checkable experiments, not formal proofs unless a
finite certificate is explicitly verified.

* Apple M2 Max Metal implementation: ~35x over the vectorized single-core CPU reference on
  the arity-3 falsifier; batched structured search ~171 candidates/s.
* `D2 = D_((B->B)->B)` has 355 elements and width 80 (explicit certificate).
* 100k structured candidates: 93,932 survive every arity-3 ordinary test; they collapse to
  13,460 symmetry classes.
* Every one of those 13,460 classes is nevertheless PCF-definable.  6,497/6,775 two-cone
  problems are solved by decision trees over the 11 closed calls; the remaining 278 use one
  round of nested calls.  The exported 4,233 columns and tree certificates are under
  `gpu/data/m4_export/`.
* SAT then constructed genuinely non-definable arity-3-preserving candidates.  A particularly
  small three-cone candidate is ff on `up(129) U up(272) U up(321)` and bottom elsewhere.
  Its non-definability has a small first-call compatibility argument, which relies on the
  standard head-call lemma for normal forms (not yet written out).
* These are NOT Sieber counterexamples: a search over all 17,240 arity-4 intersections
  (1,027 up to coordinate permutation), stopped once witnesses were found, finds ordinary
  relations killing both the three-cone and 20-cone candidates.  The first three-cone killer
  and tuple are documented in `gpu/REPORT.md`.
* Lesson: elementary arity-4 tests are insufficient; intersections are essential.  Finite
  k-way parallel-looking obstructions can survive lower arity and then be caught one arity
  later.

## 2. Current strategic interpretation

Do not resume blind cone/race generation.  The repeated pattern is:

1. simple apparent parallelism is actually definable via nested calls; or
2. a genuinely non-definable finite local obstruction is caught by a higher-arity ordinary
   Sieber relation.

Ordinary relations already have unbounded finite arity.  The remaining ordinary-vs-Kripke
gap is therefore more plausibly about coherence under world extension than about another
fixed finite race.

The research direction was reversed: generate behavior from an explicit Kripke extension
that is absent from the corresponding ordinary lift, then ask for an ordinary-preserving
functional that violates the Kripke relation.

## 3. Important correction about O'Hearn--Riecke finiteTest

Do NOT try to enumerate the checked `finiteTest` by taking small contexts.

In `OR/FiniteWorlds.lean`:

```
finiteTest n:
  World := Ctx
  ground Gamma := Def n Gamma nat
```

and `Def` means definability by an open PCF term over the context.  Thus even though each
finite-level environment set is finite, deciding the selected ground relation at a
higher-order context contains the very definability problem under study.

What can be enumerated soundly are explicit computable Kripke logical relations whose ground
relations are ordinary sequentiality relations.  PCF terms preserve these by the fundamental
lemma, so a violation is a sound non-definability certificate.  Such a family need not be
complete.

## 4. Kripke separator search already performed

See `gpu/kripke_separator.py` (the search), `gpu/search_kripke_two_world.py` (the relation
generator), and `gpu/data/kripke_separator_all.json`, the per-case record of every relation
searched.  `gpu/data/kripke_separator.json` lists only the cases with E nonempty.

Smallest case searched:

* lower world arity 2;
* one extension of arity 3;
* reindexing maps up to symmetry: a constant map, a map with fibres of sizes 2 and 1, and the
  set of all surjections (other sets of maps were not tried);
* all 676 compatible computable two-world Kripke relations built from arbitrary ordinary
  sequentiality relations.

For each Kripke relation K with ordinary lower-world baseline R, compute

```
E = K_D2(lower) \ R^ord_D2(lower).
```

Only tuples in E could separate a functional already preserving R.

Result: **E is empty for every one of the 676 cases.**

What was observed is only the inclusion `K_D2(w) ⊆ R^ord_D2(w)`.  The reverse inclusion was
not checked, and the size of the enlargement before reindexing was not measured.  The likely
mechanism:

* extension shrinks the admissible relation at D1, which alone would enlarge the arrow
  relation at D2;
* the Kripke reindexing/future-world obligation requires the pulled-back tuple to satisfy the
  ordinary relation upstairs, which apparently removes those extra D2 tuples.

This is the current frontier.

## 5. Highest-value next question

Before running the expensive arity-3 -> arity-4 one-extension search, investigate:

> **One-step collapse conjecture.**  For a two-world frame w < w+ with compatible
> sequentiality relations at ground type, does the lower-world Kripke relation at
> D2 = (B->B)->B always equal the corresponding ordinary single-world lift?  (The data so far
> shows only `⊆` in the 676 cases searched.)

If yes in general, skip every larger one-step experiment.

The proof should compare the two arrow liftings explicitly.  Export/inspect:

```
K_D1(w)
Rord_D1(w)
K_D2(w)
Rord_D2(w)
```

and the reindexing map.  Try both inclusions.  Identify whether the argument uses the fact
that w+ is terminal.

### If collapse uses terminality

The next meaningful experiment is the smallest chain

```
w0 < w1 < w2
```

because at w1 the argument relation itself anticipates w2.  This introduces nested future
dependence and is qualitatively different from a terminal one-step extension.

### If collapse does not use terminality and composes

Small linear chains may be dead too.  Then investigate whether branching worlds are needed,
or widen the semantic type.  Do not spend days on the arity-3 -> 4 one-step enumeration
until this is understood.

### If one-step collapse is false in general

Then optimize and run the arity-3 -> 4 one-extension search.  There are roughly
85 x 1,027 ground-relation pairs before compatibility filtering, so reuse the grouping,
symmetry and GPU lifting machinery rather than a naive product.

## 6. Progress metric for future Kripke-derived candidates

For any candidate obtained by violating an explicit computable Kripke relation:

1. the Kripke violation is already a sound proof of non-definability;
2. immediately run the complete ordinary arity-3 suite;
3. then all 1,027 symmetry classes of arity-4 intersections;
4. continue to higher ordinary arity only for survivors.

Record the maximum **complete ordinary arity survived**.

The previous explicit non-definable candidates score only 3: they survive all arity-3 tests
and die at arity 4.  A fixed Kripke-derived candidate surviving complete arities 4, 5, ...
would be qualitatively new evidence.

## 7. Files

* `SIEBER.md` -- mathematical results, sources, Loader type extraction.
* `GPU_SEARCH.md` -- original Metal/GPU implementation specification.
* `gpu/REPORT.md` -- chronological computational results and certificates.
* `gpu/sieber_cpu.py` -- CPU reference semantics/tests.
* `gpu/sieber_metal.py` -- Metal kernels.
* `gpu/m1.py`, `gpu/m2.py` -- arity-3 validation and batched search.
* `gpu/m4.py`, `gpu/export_m4.py` -- definability synthesis and exported columns/trees.
* `gpu/arity4_h3.py` -- complete arity-4 intersection search for the small candidate.
* `gpu/verify_candidate.py` -- independent numpy checks for the failed non-definable candidates.
* `gpu/search_kripke_two_world.py` -- smallest computable Kripke-vs-ordinary separator search.
* `gpu/data/` -- certificates and exported search data.

## 8. Things not to claim

* No explicit counterexample to Sieber's all-arity ordinary model has been found.
* Surviving finitely many ordinary arities never proves membership in Sieber's model.
* The three-cone and 20-cone non-definable tables are explicitly rejected at arity 4.
* The checked O'Hearn--Riecke `finiteTest` is not an effective finite enumerator of
  higher-order Kripke tests.
* The order-3/order-4 sharpenings documented on this branch are not Lean endpoints.
* The exact-order statements ("holds through order 2/3") are conditional on identifying
  $`D^B`$/$`D^N`$ with Sieber's presentation; do not state them unconditionally.
* No priority beyond `SIEBER.md`'s "Relation to the literature": the results combine
  O'Hearn--Riecke's p. 15 effective-presentation remark, Loader 2001 and (for Theorem B)
  Milner and Müller, made explicit and Lean-checked under stated hypotheses.
