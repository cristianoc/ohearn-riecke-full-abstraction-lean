# GPU search: report on M1–M2 and a proposal for M4

This reports on milestones M1 and M2 of [`GPU_SEARCH.md`](../GPU_SEARCH.md), the analysis that followed, and why M4 cannot be done as specified. The target type is $`τ_0=((B\to B)\to B)\to B`$, with candidates $`h : D_2 \to B`$ and $`|D_2|=355`$.

## Machine

Apple M2 Max (Mac14,6), 38 GPU cores, 32 GB. MLX 0.32.2, Python 3.12. The first dispatch, including Metal compilation, takes 9.3 ms; later dispatches take 0.5 ms.

## M1: arity-3 falsifier (`m1.py`)

One Metal kernel serves two levels:
- candidates $`D_1\to B`$, on the carrier $`D_1`$;
- candidates $`D_2\to B`$, on the carrier $`D_2`$.

It never materialises the lifted relation on $`D_2`$. The 86 distinct arity-3 tests include all arity-1 and arity-2 tests, because $`S^2_{A,B}\times V=S^3_{A,B}`$.

All gates pass:
- **A. Carriers.**
  - The carriers come out as 3 / 11 / 355.
  - The GPU-filtered $`D_2`$ is exactly the definable set.
  - The relations lifted to $`D_1`$ agree with an oracle that follows the definitions.
- **B. Differential testing.** 2,000 restricted-grid cases × 86 tests give 172,000 CPU/GPU comparisons, covering grids with and without witnesses. In addition, 20 definable candidates checked on the full $`D_2^3`$ grid have no witness anywhere.
- **C. Historical witnesses.** The AND witness $`((\bot,\bot,tt),(\bot,tt,\bot),(\bot,\bot,\bot))`$ under $`S^3_{01,012}`$ is rediscovered. Each of the 42 monotone non-carrier elements at $`D_2`$ gets a witness, verified on the CPU.

Metal provides only a weak compare-and-swap, so the kernel retries its claim. Otherwise a unique witness could be lost.

For one candidate that has no witness, checking all 86 tests on all 44.7M triples takes **0.95 s** on the GPU. A vectorised single-core numpy version of the same computation takes **33.5 s**, a **35×** speed-up. A multi-core CPU implementation would narrow this, probably to 3–5×; that figure is an estimate, not a measurement.

## M2: batched falsification (`m2.py`)

- **Candidates.** They come from the symbolic language of §7, are hash-consed by table, and are filtered for monotonicity on the CPU.
- **Witness bank.** A CPU bank of verified witnesses kills most dead candidates without any GPU work.
- **GPU kernel.** It dispatches only the non-constant output buckets $`H_u\times H_v\times H_z`$ of each candidate. For each bucket it scans only the tests that forbid that output pattern, most frequent killers first. Each test's lifted relation is ordered so the entries that fail most often come first.
- **Checks.** Every witness is re-verified on the CPU, and verdicts match M1 on 350 sampled candidates.

Results on 100,000 candidates:
- 171 candidates/s;
- **94% (93,932) survive all arity-3 tests**;
- the bank holds 790 witnesses.

Survivors dominate the running time, at about 6 ms each on the GPU.

**Conclusion.** Arity-3 falsification is cheap, but on this candidate language it rejects almost nothing.

## Size of the search space

$`D_2`$ has width 80. The certificate is an explicit antichain, checked pairwise, in `data/width_certificate.json`. So there are at least $`2^{80}\approx1.2\times10^{24}`$ monotone $`\{\bot,tt\}`$-valued candidates. At the measured rate that is about $`6\times10^{21}`$ s, roughly $`10^4`$ times the age of the universe, and a $`10^6\times`$ speed-up still leaves about $`2\times10^8`$ years. Exhaustive enumeration is ruled out. In any case, preservation of tests of every arity is not a finite check.

## Analysis of the survivors and the witness bank (`analyze_m2.py`)

Classes are taken up to the 16 symmetries of $`τ_0`$. These swap $`tt/ff`$ independently at each of the four occurrences of $`B`$. Negation is definable and each test is invariant under a simultaneous swap, so both definability and test preservation are invariant.

- **Survivors.** The 93,932 surviving tables fall into **13,460 classes**. Each class is represented by the minimal antichains of $`T_h=h^{-1}(tt)`$ and $`F_h=h^{-1}(ff)`$ (`data/m2_survivor_classes.json`).
  - By $`|\min T_h|+|\min F_h|`$ the counts are: 1 class of size 0, 66 of size 1, **13,272 of size 2**, 57 of size 3, and 64 of size 4.
  - The size-1 classes are principal cones, which are definable.
- **Witness bank.** The 790 certificates fall into 350 orbits (the orbits of the triple and test under the symmetries and coordinate permutations). They use **only two tests** up to coordinate permutation, each an intersection of two generators:
  - $`S^3_{\{0\},\{012\}}\cap S^3_{\{1,2\},\{012\}}`$: 761 certificates;
  - $`S^3_{\{0\},\{012\}}\cap S^3_{\{1,2\},\{1,2\}}`$: 29 certificates.

The single relation $`S^3_{01,012}`$ kills nothing here.

Explicitly, as ground relations on $`B^3`$:
```math
R_1 = S^3_{\{0\},\{012\}}\cap S^3_{\{1,2\},\{012\}}
    = \{ttt,\ fff\}\cup\{\bot\bot\bot,\ \bot\bot t,\ \bot\bot f,\ \bot t\bot,\ \bot f\bot\},
```
```math
R_2 = S^3_{\{0\},\{012\}}\cap S^3_{\{1,2\},\{1,2\}}
    = R_1\cup\{\bot tt,\ \bot ff\}.
```
Both say that if $`x_0`$ is defined, the triple is constant. They differ on the other two coordinates:
- $`R_1`$: if $`x_1`$ and $`x_2`$ are both defined, the whole triple is constant, so $`x_0`$ must be defined too;
- $`R_2`$: if $`x_1`$ and $`x_2`$ are both defined, they must be equal, but $`x_0`$ may be $`\bot`$.

For a candidate $`h`$, a violation is a related triple $`(F_0,F_1,F_2)`$ of $`D_2`$ on which:
- $`R_1`$: $`h`$ is defined on $`F_0`$ but not constant; or $`h`$ is defined on $`F_1`$ and $`F_2`$ but not on $`F_0`$, or not constant.
- $`R_2`$: $`h`$ is defined on $`F_0`$ but not constant; or $`h`$ is defined on $`F_1`$ and $`F_2`$ with different values.

## Arity-4 diagnostic (`diag_arity4.py`)

The question is whether arity 4 suddenly becomes strong. The diagnostic uses the elementary relations $`S^4_{A,B}`$ with $`A\neq\emptyset`$, which gives 61 distinct relations, without intersections. It runs on 180 survivor classes: the 60 smallest, 60 random and 60 largest.

A positive control passes: random tables are killed, and their witnesses are verified on the CPU. **0 of the 92 classes checked were killed**, and the run was then stopped. M4 below shows why: every survivor class is definable, and definable elements preserve every relation of every arity. On this candidate family the diagnostic could not have killed anything.

## Why M4 cannot be done as specified

Lemma 13 of [`SIEBER.md`](../SIEBER.md) uses Loader's equation-solvability problem, which is undecidable already at order 3 (Ong–Tzevelekos, *Functional Reachability*, Lemma 6 / Corollary 7, attributing the order-3 statement to Loader). The same argument rules out a uniform exact M4:
1. Suppose some algorithm decided, for any order-3 type and any table, whether the table is PCF-definable.
2. Every carrier's monotone function space is finite and computable. So we could list the candidates for the unknown, keep the definable ones, and check the equations.
3. That would decide Loader's order-3 problem. Hence **no such algorithm exists**.

Definability is semi-decidable, by enumerating terms. Non-definability is not, uniformly. In particular, no finite family of Kripke relations can decide definability at every order-3 type.

**Finite Kripke witnesses are sound but not known to be complete.** The Lean characterization `finiteTest` (`OR/FiniteWorlds.lean`) is not a finite object:
- its worlds are *all* typed contexts (`World := Ctx`);
- its ground relation at a world is the set of *definable* maps (`Def n Γ .nat`);
- the arrow clause quantifies over every extension of a context.

Enumerating finite Kripke relations (finitely many finite worlds, computable relations) therefore only gives sound rejections. It cannot be complete uniformly at order 3: otherwise definability would be semi-decidable on both sides, hence decidable. For $`τ_0`$ alone completeness is not excluded, but nothing guarantees it. So there is no guarantee that every pair below is eventually resolved.

For the single type $`τ_0`$ the question has a definite answer. But an exact M4 with a completeness justification (§8) needs an argument specific to $`τ_0`$; it cannot come from a general saturation engine.

## Reduction of the two-cone classes

The 13,272 two-cone classes all reduce to one question per unordered pair $`\{p,q\}`$ of minimal elements:
```math
\text{is } \uparrow p \cup \uparrow q \text{ the convergence domain of a definable term?}
```

For unions this is immediate: $`\mathrm{union}(p,q)`$ is $`tt`$ exactly on that domain. For races, $`\mathrm{race}(p,q)`$ is $`tt`$ on $`\uparrow p`$ and $`ff`$ on $`\uparrow q`$:
- If $`G`$ has that domain, then $`\mathrm{race}(p,q)=\mathsf{if}\ G\ \mathsf{then}\ Z\ \mathsf{else}\ Z`$. Here $`Z = \mathsf{case}\ F(φ)`$, where φ is a closed argument at which $`p`$ and $`q`$ are both defined and differ. Such a φ exists because the two cones are disjoint, so $`p`$ and $`q`$ are incompatible.
- Conversely, $`\mathsf{if}\ \mathrm{race}(p,q)\ \mathsf{then}\ tt\ \mathsf{else}\ tt`$ has the domain of the union.

The two-cone classes contain **6,775 distinct pairs**.

The earlier hand analysis shows why these problems are subtle. Terms can separate the cones with nested calls that exploit the order in which $`F`$ asks its argument. One example is
```math
F\bigl(λz.\ \mathsf{case}\ z\ \mathsf{of}\ tt\mapsto ff,\ ff\mapsto \mathsf{case}\ F(λz'.\cdots F(\bot tt)\cdots)\bigr).
```
Separators like this one, needed for 5-point cores, involve calls nested three deep.

## Proposal for M4: a two-sided search with certificates

Run over the 6,775 pair problems, each ending as definable, non-definable or open:
1. **Definable side.** Synthesise a term whose domain is $`\uparrow p\cup\uparrow q`$. Search for nested separator arguments, including the three-level shapes found by hand. A term found is a proof of definability.
2. **Non-definable side.** For pairs that synthesis does not settle, search for a violated Kripke relation: more worlds, larger arities, intersections of generators. By the fundamental lemma every definable element preserves every Kripke relation, so a violation is a proof of non-definability.
3. **Open pairs.** These are where an argument specific to $`τ_0`$ is needed. If both sides settle every pair, the result is a complete picture of two-cone definability at $`τ_0`$. The first pair certified non-definable would be the counterexample candidate. It would still need an all-arity argument for membership in Sieber's model.

M3 (high-throughput arity 4) is postponed. See the diagnostic above.

## M4 results (`m4.py`)

The M4 search (definable side only) settled every survivor class. **All of them are definable**, so the Kripke side was not needed.

| Survivor classes | Count | Settled by |
|---|---|---|
| Two-cone pair problems (covering 13,272 classes) | 6,775 | 6,497 by decision trees over the 11 closed calls $`F(φ)`$; the remaining 278 by one round of nested calls |
| Three or four cones | 121 | Decision trees over the same columns |
| Principal cones, and the constant $`\bot`$ | 67 | Definable by construction |

The 6,497 pairs settled by closed calls are exactly the pairs with incompatible $`p,q`$. One closed call at a point where they disagree sends each $`F`$ to at most one cone, and a principal test does the rest. The 278 hard pairs are the **compatible** ones: unions of two cones with a common upper bound, where convergence on either cone looks parallel. Every one is separated by a single level of nested calls. These are arguments $`λz.\,\mathsf{case}\ z\ \mathsf{of}\ tt\mapsto a,\ ff\mapsto b`$ or $`λz.\,a`$, where $`a,b`$ are constants or $`\mathsf{case}\ F(φ)`$ of constants. They exploit the order in which $`F`$ interrogates its argument.

**Direct verification.** Without using the union/race reduction, all 13,460 classes' own tables have decision trees over 4,233 columns: the 11 closed calls plus the first nested round.

**Soundness.** Certificates are correct by construction. Each column is the semantics of an explicit term, computed with the same $`D_2`$ tables as M1. A tree is accepted only if it computes the target table exactly.

### Consequence

No element in this candidate language is a counterexample. Every table the §7 language generated (up to five principal cones) that survives the arity-3 tests is PCF-definable.

If $`τ_0`$ has a non-definable Sieber element, it lies outside this family. It would need many cones with interlocking structure, or it could be that $`τ_0`$ is universal. The next step is to generate candidates that the definability side does *not* immediately solve. Examples are tables with many minimal cones, and tables built to defeat one level of nested calls. A second option is to widen the type (M5).

## A non-definable table that preserves every arity-3 test

`universality.py` asks z3 for a state $`(h,S)`$ with $`h`$ preserving all arity-3 tests and no progressing splitter among the 4,233 columns. It finds one at the root. That $`h`$ is $`ff`$ on a 146-element up-set with 20 minimal elements (`data/bad_state_h.npy`). `deepen.py` finds no column at the next nesting level that is total on its support, and `root_obstruction.py` turns this into a proof of non-definability. Three of the 20 minimal points already suffice, which gives a much smaller candidate:
```math
h_3(F)=\begin{cases} ff & F\in\ \uparrow 129\ \cup \uparrow 272\ \cup \uparrow 321,\\ \bot & \text{otherwise,}\end{cases}
```
with 35 support elements (`data/candidate_3cone_h.npy`). As tables on $`D_1=(\bot\bot\bot,\ \bot\bot t,\ \bot\bot f,\ \bot t\bot,\ \bot tt,\ \bot tf,\ \bot f\bot,\ \bot ft,\ \bot ff,\ ttt,\ fff)`$:

| Point | Table | Arguments on which it converges |
|---|---|---|
| 129 | `⊥⊥⊥⊥⊥f⊥tf⊥f` | `⊥tf ⊥ft ⊥ff fff` |
| 272 | `⊥⊥⊥fff⊥⊥⊥f⊥` | `⊥t⊥ ⊥tt ⊥tf ttt` |
| 321 | `⊥t⊥⊥t⊥⊥t⊥tf` | `⊥⊥t ⊥tt ⊥ft ttt fff` |

The common upper bounds are 281 of 129 and 272, and 333 (also 335) of 129 and 321. Points 272 and 321 have none.

`verify_candidate.py` checks both $`h_3`$ and the 20-cone $`h`$ using numpy only (no z3, no GPU):
1. $`h`$ is monotone.
2. $`h`$ preserves all 85 non-trivial arity-3 tests, over all 107,189,017 related triples of $`D_2`$.
3. $`h`$ is not PCF-definable. Suppose $`h`$ is definable and not constant. Its normal form $`λF.\,G`$ then evaluates a call $`F(ψ)`$ first, where $`ψ=λz.M`$ may use $`F`$. The conditional is strict, so $`F(ψ_F)\neq\bot`$ on all of $`\mathrm{supp}(h)`$. The map $`F\mapsto ψ_F`$ is definable, hence monotone. Whenever two support points have a common upper bound $`u`$, their $`ψ`$-values lie below $`ψ_u`$ and are therefore compatible. The allowed arguments above make this impossible:
   - compatibility of 129 with 272 along 281 forces $`ψ_{129}=\bot tf`$, because every allowed argument of 272 is $`t`$ at $`tt`$;
   - compatibility of 129 with 321 along 333 forces $`ψ_{129}\in\{\bot ft,\ \bot ff,\ fff\}`$.

Neither $`h`$ nor $`h_3`$ is killed by the 61 elementary arity-4 relations $`S^4_{A,B}`$ either.

**Status.** $`h_3`$ is a non-definable table that preserves every arity-3 Sieber test. It is a counterexample to universality of $`τ_0`$ if it also preserves Sieber's relations of **every** arity, and that is the open step. Point 3 relies on the head-call lemma, proved in [`HEADCALL.md`](../HEADCALL.md) (Lemma 4 and Theorem 6).

### Arity 4 kills both candidates (`arity4_h3.py`)

There are 17,240 distinct intersections of $`S^4_{A,B}`$, or 1,027 up to coordinate permutation. For each one, z3 searches for a related tuple of $`D_2`$ whose image under the candidate lies outside the relation, and every witness is re-verified directly. The positive control (a random table) is killed.

- $`h_3`$ is **killed**: 39 of the first 400 tests already have witnesses. The first is the relation $`R = S^4_{\{0\},\{0123\}}\cap S^4_{\{1,2\},\{1,2\}}\cap S^4_{\{1,3\},\{1,3\}}\cap S^4_{\{1,2,3\},\{0123\}}`$ with the tuple $`(12,\,129,\,323,\,276)`$. Coordinates 1–3 lie in the three cones (above 129, 321 and 272), and 12 is a common lower bound of all three. The outputs are $`(\bot,ff,ff,ff)`$, but $`R`$ requires coordinate 0 to be defined whenever coordinates 1, 2 and 3 all are. This is the four-coordinate form of the main arity-3 killer, and it detects exactly the three-way "parallel" convergence behind the non-definability proof.
- The 20-cone table is **killed** too, by the tuple $`(2,\,259,\,321,\,78)`$.

**Conclusion.** Neither table is in Sieber's model. The first-call obstruction ("no monotone $`ψ`$ makes the first call total") is sound for non-definability, but here the arity-4 relations see it as well.

**Next steps.**
- Add arity-4 constraints to the universality SAT query, lazily, with this search as the oracle. That asks whether some table preserves all arity-4 tests and still has no admissible first call.
- Test the conjecture that $`k`$ mutually "parallel" cones are killed at arity $`k+1`$. A counterexample must defeat the first call in a way no finite-arity relation of this shape can express.

## Kripke-vs-ordinary separators (`kripke_separator.py`)

Candidates are now derived from Kripke behaviour itself. For a computable Kripke relation $`K`$ with sequentiality relations as ground components, every PCF term satisfies the fundamental lemma. So a violation of $`K`$ proves non-definability.

If $`h`$ preserves the ordinary test $`R(w)`$, any violation of $`K`$ at world $`w`$ must use a tuple in
```math
E = K_{D_2}(w)\setminus R^{\mathrm{ord}}_{D_2}(w),
```
the tuples made related only by world extension. Maps into the extension world reduce to ordinary tests there. For each $`K`$ the search computes $`E`$. If $`E\neq\emptyset`$, z3 looks for a monotone $`h`$ that preserves all arity-3 tests and violates $`K`$ on $`E`$, and each hit then goes through the arity-4 gauntlet.

**Result.** $`E=\emptyset`$ for all 676 relations with worlds $`w`$ of arity 2 and $`w^+`$ of arity 3:
- $`R(w)`$ ranges over the arity-2 tests and $`R(w^+)`$ over the arity-3 tests;
- the maps $`w^+\to w`$ are, up to symmetry, a constant map, a map with fibre sizes 2 and 1, or all surjections.

The per-case record, one entry per relation including those with $`E=\emptyset`$, is `data/kripke_separator_all.json`; `data/kripke_separator.json` lists only the cases with $`E\neq\emptyset`$.

In other words $`K_{D_2}(w)\subseteq R^{\mathrm{ord}}_{D_2}(w)`$ in every case, and $`K_{D_1}(w)\subseteq R^{\mathrm{ord}}_{D_1}(w)`$ as well. The reverse inclusion $`R^{\mathrm{ord}}_{D_2}(w)\subseteq K_{D_2}(w)`$ holds in 636 cases and fails in 40 (test indices 1 and 3); in 33 of those $`K_{D_1}(w)`$ is already strictly smaller, and in the other 7 the reindexing condition alone removes tuples. The Kripke relation is therefore equal to the ordinary lift or strictly smaller, and no separation is possible with these worlds.

## Non-definability cores and the tests that kill them

A **core** is a set $`K \subseteq D_2`$ such that no head call $`\psi : D_2 \to D_1`$ that is monotone and preserves the tests of arity $`\le 3`$ has $`F(\psi_F)`$ defined for every $`F \in K`$. A definable non-constant table has such a head call (HEADCALL.md, Lemma 4; Lean: `OR/Sieber/HeadCall.lean`), and adding support only adds constraints on $`\psi`$, so every non-constant table defined on a core is not definable. A non-constant monotone table is $`\bot`$ at the least element $`\bot`$ of $`D_2`$.

**Head-call test (`headcall_sat.py`, computed).** z3 searches for such a $`\psi`$, adding arity-3 constraints lazily. It reports no head call for $`h_3`$ and for the 20-cone table, and finds one for the definable control $`F \mapsto F(\bot tf)`$ and for a table with 27 support points and no total column among the 4,233 of M4. `cores.py` shrinks the 20 minimal points of the 20-cone table to the core $`\{129, 272, 321\}`$, the core of $`h_3`$.

**The core of $`h_3`$ is killed at arity 4 (computed).** `core4.py 55 129 272 321` asks for a non-constant monotone table defined on 129, 272 and 321 that preserves every test of arity $`\le 4`$, with arity-3 and arity-4 constraints added lazily as related tuples (each related tuple forbids every output pattern outside the test). The answer is UNSAT after one arity-4 constraint: the tuple $`(\bot, 129, 272, 323)`$, with $`323 \ge 321`$, is related for a test that excludes every pattern $`(\bot, u, v, w)`$ with $`u, v, w`$ defined.

**Small cores die at arity $`|K|+1`$ (computed).** `core_kills.py 55` enumerates the cores of Theorem 6's kind (pairwise compatibility on pairs with a common upper bound) of size 2 and the minimal ones of size 3:

| Cores | Number | Killed through a tuple $`(\bot, K)`$ at arity $`\lvert K\rvert+1`$ |
|---|---|---|
| size 2 | 1,036 | 1,036, at arity 3 |
| size 3, containing no core of size 2 | 39,488 | 39,488, at arity 4 |

In each case a test of arity $`|K|+1`$ relates $`(\bot, K)`$ (in some order) and excludes every pattern that is $`\bot`$ at $`\bot`$'s position and defined at the others, so no table defined on $`K`$ lies in Sieber's model.

**Conjecture P.** For every core $`K`$, some test of arity $`|K|+1`$ relates a tuple formed by $`\bot`$ and elements above the points of $`K`$ and excludes every pattern that is $`\bot`$ at the first coordinate and defined elsewhere. With an inductive version for the states of `universality.py`, Conjecture P would make $`τ_0`$ universal, and would place the non-definable elements given by `SIEBER.md` Lemma 13 at other order-3 types.
