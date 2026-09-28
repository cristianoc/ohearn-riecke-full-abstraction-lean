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

## Arity-4 diagnostic (`diag_arity4.py`)

The question is whether arity 4 suddenly becomes strong. The diagnostic uses the elementary relations $`S^4_{A,B}`$ with $`A\neq\emptyset`$, which gives 61 distinct relations, without intersections. It runs on 180 survivor classes: the 60 smallest, 60 random and 60 largest.

A positive control passes: random tables are killed, and their witnesses are verified on the CPU. At the time of writing, **0 of the first 30 classes are killed**. The run takes about 20 s per class, and its results go to `data/arity4_diagnostic.json`.

## Why M4 cannot be done as specified

Lemma 13 of [`SIEBER.md`](../SIEBER.md) uses Loader's equation-solvability problem, which is undecidable already at order 3 (Ong–Tzevelekos, *Functional Reachability*). The same argument rules out a uniform exact M4:
1. Suppose some algorithm decided, for any order-3 type and any table, whether the table is PCF-definable.
2. Every carrier's monotone function space is finite and computable. So we could list the candidates for the unknown, keep the definable ones, and check the equations.
3. That would decide Loader's order-3 problem. Hence **no such algorithm exists**.

Definability is semi-decidable, by enumerating terms. Non-definability is not, uniformly. In particular, no finite family of Kripke relations can decide definability at every order-3 type.

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

M3 (high-throughput arity 4) is postponed unless the diagnostic shows arity 4 is strong.
