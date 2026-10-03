# Arity of Sieber tests needed to decide membership

This note concerns the ordinary Boolean Sieber model of [`SIEBER.md`](SIEBER.md) §1: carriers $`D_\tau`$, tests $`R`$ (finite intersections of $`S^w_{A,B}`$), lifted relations $`R_\tau`$. A monotone $`f : D_\sigma \to D_\rho`$ lies in $`D_{\sigma\to\rho}`$ when $`(f,\dots,f) \in R_{\sigma\to\rho}`$ for every test $`R`$ of every arity. The question is how large an arity must be considered to decide membership at a fixed type. A counterexample candidate such as $`h_3`$ of [`gpu/REPORT.md`](gpu/REPORT.md) is certified only by preservation at every arity.

Labels: **proved** (proof given here), **cited** (source and scope given), **computed** (finite computation, script and data file given), **conjectured**.

## 1. Notation

For a map $`\pi : w \to k`$ and a set $`X`$, write $`\Delta_\pi : X^k \to X^w`$ for $`y \mapsto y \circ \pi`$. For a test $`R`$ of arity $`w`$,
```math
\pi^*R = \{\, x \in V^k \mid x\circ\pi \in R \,\}.
```
For a type $`\tau`$ and a surjection $`\pi`$ put
```math
P_\tau = \pi^*(R_\tau) = \{\, x \in D_\tau^{\,k} \mid x\circ\pi \in R_\tau \,\},
\qquad
Q_\tau = (\pi^*R)_\tau .
```
$`E_\pi`$ is the fibrewise-equality test
```math
E_\pi = \bigcap_{j<k} S^w_{\emptyset,\ \pi^{-1}(j)} = \{\, g \in V^w \mid g \text{ is constant on every fibre of } \pi \,\}.
```
A tuple $`G \in D_\tau^{\,w}`$ is *fibre-constant* when $`G_i = G_{i'}`$ whenever $`\pi(i) = \pi(i')`$, that is, when $`G \in \Delta_\pi(D_\tau^{\,k})`$.

The *order* is $`\mathrm{ord}(B) = 0`$, $`\mathrm{ord}(\sigma\to\rho) = \max(\mathrm{ord}(\sigma)+1, \mathrm{ord}(\rho))`$, as in `SIEBER.md` (17).

## 2. Reindexing and lifting

### 2.1 Ground reindexing

**Lemma R1 (proved; Lean: `Elem.pullback`, `Test.holds_pullback` in `OR/Sieber/Arity/Reindex.lean`).** For every map $`\pi : w \to k`$ and $`A \subseteq B \subseteq w`$,
```math
\pi^* S^w_{A,B} = S^k_{\pi(A),\,\pi(B)} .
```
Hence $`\pi^*`$ commutes with finite intersections (including the empty one, $`\pi^*V^w = V^k`$), and $`\pi^*R`$ is a test: if $`R = \bigcap_j S^w_{A_j,B_j}`$ then $`\pi^*R = \bigcap_j S^k_{\pi(A_j),\pi(B_j)}`$.

*Proof.* For $`x \in V^k`$: some $`i \in A`$ has $`x_{\pi(i)} = \bot`$ iff some $`j \in \pi(A)`$ has $`x_j = \bot`$; and $`x\circ\pi`$ is constant on $`B`$ iff $`x`$ is constant on $`\pi(B)`$. Also $`\pi(A) \subseteq \pi(B)`$. Edge cases are covered by the same two equivalences: for $`A = \emptyset`$ the first disjunct is false on both sides; when $`|\pi(B)| \le 1`$ (in particular $`B = \emptyset`$, or $`B`$ inside one fibre) both sides are the full relation. Preimages commute with intersections. $`\square`$

The proof uses only $`\bot`$ and equality of values, so Lemma R1 holds verbatim over $`ℕ_\bot`$. Surjectivity is not needed for R1; it is used in R2.

### 2.2 The lifted reindexed test

**Lemma R2 (proved).** Let $`\pi : w \to k`$ be surjective and $`R`$ a test of arity $`w`$. For every type $`\tau`$:
1. every tuple in $`(R \cap E_\pi)_\tau`$ is fibre-constant;
2. $`(\pi^*R)_\tau = \Delta_\pi^{-1}\bigl((R\cap E_\pi)_\tau\bigr)`$.

*Proof.* Constant tuples of carrier elements lie in every lifted relation (`SIEBER.md`, Lemma 1).

1. Induction on $`\tau`$. At $`B`$, $`R\cap E_\pi \subseteq E_\pi`$. At $`\sigma\to\rho`$, let $`F \in (R\cap E_\pi)_{\sigma\to\rho}`$ and $`a \in D_\sigma`$. The constant tuple $`(a,\dots,a)`$ is in $`(R\cap E_\pi)_\sigma`$, so $`(F_i\,a)_i \in (R\cap E_\pi)_\rho`$, which is fibre-constant by induction. Thus $`F_i\,a = F_{i'}\,a`$ for all $`a`$ when $`\pi(i)=\pi(i')`$, and $`F_i = F_{i'}`$ by extensionality.
2. Induction on $`\tau`$. At $`B`$: $`x \in \pi^*R`$ iff $`\Delta x \in R`$ iff $`\Delta x \in R\cap E_\pi`$. At $`\sigma\to\rho`$: $`x \in (\pi^*R)_{\sigma\to\rho}`$ iff for every $`y`$ with $`\Delta y \in (R\cap E_\pi)_\sigma`$, $`\Delta(xy) = (\Delta x)(\Delta y) \in (R\cap E_\pi)_\rho`$. By item 1 and surjectivity of $`\pi`$, every $`G \in (R\cap E_\pi)_\sigma`$ is $`\Delta y`$ for exactly one $`y`$, so this says $`\Delta x \in (R\cap E_\pi)_{\sigma\to\rho}`$. $`\square`$

So $`P_\tau = \Delta^{-1}(R_\tau)`$ and $`Q_\tau = \Delta^{-1}((R\cap E_\pi)_\tau)`$: comparing $`P`$ with $`Q`$ is comparing the lifts of $`R`$ and of $`R\cap E_\pi`$ on fibre-constant tuples. Lifting does not commute with intersection at higher types, and that is the whole difference.

### 2.3 Which inclusion holds

**Lemma R3 (proved).** Fix $`R`$ and a surjection $`\pi`$.
1. $`P_B = Q_B`$ (Lemma R1).
2. If $`Q_\sigma \subseteq P_\sigma`$ and $`P_\rho \subseteq Q_\rho`$, then $`P_{\sigma\to\rho} \subseteq Q_{\sigma\to\rho}`$.
3. If $`P_\sigma \subseteq Q_\sigma`$ and $`Q_\rho \subseteq P_\rho`$, then every $`x \in Q_{\sigma\to\rho}`$ satisfies $`(\Delta x)\,G \in R_\rho`$ for every **fibre-constant** $`G \in R_\sigma`$.

*Proof.* (2) Let $`\Delta x \in R_{\sigma\to\rho}`$ and $`y \in Q_\sigma \subseteq P_\sigma`$. Then $`\Delta y \in R_\sigma`$, so $`\Delta(xy) \in R_\rho`$, i.e. $`xy \in P_\rho \subseteq Q_\rho`$. (3) Let $`G = \Delta y \in R_\sigma`$. Then $`y \in P_\sigma \subseteq Q_\sigma`$, so $`xy \in Q_\rho \subseteq P_\rho`$, i.e. $`(\Delta x)G = \Delta(xy) \in R_\rho`$. $`\square`$

Membership $`\Delta x \in R_{\sigma\to\rho}`$ quantifies over **all** $`G \in R_\sigma`$, including those that are not fibre-constant; item 3 reaches only the fibre-constant ones. This is the only obstruction to $`Q \subseteq P`$.

**Corollary R4 (proved).** If every argument type of $`\tau`$ is $`B`$, i.e. $`\tau = B^n \to B`$, then $`P_\tau \subseteq Q_\tau`$ for every test and every surjection. More generally $`P_{\sigma_1\to\cdots\to\sigma_n\to B} \subseteq Q_{\sigma_1\to\cdots\to\sigma_n\to B}`$ whenever $`Q_{\sigma_j} \subseteq P_{\sigma_j}`$ for all $`j`$.

*Proof.* Induction on $`n`$ with R3.2, using $`Q_B = P_B`$ at each argument and at the result. $`\square`$

**Proposition R5 (proved): equality fails already at $`B \to B`$.** The reverse inclusion $`Q_{B\to B} \subseteq P_{B\to B}`$ is false. Take
```math
R = S^3_{\{0,1\},\{0,1,2\}},\qquad \pi = (0,1,0) : 3 \to 2,\qquad \pi^*R = S^2_{\{0,1\},\{0,1\}},
```
and $`x = (x_0, x_1)`$ with $`x_0 = (\bot,\bot,\mathsf{tt})`$ (the table on $`\bot,\mathsf{tt},\mathsf{ff}`$) and $`x_1 = \lambda v.\mathsf{tt}`$.
- $`x \in Q`$: for $`y \in \pi^*R`$ the output is $`(x_0\,y_0,\ \mathsf{tt})`$ with $`x_0\,y_0 \in \{\bot,\mathsf{tt}\}`$, which lies in $`\pi^*R`$.
- $`x \notin P`$: $`g = (\mathsf{ff},\bot,\bot) \in R`$, and $`(\Delta x)\,g = (x_0\,\mathsf{ff},\ x_1\,\bot,\ x_0\,\bot) = (\mathsf{tt},\mathsf{tt},\bot) \notin R`$.

The argument $`g`$ is not constant on the fibre $`\{0,2\}`$ (it is $`\mathsf{ff}`$ and $`\bot`$ there). So the statement "at types with only ground arguments the two coincide" is false; what holds is the one inclusion R4.

**Proposition R5′ (proved): the same at $`(B\to B)\to B`$.** With
```math
R = R_1 = S^3_{\{0\},\{0,1,2\}} \cap S^3_{\{1,2\},\{0,1,2\}},\qquad \pi = (0,0,1),\qquad \pi^*R = S^2_{\{0\},\{0,1\}},
```
(the main arity-3 killer of `gpu/REPORT.md`), let $`x_0 = \lambda f.\,\mathsf{if}\ f\,\bot\ \mathsf{then}\ \bot\ \mathsf{else}\ \mathsf{tt}`$ (it is $`\mathsf{tt}`$ exactly at $`f = \lambda v.\mathsf{ff}`$) and $`x_1 = \lambda f.\mathsf{tt}`$. Then $`x \in Q_{D_2}`$, since the output $`(x_0\,y_0, \mathsf{tt})`$ has first component in $`\{\bot,\mathsf{tt}\}`$. And $`x \notin P_{D_2}`$: the tuple $`G = (\lambda v.\bot,\ \lambda v.\mathsf{ff},\ \lambda v.\bot)`$ is in $`(R_1)_{B\to B}`$ (its outputs are $`(\bot,\mathsf{ff},\bot)`$, with $`\bot`$ at coordinate $`0 \in A`$ and in $`\{1,2\}`$), but $`(\Delta x)\,G = (\bot,\mathsf{tt},\mathsf{tt}) \notin R_1`$. Here $`G`$ is an argument tuple at $`D_{B\to B}`$ that is not constant on the block $`\{0,1\}`$.

### 2.4 Computation (computed)

`gpu/arity_lib.py` implements $`P`$, $`Q`$ and the right-hand side of R2.2 directly from the definitions on the carriers $`D_{B\to B}`$ (11), $`D_{B\to B\to B}`$ (163) and $`D_2 = D_{(B\to B)\to B}`$ (355). The two higher carriers are taken as the definable elements, which is correct at order $`\le 2`$ (`SIEBER.md`, Theorem U, cited from Sieber; `gpu/REPORT.md` gate A checks $`D_2`$ computationally). The arity-4 tests are a seeded random sample of the 17,241 distinct intersections of $`S^4_{A,B}`$.

| Level | Tests × surjections | Tuples | $`P\subseteq Q`$ | $`Q\subseteq P`$ | R2.2 | File |
|---|---|---|---|---|---|---|
| $`B\to B`$ | all 86 arity-3 × 6 maps $`3\to2`$ | all | 516/516 | 390/516 | 516/516 | `arity_reindex_first_order.json` |
| $`B\to B\to B`$ | all 86 arity-3 × 6 maps $`3\to2`$ | all | 516/516 | 372/516 | 516/516 | same |
| $`B\to B`$ | 40 arity-4 × 50 maps $`4\to2,3`$ | all | 2000/2000 | 854/2000 | 2000/2000 | same |
| $`D_2`$ | all 86 arity-3 × 6 maps $`3\to2`$ | all 126,025 pairs | 516/516 | 372/516 | 516/516 | `arity_reindex_D2_w3.json` |
| $`D_2`$ | 3 arity-4 × 14 maps $`4\to2`$ | all pairs | 42/42 | 20/42 | 42/42 | `arity_reindex_D2_w4.json` |
| $`D_2`$ | 7 arity-4 (seed 2), the 169 (test, map) pairs with $`Q_{B\to B}\not\subseteq P_{B\to B}`$ | all pairs ($`k=2`$, 49 maps) or 20,000 random triples ($`k=3`$, 120 maps) | no counterexample | — | — | `arity_focus.json` |

Every file records the first explicit instance of $`Q\not\subseteq P`$ with its violating argument; R5 and R5′ above are those instances, checked by hand.

By R3.2, a pair $`(R,\pi)`$ with $`Q_{B\to B} \subseteq P_{B\to B}`$ gives $`P_{D_2} \subseteq Q_{D_2}`$ for free. The informative $`D_2`$ checks are therefore the pairs with $`Q_{B\to B} \not\subseteq P_{B\to B}`$: 126 of the 516 arity-3 pairs (all checked exhaustively over pairs of $`D_2`$) and the 169 arity-4 pairs of `arity_focus.json`. In none of them does $`P_{D_2} \not\subseteq Q_{D_2}`$ occur. There is no instance with $`P \not\subseteq Q`$ at any level checked.

**Conjecture R7 (false).** $`P_{D_2} \subseteq Q_{D_2}`$ for every test and every surjection. It holds for every test of arity at most 3 (the table above, with `R7.md` M2–M3) and fails at arity 4: `R7.md` §4 gives a test of arity 4, a single merge $`\pi : 4 \to 3`$ and a triple in $`P_{D_2} \setminus Q_{D_2}`$ (computed). The random arity-4 sample above does not contain that test.

## 3. Arity bounds for the diagonal

For a type $`\tau`$ let $`N(\tau)`$ be the least $`N`$ such that every monotone candidate $`f \notin D_\tau`$ (with all argument carriers the true ones) fails some test of arity $`\le N`$.

**Proposition R0 (proved, non-constructive).** $`N(\tau)`$ is finite for every $`\tau`$. The candidates form a finite set (`SIEBER.md`, Lemma 3), each non-member fails some test, and $`N(\tau)`$ is the maximum over non-members of the least failing arity.

**Theorem R6 (proved; Lean: `R6`, `R6_bound` in `OR/Sieber/Arity/Bound.lean`, for every candidate function, monotone or not).** Let $`\tau = \sigma_1\to\cdots\to\sigma_n\to B`$ and suppose $`P_{\sigma_j} \subseteq Q_{\sigma_j}`$ for every $`j`$, every test and every surjection. If a monotone $`f`$ fails a test $`R`$ of arity $`w`$, then it fails $`\pi^*R`$ for a surjection $`\pi : w \to k`$ with
```math
k \le \min\Bigl(w,\ \prod_{j=1}^n |D_{\sigma_j}|\Bigr).
```
Hence $`N(\tau) \le \prod_j |D_{\sigma_j}|`$.

*Proof.* Unfolding the definition, $`(f,\dots,f) \notin R_\tau`$ means that there are $`G^j \in R_{\sigma_j}`$ with $`\bigl(f\,G^1_i\cdots G^n_i\bigr)_i \notin R`$. Let $`\pi : w \to k`$ be the surjection onto the set of distinct columns $`(G^1_i,\dots,G^n_i)`$, so $`k \le \prod_j |D_{\sigma_j}|`$, and write $`G^j = y^j\circ\pi`$. Then $`y^j \in P_{\sigma_j} \subseteq Q_{\sigma_j} = (\pi^*R)_{\sigma_j}`$. The output tuple is $`\bigl(f\,y^1_l\cdots y^n_l\bigr)_l \circ \pi \notin R`$, so $`\bigl(f\,y^1_l\cdots y^n_l\bigr)_l \notin \pi^*R`$. Thus $`(f,\dots,f) \notin (\pi^*R)_\tau`$, and $`\pi^*R`$ is a test of arity $`k`$ by R1. $`\square`$

The bound counts distinct argument columns only. It does not lower the arity of a failing tuple whose entries are pairwise distinct.

**Corollary R6a (proved).** By R4, the hypothesis of R6 holds when every $`\sigma_j`$ has order $`\le 1`$, that is, at every type of order $`\le 2`$:
- $`N(B^n\to B) \le 3^n`$;
- $`N\bigl((B\to B)\to B\bigr) \le |D_{B\to B}| = 11`$;
- in general $`N(\tau) \le \prod_j |D_{\sigma_j}|`$ for $`\mathrm{ord}(\tau) \le 2`$.

Since $`D_\sigma`$ at order $`\le 1`$ is computed by finitely many tests, $`\tau \mapsto D_\tau`$ is computable at order $`\le 2`$ from tests alone. This agrees with Sieber's definability at order $`\le 2`$ (cited, `SIEBER.md` Theorem U). For $`(B\to B)\to B`$ the computation of `gpu/REPORT.md` (gate A) shows that arity 3 already suffices, so the bound 11 is not sharp there.

## 4. The type $`\tau_0 = ((B\to B)\to B)\to B`$

R6 applies to $`\tau_0`$ with the single argument $`\sigma = (B\to B)\to B`$ exactly when $`P_{D_2} \subseteq Q_{D_2}`$ for all tests and surjections, which is Conjecture R7. R7 fails (`R7.md` §4), so R6 gives no bound at $`\tau_0`$.

- **Proved.** $`N(\tau_0)`$ is finite (R0).
- **Proved, from a computation.** $`N(\tau_0) \ge 4`$. The table $`h_3`$ is not in $`D_{\tau_0}`$ but preserves every test of arity $`\le 3`$. Both facts are computed in `gpu/REPORT.md`: preservation by `gpu/verify_candidate.py`, exhaustive over all 107,189,017 related triples of $`D_2`$; failure by `gpu/arity4_h3.py`, with the test $`R = S^4_{\{0\},\{0123\}}\cap S^4_{\{1,2\},\{1,2\}}\cap S^4_{\{1,3\},\{1,3\}}\cap S^4_{\{1,2,3\},\{0123\}}`$ and the related tuple $`(12,129,323,276)`$ of $`D_2`$, whose image $`(\bot,\mathsf{ff},\mathsf{ff},\mathsf{ff})`$ is outside $`R`$. The witness is re-checked with `arity_lib.related` (command below). Its four entries are distinct, so no reindexing lowers its arity.
- **Open.** Any upper bound on $`N(\tau_0)`$ beyond finiteness. The counterexample to R7 shows that R6's proof does not transfer; it does not show that $`N(\tau_0) > 355`$.

**Where the argument stops.** The route to R7 through R3.2 needs $`Q_{B\to B} \subseteq P_{B\to B}`$, and R5 refutes it: $`(R_{B\to B})`$ is defined by ground tuples that are not constant on the blocks of $`\pi`$. One level up, $`Q_{D_2} \subseteq P_{D_2}`$ fails as well (R5′), through argument tuples at $`D_{B\to B}`$ that are not constant on the blocks. By Corollary R4 this second failure blocks R3.2 for every type whose argument is $`\tau_0`$ itself, so the same route gives nothing at order 4 either. For $`\tau_0`$ the inclusion $`P_{D_2} \subseteq Q_{D_2}`$ holds at arity at most 3 and fails at arity 4 (`R7.md` §4).

**Interpretation (not a theorem).** The tuples that $`R`$ admits and $`R\cap E_\pi`$ excludes are those that distinguish coordinates which $`\pi`$ identifies. In O'Hearn–Riecke's Kripke relations a world extension with a reindexing map plays the same role: the arrow clause at the smaller world also quantifies over tuples available only in the extended world. `gpu/REPORT.md` (Kripke-vs-ordinary separators) finds that, for the two-world relations tried, these extra tuples do not enlarge the relation at $`D_2`$. R7 is the analogous statement for ordinary tests under reindexing, and it fails at arity 4.

**Relation to the $`h_3`$ pattern (conjectured).** `gpu/REPORT.md` conjectures that $`k`$ mutually "parallel" cones are first killed at arity $`k+1`$. Together with width 80 of $`D_2`$ this would suggest that $`N(\tau_0)`$ grows with the largest family of such cones. No such family beyond $`k = 3`$ is known.

## 5. Effective presentation and Loader

**Cited.** O'Hearn and Riecke, *Kripke logical relations and PCF*, Inf. & Comp. 120(1), 1995, printed p. 15: "if, for instance, Sieber's more tame relations determined the fully abstract model, there would be an effective presentation." On the same page they call Loader's (1994) full-type-hierarchy result "apparently not immediately relevant to the PCF definability problem". They do not say how the effective presentation is obtained. Curien (*Definability and full abstraction*, ENTCS 172, 2007, §2) states the general principle that a direct construction of the fully abstract model would lead to an effective presentation; he does not apply it to Sieber's relations.

**Proposition L1 (proved).** If some computable $`\tau \mapsto M(\tau)`$ satisfies $`M(\tau) \ge N(\tau)`$, then $`\tau \mapsto D_\tau`$ (with order and application tables) is computable.

*Proof.* Induction on $`\tau`$. Given $`D_\sigma`$ and $`D_\rho`$, list the finitely many monotone candidates and the finitely many tests of arity $`\le M(\tau)`$; for each test the lifted relations at $`\sigma`$ and $`\rho`$ are finite sets computed from the known carriers; keep the candidates whose constant tuple lies in every such relation. By the choice of $`M`$, these are exactly the members of $`D_\tau`$. $`\square`$

**Proposition L2 (proved).** If such a computable $`M`$ exists, then Loader's theorem implies that the finitary Boolean Sieber model is neither universal nor equationally fully abstract.

*Proof.* If it were equationally fully abstract, then $`M \simeq N`$ iff $`⟦M⟧ = ⟦N⟧`$; with L1 the denotations are computable by evaluation on finite tables, so $`\simeq`$ would be decidable, contradicting Loader. Universality implies equational full abstraction (`SIEBER.md`, Lemma 4). $`\square`$

This route to non-universality does not use `SIEBER.md` Lemma 6 (universality implies effectiveness); it replaces that lemma by the computable bound. Non-universality is already proved (Theorem A), so L2 adds only the failure of equational full abstraction for the finitary model, which `SIEBER.md` §3 leaves open. Contrapositively: if the finitary model is equationally fully abstract, no computable bound $`M \ge N`$ exists. This is the precise content of the O'Hearn–Riecke remark in the setting of this repository. Theorem R6 gives such a bound at order $`\le 2`$; at order 3 none is known.

## 6. Reproduction

From `gpu/`. The first run of any script builds $`D_2`$ (about 18 s) and caches it in `data/arity_D2.npy`.

| Command | Time | Output |
|---|---|---|
| `python3 arity_reindex.py --deadline 55 --parts 0,1,2 --out data/arity_reindex_first_order.json` | 39 s | first-order rows of §2.4 |
| `python3 arity_reindex.py --deadline 540 --parts 3 --out data/arity_reindex_D2_w3.json` | 222 s | $`D_2`$, arity 3 |
| `python3 arity_reindex.py --deadline 55 --parts 4 --n4_d2 3 --out data/arity_reindex_D2_w4.json` | 36 s | $`D_2`$, arity 4 |
| `python3 arity_focus.py --deadline 45` | 45 s | `data/arity_focus.json` |

Each run stops at its deadline and writes partial results; `"complete": false` in a run record marks a stop. Arity-4 samples use `--seed` (default 1; `arity_focus.py` default 2).

Re-check of the $`h_3`$ witness:
```
python3 -c "import arity_lib as L, numpy as np
D1,_=L.level_D1(); D2=L.level_D2(D1); h=np.load('data/candidate_3cone_h.npy')
R=L.elementary(4,[0],[0,1,2,3])&L.elementary(4,[1,2],[1,2])&L.elementary(4,[1,3],[1,3])&L.elementary(4,[1,2,3],[0,1,2,3])
X=np.array([[12,129,323,276]]); print(L.related(D2.elems,D2.argrel(R),R,X), [int(h[i]) for i in X[0]])"
```
It prints `[ True] [0, 2, 2, 2]`: the tuple is related and its image $`(\bot,\mathsf{ff},\mathsf{ff},\mathsf{ff})`$ is outside $`R`$.
