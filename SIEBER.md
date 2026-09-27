# Sieber's model is not universal

O'Hearn and Riecke obtain full abstraction for PCF with *Kripke* logical relations, and leave open (conclusion, printed p. 14) whether Sieber's ordinary sequentiality relations, of fixed but arbitrary arity, already suffice for full abstraction.

This note proves a weaker statement: for finitary PCF, assuming Loader's theorem, **Sieber's model is not universal**. Some element is not the denotation of any closed term. Sections 1–3 give the proof, which is formalised in Lean (`OR/Sieber/`).

**This does not settle the open problem.** Universality and full abstraction are different properties. Lemma 4 shows that universality implies full abstraction, but a model can contain non-definable elements and still satisfy $`M \simeq N \iff ⟦M⟧ = ⟦N⟧`$ for all terms. Section 4 describes a proposed route from this theorem to a negative answer to the open problem, over the natural numbers, and the external results it still depends on.

The argument is nonconstructive: it shows that a non-definable element exists, but does not exhibit one. We have not found this result stated in the literature.

## 1. Definitions

**Finitary PCF.** Types are $`\tau ::= B \mid \sigma \to \tau`$. Terms are those of the simply typed λ-calculus with constants $`\mathsf{tt}, \mathsf{ff}, \bot : B`$ and a conditional $`\mathsf{if}\ C\ \mathsf{then}\ M\ \mathsf{else}\ N : B`$ for $`C, M, N : B`$; there is no fixed-point operator. Every closed term of type $`B`$ has a normal form $`\mathsf{tt}`$, $`\mathsf{ff}`$ or $`\bot`$, its *observed value*. Closed terms $`M, N : \tau`$ are *observationally equivalent*, $`M \simeq N`$, when $`K\,M`$ and $`K\,N`$ have the same observed value for every closed $`K : \tau \to B`$.

**Loader's theorem** (*Finitary PCF is not decidable*, TCS 266, 2001): $`\simeq`$ is undecidable.

**Sieber's relations.** Let $`V = \{\bot, \mathsf{tt}, \mathsf{ff}\}`$, ordered flatly. For a finite set $`w`$ and $`A \subseteq B \subseteq w`$,

```math
S^w_{A,B} = \{\, g \in V^w \mid (\exists i \in A.\ g_i = \bot) \ \lor\ g \text{ is constant on } B \,\}.
```

A *test* of arity $`w`$ is a finite intersection $`R`$ of such relations.

**Sieber's model.** By induction on types we define a finite poset $`D_\tau`$ and, for every test $`R`$ of arity $`w`$, a relation $`R_\tau \subseteq D_\tau^{\,w}`$:

```math
D_B = V, \qquad R_B = R,
```

```math
R_{\sigma\to\rho} = \{\, F \in D_{\sigma\to\rho}^{\,w} \mid \forall G \in R_\sigma.\ (F_i(G_i))_{i \in w} \in R_\rho \,\},
```

```math
D_{\sigma\to\rho} = \{\, f : D_\sigma \to D_\rho \mid f \text{ monotone and } (f, \dots, f) \in R_{\sigma\to\rho} \text{ for every test } R \,\}.
```

$`D_{\sigma\to\rho}`$ is ordered pointwise. The carriers are built from the carriers already constructed, not from the full function spaces.

A term $`\Gamma \vdash M : \tau`$ denotes a function $`⟦M⟧ : D_\Gamma \to D_\tau`$, defined as usual (the conditional is strict in its test). An element $`f \in D_\tau`$ is *definable* when $`f = ⟦M⟧`$ for a closed term $`M`$. The model is *universal* when every element of every $`D_\tau`$ is definable.

**Theorem.** If Loader's theorem holds, Sieber's model of finitary PCF is not universal: some $`D_\tau`$ contains an element that is not the denotation of any closed term.

## 2. Lemmas

**Lemma 1 (soundness).** For every term $`\Gamma \vdash M : \tau`$, the function $`⟦M⟧`$ is monotone and maps related tuples of environments to related tuples. In particular $`⟦M⟧ \in D_\tau`$ for closed $`M`$.

*Proof.* Induction on $`M`$, proving monotonicity and preservation together. Constant tuples lie in every $`S^w_{A,B}`$ (they are constant on $`B`$), and then in every $`R_\tau`$ (at $`\sigma \to \rho`$, the constant tuple of $`f \in D_{\sigma\to\rho}`$ is related by definition of the carrier). So constants and variables are handled, and abstraction and application follow from the definition of $`R_{\sigma\to\rho}`$; the constant-tuple property also shows that an abstraction lands in the carrier. For the conditional it suffices that each $`S^w_{A,B}`$ is closed under the strict conditional: let $`c, a, b \in S^w_{A,B}`$. If $`c_i = \bot`$ for some $`i \in A`$, the result is $`\bot`$ at $`i`$. Otherwise $`c`$ is constant on $`B`$, with value $`v`$ say. If $`v = \bot`$ the result is $`\bot`$ on all of $`B`$, hence constant there; if $`v = \mathsf{tt}`$ the result agrees with $`a`$ on $`B`$, and $`a`$ is either $`\bot`$ at some $`i \in A \subseteq B`$ or constant on $`B`$; similarly for $`\mathsf{ff}`$ and $`b`$. $`\square`$

**Lemma 2 (adequacy).** For a closed term $`M : B`$, $`⟦M⟧`$ is its observed value.

*Proof.* A logical relation between $`D_\tau`$ and the full set-theoretic type hierarchy over $`V`$ (equality at $`B`$) is preserved by every term constructor. In the full hierarchy β-reduction is sound and the normal forms $`\mathsf{tt}, \mathsf{ff}, \bot`$ denote themselves. $`\square`$

**Lemma 3 (finiteness).** Every $`D_\tau`$ is finite, since it is a set of functions between finite sets.

**Lemma 4 (full abstraction from universality).** If the model is universal, then for closed $`M, N : \tau`$, $`M \simeq N`$ if and only if $`⟦M⟧ = ⟦N⟧`$.

*Proof.* If $`⟦M⟧ = ⟦N⟧`$ then $`⟦K\,M⟧ = ⟦K⟧(⟦M⟧) = ⟦K⟧(⟦N⟧) = ⟦K\,N⟧`$ for every $`K`$, so $`M \simeq N`$ by Lemma 2; this direction does not need universality. Conversely, distinct $`x \ne y \in D_\tau`$ are separated by some $`t \in D_{\tau \to B}`$ with $`t(x) \ne t(y)`$: at $`B`$ take the identity; at $`\sigma \to \rho`$ pick $`a`$ with $`x(a) \ne y(a)`$, a separator $`t'`$ for $`x(a), y(a)`$, and set $`t(f) = t'(f(a))`$. This $`t`$ is monotone, and preserves every test because the constant tuple of $`a`$ is related. By universality $`t = ⟦K⟧`$, and then $`⟦K\,M⟧ \ne ⟦K\,N⟧`$, so $`M \not\simeq N`$ by Lemma 2. $`\square`$

**Lemma 5 (normal forms).** Every term has a β-normal, η-long form with the same denotation. In a closed normal form of type $`\tau = \sigma \to \rho`$, every subterm, bound variable and argument has a type that is a subformula of $`\sigma`$ or of $`\rho`$, hence a proper subtype of $`\tau`$.

*Proof.* Normal forms exist by normalisation for the simply typed λ-calculus (the conditional is a first-order constant). β preserves denotations by the substitution lemma, and η by extensionality of $`D`$. The subformula property is proved by induction on normal forms: a neutral term $`x\,N_1 \cdots N_k`$ has the type of a suffix of the type of $`x`$, and its arguments have subformulas of that type. $`\square`$

**Lemma 6 (effectiveness).** If the model is universal, the finite structures $`D_\tau`$, with their order and application tables, are computable from $`\tau`$.

*Proof.* Induction on $`\tau`$; $`D_B = V`$ is given. Let $`\tau = \sigma \to \rho`$, with $`D_\sigma`$ and $`D_\rho`$ already computed. Every element of $`D_\tau`$ is one of the finitely many monotone maps $`D_\sigma \to D_\rho`$, the *candidates*, which can be listed. Run two searches in parallel.

- *Rejection.* Enumerate pairs $`(w, R)`$ of an arity and a test; for each fixed $`w`$ there are finitely many tests. For each, compute the relations $`R_\sigma`$ and $`R_\rho`$ from the known carriers (by the recursive definition, each is a finite set of tuples) and reject every candidate $`f`$ with $`(f, \dots, f) \notin R_\tau`$. By definition of $`D_\tau`$, a rejected candidate is not in $`D_\tau`$. Conversely, a candidate outside $`D_\tau`$ fails some particular test, so it is eventually rejected. No bound on the arity is needed.
- *Acceptance.* Enumerate the closed normal forms of type $`\tau`$ and compute their denotations. By Lemma 5 only the carriers of proper subtypes of $`\tau`$ are needed, and they are known. Accept each candidate so obtained. By Lemma 1 an accepted candidate is in $`D_\tau`$. Conversely, by universality and Lemma 5 every element of $`D_\tau`$ is the denotation of a closed normal form, so it is eventually accepted.

Every candidate is eventually either accepted or rejected, and never both. Since there are finitely many candidates, the procedure terminates, and $`D_\tau`$ is the set of accepted candidates. $`\square`$

## 3. Proof of the theorem

Suppose the model is universal. Given closed $`M, N : \tau`$, compute by Lemma 6 the carriers of all types occurring in $`M`$ and $`N`$. Then compute $`⟦M⟧`$ and $`⟦N⟧`$ by evaluating the terms on these finite tables, and compare them. By Lemma 4 this decides $`M \simeq N`$, contradicting Loader's theorem. Hence some $`D_\tau`$ has a non-definable element. $`\square`$

**Corollary.** That element $`f`$ preserves every sequentiality relation of every arity. Since $`D_\tau`$ is finite, a directed set of definable elements has a greatest element, so $`f`$ is not a supremum of definable elements either.

**What this does not show.** It does not show that Sieber's model fails full abstraction for finitary PCF. Only the direction "universal ⇒ fully abstract" (Lemma 4) is proved; non-definable elements could be semantic junk that no program distinguishes.

**Why the argument uses finiteness of the tests but not a bound on their arity.** Relatedness of a tuple for one fixed test is a finite computation, so non-membership is semi-decidable even though there are tests of every arity. Universality makes membership semi-decidable too, and finiteness of the candidate set turns the two semi-decisions into a decision.

## 4. Towards the open problem: detailed transfer proof

This section records the mathematical proof to formalise next. **Model distinction:** let (D^B) be the ordinary single-world Sieber model over (B_⊥={⊥,0,1}), and let (D^N) be the ordinary single-world Sieber model over (ℕ_⊥), defined by the same induction. The existing `OR.D` is the O'Hearn--Riecke **Kripke** model, not (D^N). Do not use it as the definition of the natural Sieber model. Its projection proofs may be copied/reused only after establishing the corresponding facts for (D^N).

Translate types by `hat(B)=nat` and `hat(σ→τ)=hat(σ)→hat(τ)`. Let (ψ^1) be the usual PCF level-1 projection:
```math
ψ^1_B(⊥)=⊥,\quad ψ^1_B(0)=0,\quad ψ^1_B(1)=1,\quad ψ^1_B(n)=⊥\ (n≥2),
```
```math
ψ^1_{σ→τ}(f)(x)=ψ^1_τ(f(ψ^1_σ x)).
```
Write (L_τ={x∈D^N_τ\mid ψ^1_τx=x}). The central theorem is
```math
D^B_τ \cong L_{\widehat τ}.
```

### 4.1 Ground relation lemma

For a test (R), an intersection of elementary (S^w_{A,C}), define
(j:B_⊥→ℕ_⊥) by (⊥↦⊥,0↦0,1↦1), and define (q:ℕ_⊥→B_⊥) by fixing
(⊥,0,1) and sending every (n≥2) to (⊥). Thus (qj=id) and (jq=ψ^1_B).

**Lemma 7.** For every Boolean tuple (g:w→B_⊥),
```math
R^B(g) \iff R^N(j\circ g).                       \tag{7a}
```
For every natural tuple (h:w→ℕ_⊥),
```math
R^N(h) \Longrightarrow R^B(q\circ h).             \tag{7b}
```

*Proof.* Work componentwise on (S^w_{A,C}). For (7a), (j) is injective and reflects bottom, so it preserves and reflects both alternatives: bottom at some coordinate in (A), or constancy on (C). For (7b), (q) is strict, so a bottom witness remains bottom; and every function preserves equality, so constancy remains constancy. Intersections preserve the statements. The converse of (7b) for arbitrary natural tuples is not needed. ∎

### 4.2 Simultaneous transfer lemma

Define, by induction on Boolean types,
```math
i_B=j,\qquad r_B=q,
```
and
```math
i_{σ→τ}(f)(x)=i_τ(f(r_σx)),                         \tag{8}
```
```math
r_{σ→τ}(F)(a)=r_τ(F(i_σa)).                         \tag{9}
```

**Lemma 8 (transfer).** Simultaneously for every (τ):

1. (i_τ:D^B_τ→D^N_{\widehat τ}) and (r_τ:D^N_{\widehat τ}→D^B_τ) are well-defined.
2. They are monotone.
3. For every test (R) and Boolean tuple (g:w→D^B_τ),
   ```math
   R^B_τ(g) \iff R^N_{\widehat τ}(i_τ\circ g).     \tag{10}
   ```
4. For every test (R) and natural tuple (h:w→D^N_{\widehat τ}),
   ```math
   R^N_{\widehat τ}(h) \Longrightarrow R^B_τ(r_τ\circ h). \tag{11}
   ```
5. (r_τi_τ=id).
6. (i_τr_τ=ψ^1_{\widehat τ}).

*Proof.* The ground case is Lemma 7 plus (qj=id), (jq=ψ^1_B).

Let (τ=σ→ρ). For the forward implication of (10), suppose (f:w→D^B_{σ→ρ}) is Boolean-related and (x:w→D^N_{\widehat σ}) is natural-related. By induction (11), (r_σ∘x) is Boolean-related. Apply the Boolean arrow relation to get
```math
R^B_ρ\bigl(f_k(r_σx_k)\bigr)_k.
```
By induction (10) at (ρ),
```math
R^N_{\widehatρ}\bigl(i_ρ(f_k(r_σx_k))\bigr)_k,
```
which is exactly the required result by (8).

Conversely suppose (i_{σ→ρ}∘f) is natural-related and let (a:w→D^B_σ) be Boolean-related. By induction (10), (i_σ∘a) is natural-related. Applying the natural arrow relation gives
```math
R^N_{\widehatρ}\bigl(i_ρ(f_k(r_σ(i_σa_k)))\bigr)_k.
```
Use (r_σi_σ=id), then induction (10) backwards at (ρ), to obtain
(R^B_ρ(f_k(a_k))_k). This proves (10).

For (11), suppose (F:w→D^N_{\widehatσ→\widehatρ}) is natural-related and (a:w→D^B_σ) is Boolean-related. By (10) at (σ), (i_σ∘a) is natural-related. Hence
```math
R^N_{\widehatρ}\bigl(F_k(i_σa_k)\bigr)_k.
```
Apply induction (11) at (ρ). By (9) the result is exactly
(R^B_ρ(r_{σ→ρ}(F_k)(a_k))_k).

These calculations applied to constant tuples prove that (8) and (9) preserve every test, hence really land in the restricted arrow carriers. Monotonicity follows from the induction hypotheses and monotonicity of the transported functions.

For the first inverse law,
```math
r_{σ→ρ}(i_{σ→ρ}f)(a)
 =r_ρ(i_ρ(f(r_σ(i_σa))))=f(a).
```
For the second,
```math
i_{σ→ρ}(r_{σ→ρ}F)(x)
 =i_ρr_ρ(F(i_σr_σx))
 =ψ^1_ρ(F(ψ^1_σx))
 =ψ^1_{σ→ρ}(F)(x).
```
Thus all six assertions hold. ∎

**Formalisation warning.** Prove (10), (11), well-definedness and the inverse equations in one mutual/type induction. Defining carrier-valued (i,r) before relation preservation is available is otherwise circular.

### 4.3 Level-one isomorphism

**Lemma 9.**
```math
D^B_τ \cong L_{\widehatτ}
```
as ordered sets, with maps (i_τ,r_τ).

*Proof.* For (a∈D^B_τ),
```math
ψ^1(i_τa)=i_τr_τi_τa=i_τa.
```
If (x∈L_{\widehatτ}), then
```math
i_τ(r_τx)=ψ^1x=x.
```
The other inverse law is Lemma 8(5), and both maps are monotone by Lemma 8(2). ∎

### 4.4 Compactness

Assume the ordinary natural Sieber carriers have directed suprema, the projections are continuous, and (ψ^1≤id), as in the standard construction.

**Lemma 10.** Every (x∈L_{\widehatτ}) is compact.

*Proof.* Let (E) be directed and (x≤⊔E). Then
```math
x=ψ^1x≤ψ^1(⊔E)=⊔_{e∈E}ψ^1e.
```
The set (ψ^1(E)) is directed and lies in (L_{\widehatτ}), which is finite by Lemma 9 and finiteness of (D^B_τ). A directed subset of a finite poset has a greatest element, say (ψ^1e_0). Therefore
```math
x≤ψ^1e_0≤e_0.
```
Hence (x) is compact. ∎

### 4.5 From hypothetical full abstraction to a grade-1 term

Assume for contradiction that the ordinary natural Sieber model (D^N) is inequationally fully abstract.

Use the Milner--Plotkin compact-definability characterization: for an order-extensional PCF model satisfying the standard domain hypotheses, full abstraction implies that every compact element is definable. This is an **external theorem**; in Lean its hypotheses should be made explicit.

Take arbitrary (h∈D^B_τ). By Lemmas 9--10, (i_τh) is compact, so there is a closed PCF term (M:\widehatτ) with
```math
⟦M⟧_N=i_τh.                                         \tag{12}
```
Since (i_τh) is fixed by (ψ^1), and the PCF term (Ψ^1) denotes (ψ^1),
```math
⟦Ψ^1M⟧_N=⟦M⟧_N.
```
Full abstraction gives
```math
Ψ^1M\simeq M.                                       \tag{13}
```
Thus (M) is a finite term of grade 1 in Müller's terminology.

### 4.6 Grade-1 game-term reinterpretation

Use Müller's Game Term Theorem: every finite term of grade (i) is observationally equivalent to a game term of grade (i). From (13) obtain a grade-1 game term (G:\widehatτ) with
```math
G\simeq M.                                          \tag{14}
```
Full abstraction and (12) imply
```math
⟦G⟧_N=i_τh.                                         \tag{15}
```

A grade-1 game term contains only bottom, numerals (0,1), variables, abstraction/application, and the strict finite operation
```math
case_1(z;N_0,N_1),
```
which returns (N_0) on (0), (N_1) on (1), and bottom otherwise.

Define a Boolean translation (G^B) structurally: (⊥↦⊥), (0↦tt), (1↦ff); preserve variables, lambda and application; translate (case_1(z;N_0,N_1)) to the strict Boolean conditional on (z^B).

**Lemma 11 (reinterpretation).** For every grade-1 game term (G) of translated type and Boolean environment (ρ),
```math
⟦G⟧_N(iρ)=i_τ(⟦G^B⟧_B(ρ)).                         \tag{16}
```

*Proof.* Structural induction on (G).

Constants and variables are immediate. Lambda is pointwise the induction hypothesis.

For application (PQ), write the function type as (σ→τ). By induction,
```math
⟦P⟧_N(iρ)=i_{σ→τ}(⟦P^B⟧_Bρ),\qquad
⟦Q⟧_N(iρ)=i_σ(⟦Q^B⟧_Bρ).
```
Then by (8) and (r_σi_σ=id),
```math
i_{σ→τ}(f)(i_σa)
 =i_τ(f(r_σ(i_σa)))
 =i_τ(f(a)),
```
which is exactly (16) for application.

For (case_1), the induction hypothesis says that the natural scrutinee is in the image of (i_B), hence is exactly (⊥,0), or (1). On these three values natural (case_1) agrees respectively with strict Boolean conditional on (⊥,tt,ff). Apply the induction hypotheses to the selected branch. ∎

For closed (G), (16) and (15) give
```math
i_τ(⟦G^B⟧_B)=⟦G⟧_N=i_τh.
```
Apply (r_τ) and use (r_τi_τ=id):
```math
⟦G^B⟧_B=h.
```
Since (h) was arbitrary, every element of every Boolean carrier is definable. Thus (D^B) is universal, contradicting `sieber_not_universal`.

### 4.7 Conditional conclusion

Subject only to the two cited external results in the precise forms used above (Milner--Plotkin compact definability and Müller's grade-1 Game Term Theorem), the preceding lemmas prove:
```math
\boxed{\text{the ordinary Sieber model over }ℕ_⊥\text{ is not fully abstract for PCF}.}
```

The internal proof obligations are Lemmas 7--11. Lemmas 7--9 and 11 are elementary inductions; Lemma 10 is the finite-image compactness argument. The Lean agent should formalise these arguments rather than search for alternative proofs.


## 5. Remarks

**Why this does not apply to the Kripke construction.** Each Kripke world is finite, but there are infinitely many worlds (all finite typed contexts), and the arrow clause quantifies over every extension of the current world. Checking that a higher-type tuple is related is then no longer a finite computation, so the rejection search of Lemma 6 is not available. The same holds for preorder-shaped worlds.

**Unary PCF is different.** Over the one-point ground type $`\{\bot, \top\}`$ the answer is positive at all types: Laird (*Sequentiality in bounded biorders*, 2005, Theorem 3.11) shows that every standard order-extensional model of unary PCF excluding parallel composition is universal, and a single ternary test excludes it.

## 6. The Lean formalisation

```lean
def SieberNotUniversal : Prop :=
  Loader → ∃ (τ : Ty) (f : SieberBool τ), ¬ Definable f

theorem sieber_not_universal : SieberNotUniversal
```

`Loader` states Loader's theorem as `¬ ComputablePred` of observational equivalence on pairs of term codes. The proof has no `sorry` and depends only on `propext`, `Classical.choice` and `Quot.sound`. Sections 1–3 are formalised; section 4 is not. The formal result is non-universality; the Lean development proves `universal_fully_abstract` (universality implies full abstraction) and nothing in the converse direction.

The parallel search of Lemma 6 is realised by *certificates*. A certificate lists the carriers as tables, a normal form for each element, the values of all subterms in all environments, and, for each rejected candidate, a failing test with its lifted relations. A checker verifies a certificate by local consistency checks only, so it is primitive recursive by composition. Universality is used only to show that certificates exist. Observational equivalence and its negation are then both recursively enumerable, hence computable (Post's theorem).

| Lean | Content |
|---|---|
| `Syntax.lean` | Finitary PCF; `Tm.code`, and `Tm.code_inj`: a code determines its typed term. |
| `Standard.lean` | The full model, `ObsEquiv`, and the statement of `Loader`. |
| `Model.lean` | Sieber's model `SieberBool`; interpretation of terms with Lemma 1 built in; `Definable`, `Universal`. |
| `Soundness.lean` | Lemmas 2–4: `Tm.obs_eq_den`, `finite_car`, `universal_fully_abstract`. |
| `Normal.lean` | Lemma 5: normalisation by evaluation, `Tm.nf_sound`. |
| `Check.lean` | The certificate checker. |
| `CheckSound.lean` | A valid certificate describes the model exactly on the types it covers (`good_all`); its verdict is equality of denotations (`verdict_sound`). |
| `CheckComplete.lean` | Under universality every pair of closed terms has a certificate (`complete`); uses the subformula property of Lemma 5. |
| `TypeCheck.lean` | Certificates for pairs of codes that are not two closed terms of the same type. |
| `PrimrecLib.lean`, `CheckPrim.lean` | Both checkers are primitive recursive. |
| `Main.lean` | Post's theorem and the proof of the theorem: `sieber_not_universal`. |
