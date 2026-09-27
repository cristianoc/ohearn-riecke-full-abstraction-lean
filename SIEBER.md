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

## 4. Towards the open problem: a proposed transfer (not formalised)

This section outlines how the theorem could give a negative answer to O'Hearn and Riecke's question for ordinary PCF over $`\mathbb N_\bot`$. The steps are:

```math
\text{FA over } \mathbb N_\bot \;\Rightarrow\; \text{compact elements definable} \;\Rightarrow\; \text{Boolean universality} \;\Rightarrow\; \bot .
```

Write $`D^B`$ and $`D^N`$ for Sieber's construction over $`\{\bot, 0, 1\}`$ (standing for $`\bot, \mathsf{tt}, \mathsf{ff}`$) and over $`\mathbb N_\bot`$.

- *A retraction at every type.* Include $`\{\bot, 0, 1\}`$ into $`\mathbb N_\bot`$, and retract by sending values $`\ge 2`$ to $`\bot`$. Both maps are strict, so they preserve the tests with the same description $`(w, A, B)`$ on both sides. Extending them covariantly and contravariantly gives $`i_\tau : D^B_\tau \to D^N_\tau`$ and $`r_\tau`$ with $`r_\tau i_\tau = \mathrm{id}`$. The idempotent $`i_\tau r_\tau`$ is the level-1 projection $`\psi^1_\tau`$, whose image consists of compact elements.
- *Full abstraction would give Boolean definability.* If $`D^N`$ were fully abstract, every compact element would be definable (Milner). A term $`M`$ defining $`i_\tau(h)`$ is equivalent to a finite game term of grade 1 (Müller's game-term theorem), which observes only the values $`0`$ and $`1`$, through strict two-case tests. Reinterpreting it over the booleans defines $`h`$. So every element of $`D^B`$ would be definable, contradicting the theorem.

**Proposed corollary.** Sieber's model over $`\mathbb N_\bot`$ is not fully abstract for PCF.

This is not yet established. The remaining obligations are:

1. **Milner's compact definability.** Check that Milner's theorem applies to Sieber's model over $`\mathbb N_\bot`$ as constructed here (order-extensional, with the projections $`\psi^n`$), so that full abstraction implies that every compact element is definable.
2. **Müller's game-term theorem.** Check the exact grade-1 form: that a term fixed by $`\Psi^1`$ is contextually equivalent to a finite game term that observes ground values only through strict two-case tests on $`0`$ and $`1`$.
3. **The reinterpretation.** Prove that such game terms, read over the booleans, define the retracted element $`r_\tau(⟦M⟧)`$. This is an induction on game terms using $`r_\tau i_\tau = \mathrm{id}`$.

The finitary theorem of Sections 1–3 does not depend on any of these.

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
