# Sieber's ordinary relations fail inequational full abstraction

O'Hearn and Riecke (*Kripke logical relations and PCF*, Inf. & Comp. 120(1), 1995) obtain a fully abstract model of PCF with *Kripke* logical relations. Their §5 (Conclusion, printed p. 14) states: "One crucial question remains: is the model based on Kripke relations actually different than Sieber's finitary relation model?", and asks "whether the simpler fixed-arity relations of Sieber suffice for full abstraction." This note proves two results about that question.

- **Theorem A** (Sections 1–3). For finitary PCF over the Booleans, assuming Loader's theorem, Sieber's model is **not universal**: some element is not the denotation of any closed term. This alone does not answer the question: a model with non-definable elements can still be fully abstract.
- **Theorem B** (Section 4). For PCF over the natural numbers, assume Loader's theorem, Milner's compact-definability theorem (1977) and Müller's Game Term Theorem (2012). Then Sieber's model $`D^N`$ is **not inequationally fully abstract**: the denotational order and the contextual preorder differ on some pair of closed terms. This answers the question for the inequational notion that O'Hearn and Riecke's own theorem uses, and for the direct presentation of the model. §4.7 gives a sharper equational statement under further cited hypotheses, and §4.8 lists what remains open.

Both are formalised in Lean (`OR/Sieber/`, Section 6), with the cited theorems as hypotheses in the forms stated there. For Theorem B the hypotheses are Lean statements of Loader's theorem, of Milner's theorem instantiated at $`D^N`$, and of Müller's theorem at grade 1; the premises of Milner's theorem are proved for $`D^N`$. Section 6 states each hypothesis exactly and names the steps that connect it to the published result outside Lean.

Both arguments are nonconstructive: they show that a non-definable element exists, but do not exhibit one.

**Relation to the literature.** Theorems A and B are short combinations of published ingredients. O'Hearn and Riecke remark (printed p. 15) that "if, for instance, Sieber's more tame relations determined the fully abstract model, there would be an effective presentation", and they call Loader's full-type-hierarchy result "apparently not immediately relevant to the PCF definability problem". Curien (*Definability and full abstraction*, ENTCS 172, 2007, §2) states the general principle that Loader's result rules out a direct, unquotiented construction of the fully abstract model, since such a construction would give an effective presentation; he does not apply it to Sieber's model. Theorem A combines that remark with Loader's undecidability theorem for finitary PCF (TCS 266, 2001); Theorem B adds Milner's compact-definability theorem (1977) and Müller's Game Term Theorem (2012). This note makes the combination explicit (Lemma 6 and Section 3 for Theorem A, Section 4 for Theorem B) and checks it in Lean under the hypotheses of Section 6.

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

**Theorem A.** If Loader's theorem holds, Sieber's model of finitary PCF is not universal: some $`D_\tau`$ contains an element that is not the denotation of any closed term.

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

Lemma 6 and Section 3 make explicit, for Sieber's model, the principle in O'Hearn and Riecke's p. 15 remark and in Curien (2007, §2) quoted in the introduction: if a model given by a direct construction of this kind is universal, it has an effective presentation, and Loader's theorem excludes one.

**Lemma 6 (effectiveness).** If the model is universal, the finite structures $`D_\tau`$, with their order and application tables, are computable from $`\tau`$.

*Proof.* Induction on $`\tau`$; $`D_B = V`$ is given. Let $`\tau = \sigma \to \rho`$, with $`D_\sigma`$ and $`D_\rho`$ already computed. Every element of $`D_\tau`$ is one of the finitely many monotone maps $`D_\sigma \to D_\rho`$, the *candidates*, which can be listed. Run two searches in parallel.

- *Rejection.* Enumerate pairs $`(w, R)`$ of an arity and a test; for each fixed $`w`$ there are finitely many tests. For each, compute the relations $`R_\sigma`$ and $`R_\rho`$ from the known carriers (by the recursive definition, each is a finite set of tuples) and reject every candidate $`f`$ with $`(f, \dots, f) \notin R_\tau`$. By definition of $`D_\tau`$, a rejected candidate is not in $`D_\tau`$. Conversely, a candidate outside $`D_\tau`$ fails some particular test, so it is eventually rejected. No bound on the arity is needed.
- *Acceptance.* Enumerate the closed normal forms of type $`\tau`$ and compute their denotations. By Lemma 5 only the carriers of proper subtypes of $`\tau`$ are needed, and they are known. Accept each candidate so obtained. By Lemma 1 an accepted candidate is in $`D_\tau`$. Conversely, by universality and Lemma 5 every element of $`D_\tau`$ is the denotation of a closed normal form, so it is eventually accepted.

Every candidate is eventually either accepted or rejected, and never both. Since there are finitely many candidates, the procedure terminates, and $`D_\tau`$ is the set of accepted candidates. $`\square`$

## 3. Proof of the theorem

Suppose the model is universal. Given closed $`M, N : \tau`$, compute by Lemma 6 the carriers of all types occurring in $`M`$ and $`N`$. Then compute $`⟦M⟧`$ and $`⟦N⟧`$ by evaluating the terms on these finite tables, and compare them. By Lemma 4 this decides $`M \simeq N`$, contradicting Loader's theorem. Hence some $`D_\tau`$ has a non-definable element. $`\square`$

**Corollary.** That element $`f`$ preserves every sequentiality relation of every arity. Since $`D_\tau`$ is finite, a directed set of definable elements has a greatest element, so $`f`$ is not a supremum of definable elements either.

**What this does not show.** It does not show that this finitary model fails full abstraction. Only the direction "universal ⇒ fully abstract" (Lemma 4) is proved; non-definable elements could be semantic junk that no program distinguishes. Section 4 closes this gap for the model over the natural numbers.

**Why the argument uses finiteness of the tests but not a bound on their arity.** Relatedness of a tuple for one fixed test is a finite computation, so non-membership is semi-decidable even though there are tests of every arity. Universality makes membership semi-decidable too, and finiteness of the candidate set turns the two semi-decisions into a decision.

## 4. The model over the natural numbers is not inequationally fully abstract

### 4.1 Setting and statement

**PCF.** Types are $`\hat\tau ::= \mathsf{nat} \mid \hat\sigma \to \hat\tau`$. The constants are $`0`$, $`\mathsf{succ}`$, $`\mathsf{pred}`$ (with $`\mathsf{pred}\,0`$ divergent), $`\mathsf{ifz}`$ and $`\mathsf{fix}`$, as in O'Hearn and Riecke (and as in the rest of this repository). For closed terms, $`M \sqsubseteq N`$ holds when for every closed context $`C`$ of type $`\mathsf{nat}`$, $`C[M]`$ reduces to a numeral $`n`$ only if $`C[N]`$ does. Write $`M \simeq N`$ when $`M \sqsubseteq N`$ and $`N \sqsubseteq M`$.

**The model $`D^N`$.** Take the definition of Section 1 with $`V`$ replaced by the flat domain $`ℕ_⊥`$, $`S^w_{A,B} \subseteq ℕ_⊥^{\,w}`$ defined by the same formula, and "monotone" replaced by "continuous". So $`D^N_{\mathsf{nat}} = ℕ_⊥`$, and $`D^N_{\hat\sigma\to\hat\tau}`$ is the set of continuous maps $`D^N_{\hat\sigma} \to D^N_{\hat\tau}`$ whose constant tuples lie in every lifted test, ordered pointwise. Constants have their standard meaning and $`\mathsf{fix}`$ denotes the least fixed point.

This is O'Hearn and Riecke's construction with their Kripke relations replaced by Sieber's fixed-arity relations, which is the comparison their question asks about. Their §2 also describes Sieber's model as the invariant elements of the continuous type hierarchy, followed by an extensional collapse. We do not prove that this presentation gives the same model; the result below is about $`D^N`$ as defined here.

**Full abstraction.** $`D^N`$ is *inequationally fully abstract* when for all closed $`M, N`$
```math
M \sqsubseteq N \iff ⟦M⟧ \le ⟦N⟧.
```
Full abstraction for open terms implies this, so failing it for closed terms is the stronger conclusion.

**Theorem B.** Assume Loader's theorem and the two published results (MP) and (GT) below. Then $`D^N`$ is not inequationally fully abstract.

**(MP) Milner's compact-definability theorem** (R. Milner, *Fully abstract models of typed λ-calculi*, TCS 4, 1977). In an order-extensional, ω-algebraic model of PCF in which $`\mathsf{fix}`$ denotes least fixed points, inequational full abstraction implies that every compact element is definable. Lemma P below shows that $`D^N`$ meets these premises. Constants are interpreted standardly and application is continuous, by construction. Curien (*Definability and full abstraction*, ENTCS 172, 2007) states Milner's result in this form: a fully abstract model of PCF on algebraic cpos must be order-extensional and have all compact elements definable.

**(GT) Müller's Game Term Theorem** (F. Müller, *On Berry's conjectures about the stable order in PCF*, LMCS 8(4), 2012, Theorem 4.12, taking $`M = N`$ and $`i = j`$). A *finite term of grade* $`i`$ is a closed term with $`M \simeq Ψ^i M`$ (Definition 3.1). Every such term is observationally equivalent to a *game term of grade* $`i`$ (Definition 4.1). At grade 1, his projection is
```math
Ψ_1^{\mathsf{nat}} = λx.\,\mathsf{if}\ x\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{if}\ \mathsf{pre}\ x\ \mathsf{then}\ 1\ \mathsf{else}\ ⊥,
\qquad
Ψ_1^{\sigma\to\tau} = λf.\,λx.\,Ψ_1^\tau(f(Ψ_1^\sigma x)).
```

A game term of grade 1 is generated by
```math
G ::= ⊥ \mid λ\vec x.\,m\ (m \in \{0,1\}) \mid λ\vec x.\,\mathsf{case}_1(y\,\vec M;\,N_0,\,N_1),
```
where $`\mathsf{case}_1(z; N_0, N_1)`$ is Müller's macro $`\mathsf{if}\ z\ \mathsf{then}\ N_0\ \mathsf{else}\ \mathsf{if}\ \mathsf{pre}\ z\ \mathsf{then}\ N_1\ \mathsf{else}\ ⊥`$. It returns $`N_0`$ on $`0`$, $`N_1`$ on $`1`$, and diverges otherwise. Here $`\vec M`$ are again game terms of grade 1.

**How (GT) enters Lean.** `GameTerms.lean` transcribes these definitions into the repository's PCF:
- Müller's $`\mathsf{pre}`$, $`\mathsf{if}`$, $`\mathsf{Y}`$, numerals and $`⊥^\sigma`$ are read as $`\mathsf{pred}`$, $`\mathsf{ifz}`$, $`\mathsf{fix}`$, $`\mathsf{succ}^n 0`$ and $`Ω_\sigma = \mathsf{fix}(λx.x)`$;
- `MullerPsi` is $`Ψ_1`$ verbatim;
- `Game` is the grammar above.

The hypothesis `MullerGameTermTheorem` is Theorem 4.12 at grade 1 in this reading. Two steps that could hide a mismatch are proved in Lean from the repository's Kripke full abstraction theorem:
- $`Ψ_1 M \simeq Ψ^1 M`$, where $`Ψ^1`$ is the repository's `projectionTerm` (`MullerPsi_equiv`);
- every game term is $`\simeq`$ to `embed` of its Boolean reading, including $`Ω_\sigma \simeq λ\vec x.Ω`$ (`Game.equiv_embed`).

What remains outside Lean is the reading itself: that $`\sqsubseteq`$ in Müller's PCF and in this one agree on terms translated as above. The languages have the same constants, including the divergent $`\mathsf{pred}\,0`$ (Müller has no rule for $`\mathsf{pre}\,0`$). The differences are that
- Müller's numerals and $`⊥^\sigma`$ are primitive, and are definable here;
- Müller observes numerals reached by unrestricted reduction, while this repository uses call-by-name head reduction.

The two observations agree by standardisation (unrestricted reduction reaches a numeral exactly when head reduction does); this is a standard fact, used here and not proved in this repository or in Lean.

### 4.2 Projections (Lemma P)

The PCF terms $`Ψ^n`$ denote
```math
ψ^n_{\mathsf{nat}}(k) = \begin{cases} k & k \le n \\ ⊥ & \text{otherwise,} \end{cases}
\qquad
ψ^n_{\hat\sigma\to\hat\tau}(f) = ψ^n_{\hat\tau} \circ f \circ ψ^n_{\hat\sigma}.
```

**Lemma P.**
1. $`ψ^n \le \mathrm{id}`$.
2. $`ψ^n ψ^n = ψ^n`$.
3. $`ψ^n \le ψ^m`$ for $`n \le m`$.
4. $`\bigsqcup_n ψ^n x = x`$.
5. The image of $`ψ^n`$ is finite.

Hence $`x`$ is compact iff $`ψ^n x = x`$ for some $`n`$. So $`D^N`$ is ω-algebraic: every element is the supremum of the chain $`(ψ^n x)_n`$ of compact elements, and there are countably many compact elements. It is order-extensional by definition.

*Proof.* Items 1–4 are by induction on types. For 4 at arrow types, use continuity of $`f`$ and the diagonal $`k = \max(m, n)`$:
```math
ψ^m(f(ψ^n x)) \le ψ^k(f(ψ^k x)).
```
For 5: an element $`f`$ of level $`n`$ at $`\hat\sigma\to\hat\tau`$ satisfies $`f(x) = f(ψ^n x)`$ and $`f(x) = ψ^n(f(x))`$. So it is determined by a map between the finite level-$`n`$ sets at $`\hat\sigma`$ and $`\hat\tau`$.

For compactness, let $`x = ψ^n x \le \bigsqcup E`$ with $`E`$ directed. The image $`ψ^n(E)`$ is directed and finite, so it contains its supremum $`ψ^n e_0`$. Then
```math
x = ψ^n x \le ψ^n\bigl(\textstyle\bigsqcup E\bigr) = \bigsqcup ψ^n(E) = ψ^n e_0 \le e_0.
```
Conversely, a compact $`x \le \bigsqcup_n ψ^n x`$ lies below some $`ψ^n x \le x`$. $`\square`$

### 4.3 Transfer between the two models

Write $`D^B`$ for Sieber's model of Section 1 and $`\widehat B = \mathsf{nat}`$. Let $`j : V \to ℕ_⊥`$ send $`⊥, \mathsf{tt}, \mathsf{ff}`$ to $`⊥, 0, 1`$, and let $`q : ℕ_⊥ \to V`$ send $`0, 1`$ to $`\mathsf{tt}, \mathsf{ff}`$ and everything else to $`⊥`$. Then $`q j = \mathrm{id}`$ and $`j q = ψ^1_{\mathsf{nat}}`$.

**Lemma 7.** For a test $`R`$ of arity $`w`$, a tuple $`g \in V^w`$ and a tuple $`h \in ℕ_⊥^{\,w}`$:
```math
R^B(g) \iff R^N(j \circ g), \qquad R^N(h) \implies R^B(q \circ h).
```

*Proof.* It suffices to consider one $`S^w_{A,B}`$. The map $`j`$ is injective and reflects $`⊥`$, so it preserves and reflects both "$`⊥`$ somewhere in $`A`$" and "constant on $`B`$". The map $`q`$ is strict and preserves equality. $`\square`$

Define $`i_\tau : D^B_\tau \to D^N_{\hat\tau}`$ and $`r_\tau : D^N_{\hat\tau} \to D^B_\tau`$ by $`i_B = j`$, $`r_B = q`$ and
```math
i_{\sigma\to\rho}(f) = i_\rho \circ f \circ r_\sigma, \qquad r_{\sigma\to\rho}(F) = r_\rho \circ F \circ i_\sigma.
```

**Lemma 8 (transfer).** For every $`\tau`$:
1. $`i_\tau`$ and $`r_\tau`$ are well defined (they land in the carriers) and monotone.
2. $`R^B_\tau(g) \iff R^N_{\hat\tau}(i_\tau \circ g)`$ and $`R^N_{\hat\tau}(h) \implies R^B_\tau(r_\tau \circ h)`$.
3. $`r_\tau i_\tau = \mathrm{id}`$ and $`i_\tau r_\tau = ψ^1_{\hat\tau}`$.
4. For every directed $`E \subseteq D^N_{\hat\tau}`$ there is $`e \in E`$ with $`r_\tau(\bigsqcup E) = r_\tau(e)`$.

*Proof.* The four items are proved together, by induction on $`\tau`$. The ground case is Lemma 7 together with $`\bigsqcup E \in E`$ in a flat domain. Let $`\tau = \sigma\to\rho`$.
- *Relations.* For the first half of 2, apply the inductive 2 at $`\sigma`$ (second half) and at $`\rho`$ (first half), and use $`r_\sigma i_\sigma = \mathrm{id}`$ for the converse direction. The second half of 2 is similar. Applied to constant tuples, 2 shows that $`i_{\sigma\to\rho}(f)`$ and $`r_{\sigma\to\rho}(F)`$ preserve every test.
- *Continuity.* $`i_{\sigma\to\rho}(f)`$ is continuous because, by 4 at $`\sigma`$, $`r_\sigma(\bigsqcup E) = r_\sigma(e)`$ for some $`e \in E`$.
- *Inverse laws.* These are the computations $`r_\rho(i_\rho(f(r_\sigma(i_\sigma a)))) = f(a)`$ and $`i_\rho(r_\rho(F(i_\sigma(r_\sigma x)))) = ψ^1(F(ψ^1 x))`$.
- *Item 4.* Since $`D^B_\sigma`$ is finite, 4 at $`\rho`$ gives, for each $`a`$, some $`F_a \in E`$ with $`r_\rho((\bigsqcup E)(i_\sigma a)) = r_\rho(F_a(i_\sigma a))`$. Let $`e \in E`$ be an upper bound of the finitely many $`F_a`$. Then $`r_{\sigma\to\rho}(e)`$ and $`r_{\sigma\to\rho}(\bigsqcup E)`$ agree, by monotonicity and antisymmetry. $`\square`$

**Lemma 9.** $`D^B_\tau \cong \{x \in D^N_{\hat\tau} \mid ψ^1 x = x\}`$ via $`i_\tau`$ and $`r_\tau`$. This follows from item 3.

**Lemma 10.** Every $`i_\tau h`$ is compact. This follows from $`ψ^1(i_\tau h) = i_\tau h`$ and Lemma P.

### 4.4 Reading game terms as Boolean terms

A grade-1 game term is, up to $`\simeq`$ (use $`Ω_\sigma \simeq λ\vec x.Ω`$), the image $`\widehat G`$ of a Boolean term $`G`$ under $`\mathsf{tt} \mapsto 0`$, $`\mathsf{ff} \mapsto 1`$, $`⊥ \mapsto ⊥`$ and $`\mathsf{if}\ C\ \mathsf{then}\ M\ \mathsf{else}\ N \mapsto \mathsf{case}_1(\widehat C; \widehat M, \widehat N)`$. Variables, abstraction and application are kept.

The naive statement $`⟦\widehat G⟧_N(i\rho) = i(⟦G⟧_B\rho)`$ is false at arrow types: $`⟦λx.x⟧_N = \mathrm{id}`$, but $`i(\mathrm{id}) = ψ^1`$. We use a logical relation instead:
```math
L_B(x, b) \iff q(x) = b,
\qquad
L_{\sigma\to\rho}(F, f) \iff \forall x\, a.\ L_\sigma(x, a) \implies L_\rho(F x, f a).
```

**Lemma 11.**
1. $`L_\tau(i_\tau a, a)`$, and $`L_\tau(x, b)`$ implies $`r_\tau x = b`$.
2. For environments related componentwise by $`L`$, $`L_\tau(⟦\widehat G⟧_N\eta,\ ⟦G⟧_B\rho)`$.

*Proof.* Part 1 is by induction on $`\tau`$. The ground case is $`q j = \mathrm{id}`$. At $`\sigma\to\rho`$: if $`L_\sigma(x, a)`$, then $`r_\sigma x = a`$, so $`i(f)(x) = i_\rho(f a)`$, which is related to $`f a`$. If $`L_{\sigma\to\rho}(F, f)`$, then from $`L_\sigma(i_\sigma a, a)`$ we get $`r(F)(a) = r_\rho(F(i_\sigma a)) = f a`$.

Part 2 is by induction on $`G`$. Variables, abstraction and application are immediate. For the constants, $`q(0) = \mathsf{tt}`$, $`q(1) = \mathsf{ff}`$ and $`q(⊥) = ⊥`$. For $`\mathsf{case}_1`$ with $`q(z) = c`$: if $`z = 0`$ then $`c = \mathsf{tt}`$ and both sides take the first branch; the case $`z = 1`$ is symmetric; otherwise the natural side is $`⊥`$ and $`c = ⊥`$. $`\square`$

### 4.5 Proof of Theorem B

Suppose $`D^N`$ is inequationally fully abstract. Let $`h \in D^B_\tau`$.
1. By Lemma 10 and (MP) there is a closed $`M`$ with $`⟦M⟧ = i_\tau h`$.
2. Since $`ψ^1(i_\tau h) = i_\tau h`$, we have $`⟦Ψ^1 M⟧ = ⟦M⟧`$, so $`Ψ^1 M \simeq M`$ by full abstraction.
3. By (GT) there is a Boolean term $`G`$ with $`\widehat G \simeq M`$, and full abstraction gives $`⟦\widehat G⟧ = i_\tau h`$.
4. By Lemma 11, $`L_\tau(i_\tau h, ⟦G⟧_B)`$, hence $`⟦G⟧_B = r_\tau(i_\tau h) = h`$.

So $`D^B`$ is universal, contradicting the theorem of Section 3. $`\square`$

### 4.6 Failure propagates to every higher type order

Failure of inequational full abstraction at one order implies failure at every higher order.

**Lemma 12 (retract transport).** Let $`M, N : τ`$ satisfy
```math
M \sqsubseteq N \qquad\text{but}\qquad ⟦M⟧ \not\le ⟦N⟧.
```
Suppose $`τ`$ is a PCF-definable retract of $`σ`$: there are closed terms
$`e : τ → σ`$ and $`d : σ → τ`$ such that $`d\,(e\,x) \simeq x`$ and, in the model,
```math
⟦d⟧\circ⟦e⟧=\mathrm{id}.
```
Then inequational full abstraction also fails at $`σ`$.

*Proof.* Contextual preorder is a precongruence, so $`e\,M \sqsubseteq e\,N`$. If
$`⟦eM⟧\le⟦eN⟧`$, monotonicity of
$`⟦d⟧`$ and the retraction equation would give
```math
⟦M⟧
=⟦d(eM)⟧
\le⟦d(eN)⟧
=⟦N⟧,
```
a contradiction. $`\square`$

There is a uniform order-raising retract. Put
```math
R(τ)=τ\to τ,\qquad
e_τ(x)=λz^τ.x,\qquad
d_τ(f)=f\,Ω_τ.
```
Then $`d_τ(e_τ x)=x`$ by β-reduction, both operationally and denotationally. With the
standard convention
```math
\mathrm{ord}(B)=\mathrm{ord}(\mathsf{nat})=0,\qquad
\mathrm{ord}(σ\to τ)=\max(\mathrm{ord}(σ)+1,\mathrm{ord}(τ)),
```
we have
```math
\mathrm{ord}(R(τ))=\mathrm{ord}(τ)+1.
```
Consequently, if failure occurs at a type of order $`k`$, then it occurs at a type of
**every exact order** $`n ≥ k`$, by iterating $`R`$.

Theorem B and Lemma 12 together give a least order $`k`$ at which inequational full
abstraction of $`D^N`$ fails, and failure at every exact order $`n ≥ k`$. The argument of
this section gives no bound on $`k`$ in either direction. §4.7 (Theorem C) argues that the
first failing order of equational full abstraction is at most 4, hence $`k ≤ 4`$, from
further cited results and a reading of Stoughton's proof, and that the equational first
failing order is exactly 4 under the additional hypothesis that Sieber's (1992) positive
result transfers to $`D^N`$. Its dependency audit (§4.7.5) lists each hypothesis.

### 4.7 Locating the first failing order — source-annotated argument

This section is a mathematical argument, not formalised in Lean.  It bounds the first
failing order of equational full abstraction of $`D^N`$ from above by 4 and, under an additional hypothesis on
Sieber's 1992 result, from below by 4.  Each step is labelled as proved here, cited, or a
reading of a published proof; §4.7.5 collects the dependencies.

Use the standard convention
```math
\mathrm{ord}(B)=\mathrm{ord}(\mathsf{nat})=0,\qquad
\mathrm{ord}(σ\to τ)=\max(\mathrm{ord}(σ)+1,\mathrm{ord}(τ)).
\tag{17}
```
This is also the convention used by Ong--Tzevelekos in *Functional Reachability*, so their
order bounds require no shift.

#### 4.7.1 Loader's obstruction is already at order 3

Loader's undecidability proof contains the following finite equation-solvability problem:
```math
X\,a^j_1\cdots a^j_n \simeq b^j\qquad(j=1,\ldots,m),
\tag{18}
```
where the $`a_i^j`$ are closed finitary-PCF terms and $`b^j\in\{\mathsf{tt},\mathsf{ff}\}`$.
Ong--Tzevelekos, *Functional Reachability* (LICS 2009), Lemma 6 / Corollary 7, use exactly
this system and state explicitly:

> “Solvability of the system of equations (1) is undecidable at order 3 [Loader].”

They then obtain their reachability lower bounds at order 4 onwards.  This is a cited
statement: Ong--Tzevelekos attribute it to Loader, and §4.7.1b checks it against the type
of the unknown in Loader's construction (Loader's order 4 in his shifted convention, order 3
in (17)).  Below, "Loader's order-3 equation lemma" means: solvability of systems (18) in
which $`X`$ has a type of order at most 3 is undecidable.

**Lemma 13 (order-3 non-universality).** Assume Loader's order-3 equation lemma. Then some Boolean Sieber carrier $`D^B_τ`$, with
`ord(τ) ≤ 3`, contains a non-definable element.

*Proof.* Suppose every Boolean Sieber carrier through order 3 were universal.  Given an
order-3 Loader system (18), compute the finite carriers occurring in it bottom-up.  At a
function type the ambient monotone function space is finite.  Membership in the Sieber
carrier has two complementary semi-decisions:

* enumerate arities, finite intersections of elementary Sieber relations, and related tuples;
  a non-member is eventually rejected by a finite violated relation;
* enumerate closed finitary-PCF terms and compare their finite semantic tables with the
  candidate; by the assumed universality, every member is eventually accepted.

Dovetail these searches for the finitely many ambient candidates.  Hence the carrier at the
type of $`X`$ is computable.  Evaluate each candidate $`x`$ on the finitely many tuples
($`a^j_1,\ldots,a^j_n`$).  Ground adequacy makes (18) true exactly when these finite table
values are the specified booleans, and universality says a semantic solution exists exactly
when a term solution exists.  This decides Loader's order-3 problem, contradiction.
`□`

This is a localized version of the argument of Sections 2--3, proved here from Loader's
order-3 equation lemma (cited) and Lemmas 1, 2 and 5.

#### 4.7.1a Universality at orders 2 and 3, conditionally on Sieber's presentation

**Sieber's definability result (cited).**  Sieber (*Reasoning about sequential functions
via logical relations*, 1992), as stated in Streicher's *Domain-Theoretic Foundations of
Functional Programming*: in the standard hierarchy, at every type of level at most 2, an
element is invariant under all finite-arity PCF logical relations iff it is the supremum of
a directed set of PCF-definable elements.  Streicher also recalls Sieber's characterization
of those relations as the finite-arity sequentiality relations of Section 1.  This is a
statement about invariant elements of the *standard* hierarchy, whose function spaces
contain all (monotone or continuous) maps on the full carriers of the argument types.

**Identification hypothesis (I).**  At every type of order at most 2 (with Streicher's
"level" read as $`\mathrm{ord}`$ in (17)), the carrier $`D^B_τ`$ of Section 1 corresponds,
by restriction of functions to the carriers already built, to the set of invariant elements
of the standard hierarchy at $`τ`$, preserving definability.  $`D^B`$ builds each function
space on the carriers of the argument types, not on the full function spaces, and this
document does not prove (I).

**Theorem U (conditional).**  Assume Loader's order-3 equation lemma and (I).  In the
finitary Boolean model $`D^B`$, every element at every type of order at most 2 is
PCF-definable, while some element at a type of exact order 3 is not.

*Proof.*  For finitary PCF every carrier is finite, so a directed subset has a greatest
element, which is its supremum.  By Sieber's result and (I), every element of $`D^B_τ`$ with
$`\mathrm{ord}(τ)\le2`$ is the supremum of a directed set of definable elements, hence
definable:
```math
D^B_τ=\{⟦M⟧:M:τ\}
\qquad(\mathrm{ord}(τ)\le2).
\tag{18a}
```
Lemma 13 above supplies a non-definable element at some type of order at most 3.
Equation (18a) excludes orders 0, 1 and 2, so that element has exact order 3.  `□`

Without (I), Lemma 13 alone gives a non-definable element at some type of order at most 3.
(I) would be discharged by a proof that restriction to the constructed carriers is a
bijection between the invariant elements of the standard hierarchy and $`D^B_τ`$ at orders
at most 2 that commutes with the interpretation of terms, or by a direct proof of (18a) for
$`D^B`$.

Under the hypotheses of Theorem U and Theorem C below, the thresholds are:
```math
\begin{array}{c|cc}
 & \text{holds through} & \text{first failure}\\ \hline
\text{universality of } D^B & 2 & 3\\
\text{equational full abstraction of } D^N & 3 & 4.
\end{array}
\tag{18b}
```
The "holds through" column rests on Sieber's 1992 result and the corresponding
identification hypotheses, (I) and (I') of §4.7.4; the "first failure" column without
them reads "at most 3" and "at most 4".

The one-order offset is the same one visible in Loader's construction and in the
Stoughton compact-separation argument: a non-definable semantic object at type `σ`
is exposed observationally by terms at a type of shape `σ→B` (or `σ→nat`), one
order higher.

As an independent algorithmic check, Kawata--Asada--Kobayashi (APLAS 2015) give decision
algorithms for definability of order-2 finitary PCF; one is explicitly based on Sieber's
sequentiality relations.

#### 4.7.1b The concrete Loader type family

Loader's reduction gives substantially more type information than the bare order bound.
He fixes once and for all an undecidable semi-Thue system
$`W₀, R₁, …, R_N`$ over `{tt,ff}`.  For a word of length `m`, its encoding has type
```math
T_m = B^{2m+2}\to B.
```
Thus $`\mathrm{ord}(T_m)=1`$ in the convention (17).  If the fixed rule
$`R_i=[C_i\to C'_i]`$ has left/right lengths $`c_i,c'_i`$, Loader's Definition 9 /
Lemma 8 gives its encoding the type
```math
U_i=T_{c_i}\to T_{c'_i},
```
of order 2.

For a target word `W` of length `n`, the unknown in Loader's equation system therefore
has the explicit type
```math
σ_n =
T_{|W_0|}
\to U_1\to\cdots\to U_N
\to B^{2n+2}\to B.                              \tag{19a}
```
The prefix through $`U_N`$ is fixed once and for all with the chosen semi-Thue system;
only the final `2n+2` Boolean arguments grow with the target word.  Since some rule
argument has order 2, $`\mathrm{ord}(σ_n)=3`$.

This also explains Loader's concluding bookkeeping (he uses the shifted convention
`ord(B)=1`): word encodings have his order 2, rule encodings order 3, the equation
variable order 4, and the equivalence terms constructed from it order 5.  Subtracting one
gives orders 1,2,3,4 here.  Loader states that the latter order bound is optimal and that
the remaining type lengths are inherited from the semi-Thue system.

For Loader's **directed accessibility** premise, the relevant few-rule theorem is
Matiyasevich--Sénizergues (LICS 1996; TCS 2005), not Matiyasevich's earlier undirected
three-relation monoid word-problem example.  They prove individual accessibility
undecidable for a particular fixed semi-Thue system with exactly **three directed rules**.
Thus in (19a) one may take `N=3`:
```math
σ_n =
T_{|W_0|}\to U_1\to U_2\to U_3\to B^{2n+2}\to B.
\tag{19c}
```
The system may furthermore be taken over Loader's binary alphabet without increasing the
number of rules.  If its alphabet is $`\{a₁,…,a_k\}`$, use the injective synchronizing code
$`φ(a_i)=a b^i a`$ and replace each rule `u→v` by `φ(u)→φ(v)`.  Standard accounts of
the Matiyasevich--Sénizergues reduction note that
`w→*w'` iff `φ(w)→*φ(w')`; hence individual accessibility and the three-rule count are
preserved.  The cost is only an increase in the fixed rule lengths.

The final three-rule system in their construction has rules
```math
\rho(L)y\to\rho(M)y,\qquad
u_2^3\rho(d^ncd^n)y u_1^2\to u_2^3\rho(b^n)y u_2^2,\qquad
x\bar x\to\epsilon,
```
with `u₁=x x̄` and `u₂=x² x̄²`.  The first two rule lengths are fixed constants once their
underlying universal simulation and coding map `ρ` are fixed; the third has lengths 2 and
0.  The paper proves existence of one fixed instance, but the compact statement of the
result does not by itself expose small numerical values for the first two lengths.  This is
a bound on the Loader encoding, not a lower bound saying that a non-universal Sieber type
itself needs three order-2 arguments.

The fixed prefix can be normalized further.  Let `L` be the maximum of
$`|W₀|,c_i,c'_i`$.  Padding unused Boolean arguments with a fixed Boolean and forgetting
them gives definable retractions $`T_m ◁ T_L`$ for every fixed `m≤L`.  Retractions lift
through arrows, so each fixed $`U_i`$ retracts into $`T_L→T_L`$.  Thus all the
semi-Thue-specific higher-type structure is bounded by a fixed order-2 prefix; the
unbounded feature of Loader's guaranteed family is exactly the first-order tail
$`B^{2n+2}`$.

There is no uniform definable retraction of all the growing tails $`B^m→B`$ into one fixed
finitary-PCF type: every fixed type has a finite semantic carrier, whereas the family has
arbitrarily many distinct definable coordinate projections as `m` grows.  Thus Loader's
use of type length is not removable by a fixed finite packing trick.  Moving the input word
from type arity into term syntax does not evade this finite-state obstruction; some semantic
component must grow if arbitrarily many word positions are to remain distinguishable.

On the other hand, undecidability gives a useful existential statement about this *explicit*
family: it cannot be the case that every $`σ_n`$ is universal.  Therefore there is a least
finite `n₀` such that some element of $`D^B_{σ_{n₀}}`$ is non-definable.  Loader's argument does not identify `n₀`, nor does the reduction as stated provide an upper
bound on it.  (Undecidability alone does **not** prove that no computable upper bound exists;
that stronger claim would need a separate argument.)  Determining or bounding `n₀` is therefore
a new finite-model question rather than information directly supplied by Loader's proof.

Consequently, on the reading of §4.7.3, the order-4 counterexample type obtained after the
one-order separation step may be taken from the explicit family
```math
τ_n = σ_n\to B
```
on the Boolean side, or after the Boolean-to-natural translation,
```math
\widehat τ_n =
\bigl(
\widehat T_{|W_0|}
\to \widehat U_1\to\cdots\to\widehat U_N
\to \mathsf{nat}^{2n+2}\to\mathsf{nat}
\bigr)\to\mathsf{nat}.                           \tag{19b}
```
The undecidability argument guarantees that some member of this family carries the
obstruction; it does **not** identify a particular `n`.

#### 4.7.2 Transfer gives a compact order-≤3 obstruction

Choose $`h\in D^B_τ`$ from Lemma 13 and put
```math
e=i_τ(h)\in D^N_{\widehat τ}.
\tag{19}
```
The translation of types preserves order.  By the transfer theorem,
$`ψ^1 e=e`$; by Lemma P, $`e`$ is compact.

Assume for the moment that the natural Sieber model is **equationally** fully abstract at
all types of order at most 4.  Then $`e`$ cannot be PCF-definable.  For if
$`e=⟦M⟧`$, then
```math
⟦Ψ^1M⟧=ψ^1e=e=⟦M⟧.
```
Equational full abstraction (already at the order-≤3 type of $`M`$) gives
$`Ψ^1M\simeq M`$.  Müller's Game Term Theorem gives an equivalent grade-1 game term.
The grade-1 reinterpretation of §4.4 (Lemma 11) then gives a Boolean term denoting $`h`$,
contradicting its choice.

Thus, under the hypothetical order-4 full abstraction, $`D^N`$ contains a **non-definable
compact element of order at most 3**.

#### 4.7.3 Stoughton's contradiction costs exactly one order

We use the converse compact-definability argument of Stoughton,
*Equationally fully abstract models of PCF* (MFPS 1989 / LNCS 442, 1990),
Theorem 5.7, as reproduced in Streicher's *Domain-Theoretic Foundations of Functional
Programming* (Lemma 13.2 in the available version), which attributes it to Stoughton.

The cited theorem is global: in its class of models, equational full abstraction implies
that every compact element is definable.  What is used here is an order-local version, a
non-definable compact element at $`σ`$ contradicts equational full abstraction at
$`σ\to\mathsf{nat}`$.  That version is **a reading of the proof's internal order
bookkeeping** in Streicher's Lemma 13.2, not a cited theorem; neither Stoughton nor
Streicher states it.  The points of the proof it relies on are:

1. Choose a minimal type $`σ=σ_1\to\cdots\toσ_n\to\mathsf{nat}`$
   containing a non-definable compact $`e`$.  Compact elements at each proper argument type
   $`σ_i`$ are then definable by minimality.
2. Choose a finite projection level $`k`$ with $`e=ψ^k e`$.  The proof works entirely with
   the finite image of $`ψ^k`$.
3. Order extensionality supplies the pointwise order.  Compact inequalities can be witnessed
   on compact arguments, which are definable by step 1.
4. The proof uses finite infima.  This is not a parallel operation: at flat ground type
   $`\mathsf{glb}(x,y)`$ is PCF-definable sequentially (evaluate one numeral and then test
   the other for the same numeral), and at arrow types it is defined pointwise.  Streicher
   explicitly notes that in the order-extensional case these function-space infima are
   pointwise and PCF-definable.
5. From $`e`$, the finite projection, and the finitely many definable elements at that level,
   Stoughton's construction produces **two closed terms of type** $`σ\to\mathsf{nat}`$ (20),
   which agree on every closed PCF argument $`P:σ`$, hence are observationally equivalent
   by the Context Lemma, but whose denotations differ when applied semantically to $`e`$.

Point 5 is the order bookkeeping that the reading relies on.  From (17),
```math
\mathrm{ord}(σ\to\mathsf{nat})
 =\mathrm{ord}(σ)+1.
\tag{21}
```
On this reading, a non-definable compact at order at most 3 contradicts equational full
abstraction at a type of order at most 4.

The properties of the model that the proof uses, as read above, hold in $`D^N`$: continuity
and pointwise order, the finite projections and their approximation property, and
compactness of finite-level elements are proved (Lemma P, in Lean in `Algebraic.lean`);
definable projection terms, standard ground tests and definable finite infima are PCF
facts.  That the proof needs no further property of its class of models (for instance a
global SFP presentation) is part of the reading.

#### 4.7.4 Upper and lower bounds on the first failing order

**Theorem C.**
1. *(Upper bound.)* Assume Loader's order-3 equation lemma (§4.7.1), Müller's Game Term
   Theorem (GT) (§4.1), and the order-local reading of Stoughton's proof (§4.7.3).  Then
   $`D^N`$ fails equational full abstraction at some type of order at most 4.
2. *(Exact order.)* Assume in addition hypothesis (I') below.  Then the least order at which
   $`D^N`$ fails equational full abstraction is exactly 4.

**Identification hypothesis (I').**  For closed terms of every type of order at most 3,
$`⟦M⟧ = ⟦N⟧`$ in $`D^N`$ if and only if $`M \simeq N`$.  This is what Sieber's 1992
positive result gives if it transfers to $`D^N`$.  O'Hearn and Riecke's abstract describes
that result as full abstraction "up to rank three types", for Sieber's model presented as
the invariant elements of the continuous hierarchy followed by an extensional collapse
(§4.1).  (I') therefore needs two identifications that this document does not prove: of
$`D^N`$ with that presentation at the types concerned, and of the "rank" convention with
$`\mathrm{ord} \le 3`$ in (17).  A proof of both, or a direct proof of (I') for $`D^N`$,
discharges it.

*Proof.* 1. Suppose $`D^N`$ is equationally fully abstract at every type of order at most
4.  Lemma 13 gives a non-definable $`h \in D^B_τ`$ with $`\mathrm{ord}(τ) \le 3`$.
§4.7.2 transfers it to a non-definable compact $`e`$ of the same order in $`D^N`$, using
(GT).  On the reading of §4.7.3, Stoughton's construction produces observationally
equivalent closed terms with different denotations at a type of order at most 4, a
contradiction.

2. By part 1 the least failing order is at most 4, and by (I') it is not 0, 1, 2 or 3.  `□`

The terms of part 1 satisfy $`M \simeq N`$ and $`⟦M⟧ \ne ⟦N⟧`$, so one of
$`⟦M⟧ \le ⟦N⟧`$ and $`⟦N⟧ \le ⟦M⟧`$ fails while both $`M \sqsubseteq N`$ and
$`N \sqsubseteq M`$ hold: part 1 also bounds the first inequational failure by 4.  By Lemma 12, inequational full abstraction then fails at every
exact order $`n \ge 4`$.

**Corollary (where to search concretely).** Under (I), every non-definable element of
$`D^B`$ lies at a type of order at least 3, so a concrete Boolean search for one starts at
order-3 types.  `((B→B)→B)→B` is the order-3 type studied in `gpu/REPORT.md`.

#### 4.7.5 Dependency audit

Theorem C, part 1, relies on the following external results; everything else in its proof
is proved in this document (Lemmas 1, 2, 5, 7–11, 13, P), and Lemmas P and 7–11 are also
proved in Lean.

* **Loader (2001), *Finitary PCF is not decidable*, TCS 266**, through
  **Ong--Tzevelekos (2009), *Functional Reachability*, LICS, Lemma 6 / Corollary 7**:
  solvability of the equation systems (18) is undecidable when the unknown has order 3.
  Cited: the order-3 statement is Ong--Tzevelekos's, attributed by them to Loader, and
  matches the type of the unknown in Loader's construction (§4.7.1b).  Used in Lemma 13.
* **Müller (2012), Game Term Theorem, LMCS 8(4), Theorem 4.12**, at grade 1: a term
  fixed observationally by the level-1 projection is equivalent to a grade-1 game term.
  Cited, with the transcription into this repository's PCF and the head-reduction versus
  unrestricted-reduction gap described in §4.1.  Used in §4.7.2.
* **Stoughton (1990), *Equationally fully abstract models of PCF*, Theorem 5.7, as
  reproduced in Streicher, Lemma 13.2.**  The cited theorem is global (equational full
  abstraction implies compact definability).  The step used, that a non-definable compact
  at $`σ`$ contradicts equational full abstraction at $`σ\to\mathsf{nat}`$, is a reading of
  the proof's internal order bookkeeping (§4.7.3), not a cited theorem.  Streicher also
  notes the PCF-definability of the pointwise infima the proof uses.

Theorem C, part 2, and the positive half of Theorem U rely in addition on:

* **Sieber (1992), *Reasoning about sequential functions via logical relations*.**
  Cited for invariant elements of the standard (or continuous) hierarchy: definability at
  level at most 2 (as stated by Streicher) and full abstraction "up to rank three types"
  (as described by O'Hearn and Riecke).  It transfers to $`D^B`$ and $`D^N`$ only under the
  identification hypotheses (I) and (I'), which this document states and does not prove.

### 4.8 What remains open

- **Lean formalisation of §4.7.** Theorem U and Theorem C are not formalised in Lean; the Lean endpoints are Theorems A and B. Formalising Theorem C, part 1, needs the order-3 equation lemma as a hypothesis and the order-local Stoughton construction as a proof.
- **Sieber's presentation.** Theorems A, B and C, part 1, are about the direct presentations $`D^B`$ and $`D^N`$. Their identification with Sieber's presentation (invariant elements of the standard or continuous hierarchy, then the extensional collapse) is open; it is hypotheses (I) and (I') in §4.7.
- **The cited theorems.** They are used as stated above and are not re-proved. For (GT), the claims outside Lean are that the transcription into this repository's PCF is faithful and that the two reduction strategies make the same observations (§4.1).

## 5. Remarks

**Why this does not apply to the Kripke construction.** Each Kripke world is finite, but there are infinitely many worlds (all finite typed contexts), and the arrow clause quantifies over every extension of the current world. Checking that a higher-type tuple is related is then no longer a finite computation, so the rejection search of Lemma 6 is not available. The same holds for preorder-shaped worlds.

**Unary PCF is different.** Over the one-point ground type $`\{\bot, \top\}`$ the answer is positive at all types: Laird (*Sequentiality in bounded biorders*, 2005, Theorem 3.11) shows that every standard order-extensional model of unary PCF excluding parallel composition is universal, and a single ternary test excludes it.

## 6. The Lean formalisation

```lean
def SieberNotUniversal : Prop :=
  Loader → ∃ (τ : Ty) (f : SieberBool τ), ¬ Definable f

theorem sieber_not_universal : SieberNotUniversal
```

**`Loader`** (`Standard.lean`) is `¬ ComputablePred (fun p => ObsEquivCode p.1 p.2)`: the set of pairs of codes of observationally equivalent closed terms of the same type is not computable. Here `ObsEquiv M N` compares the values of `K M` and `K N` in the full set-theoretic hierarchy over $`V`$ (`Tm.std`), for every closed `K`. Loader's theorem is stated with the operational observed value, the normal form. That the two agree (every closed ground term reduces to a normal form whose value is its value in the full hierarchy) is argued in the module docstring of `OR/Sieber/Standard.lean` and is not proved in Lean. Theorem B is

```lean
theorem natural_sieber_not_inequationally_fully_abstract (hL : Loader)
    (hMP : NS.MilnerPlotkin) (hMu : MullerGameTermTheorem) :
    ¬ NS.InequationallyFullyAbstract
```

- **`NS.InequationallyFullyAbstract`** states $`M \sqsubseteq N \iff ⟦M⟧ \le ⟦N⟧`$ for closed terms of the repository's PCF, where $`\sqsubseteq`$ is the contextual preorder `ContextualOpLE` and $`⟦\cdot⟧`$ is the denotation in `NS.D` (`NatModel.lean`).
- **`NS.MilnerPlotkin`** is (MP) instantiated at the one model $`D^N`$: if `OrderExtensional`, `OmegaAlgebraic`, `LeastFixedPoints` and `InequationallyFullyAbstract` hold of $`D^N`$, every compact element of $`D^N`$ is the denotation of a closed term. The first three premises are proved (`orderExtensional`, `omegaAlgebraic`, `leastFixedPoints`) and discharged inside the proof. That this instance follows from Milner's theorem, whose premises are stated for his class of models, is a reading of the citation; it is not proved in Lean.
- **`MullerGameTermTheorem`** (`GameTerms.lean`) is (GT) at grade 1 only, transcribed with Müller's own $`Ψ_1`$ (`MullerPsi`) and grammar (`Game`, which also allows $`λ`$ over $`⊥`$ and so only weakens the hypothesis): a closed `M` with `Ψ₁ M ≃ M` is observationally equivalent to `G.toTm` for a game term `G`. Equivalence `≃` is `ContextualOpEq`, observed by this repository's call-by-name head reduction; Müller observes numerals reached by unrestricted reduction. That the two observations agree (§4.1) is a standardisation argument outside Lean. The form used in the proof, `MullerGrade1` (`M` is equivalent to `embed G` for a Boolean term `G`), is derived from it in Lean (`mullerGrade1`).

Neither cited theorem is proved in Lean, so Theorem B is as strong as those theorems in the Lean forms stated above, together with the readings listed next. Both proofs have no `sorry` and depend only on `propext`, `Classical.choice` and `Quot.sound`.

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
| `NatModel.lean` | The ordinary (single-world) Sieber model over $`ℕ_⊥`$, `NS.D`, with the interpretation `NS.denote` of PCF. |
| `Transfer.lean` | `ψⁿ` in `NS`; Lemmas 7–9: the maps `i`, `r` (`tr`). |
| `Algebraic.lean` | Lemma P and Lemma 10: `level_compact`, `compact_iff_level`, and the premises of (MP). |
| `Reinterpret.lean` | Game terms as `embed G`; Lemma 11 as the logical relation `LRel` (`Tm.lrel`, `den_of_embed`). |
| `GameTerms.lean` | Müller's $`Ψ_1`$ and grade-1 game terms, `MullerGameTermTheorem`, and the equivalences `MullerPsi_equiv` and `Game.equiv_embed`. |
| `NotFullyAbstract.lean` | The hypotheses and Theorem B, `natural_sieber_not_inequationally_fully_abstract`. |
