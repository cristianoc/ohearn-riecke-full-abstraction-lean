# The head-call lemma at $`τ_0=((B\to B)\to B)\to B`$

This document states and proves the lemma behind the non-definability arguments of
[`gpu/REPORT.md`](gpu/REPORT.md) ("A non-definable table that preserves every arity-3 test"),
[`gpu/verify_candidate.py`](gpu/verify_candidate.py) and
[`gpu/root_obstruction.py`](gpu/root_obstruction.py), and the first-call compatibility test that
follows from it.

**Lean.** `OR/Sieber/HeadCall.lean` proves Lemma 4 (`headCall`), Corollary 5 (`firstCall`) and Theorem 6 (`firstCall_compat`) for the Y-free language, in Sieber's model, which is the model a counterexample lives in. The proofs use only strictness of the conditional, soundness of normalisation and monotonicity. $`D_2`$ is a parameter there (any set of elements of $`D_{τ_1}`$ containing $`\bot`$), and the common upper bounds in Theorem 6 may be any elements of $`D_{τ_1}`$. `OR/Sieber/HeadCall/H3.lean` applies Theorem 6 to $`h_3`$ (§5.2): `not_definable` states that no closed term denotes $`h_3`$, with the five points given as denotations of closed terms. Lemma 1 is not formalised.

## 1. Language and model

**Types.** $`σ ::= B \mid σ\to σ`$. Write $`τ_1=(B\to B)\to B`$, so $`τ_0=τ_1\to B`$.

**Terms of finitary PCF over $`B`$.** Variables $`x^σ`$, abstraction $`λx^σ.M`$, application
$`M\,N`$, and the constants
```math
\mathsf{tt},\ \mathsf{ff},\ \bot \ :\ B,
\qquad
\mathsf{if} \ :\ B\to B\to B\to B .
```
$`\mathsf{if}\ M\ N\ P`$ is also written $`\mathsf{if}\ M\ \mathsf{then}\ N\ \mathsf{else}\ P`$.
The language **with fixpoints** adds constants $`Y_σ : (σ\to σ)\to σ`$ for every type $`σ`$.
Conditionals and $`\bot`$ at higher types are the terms
$`λ\bar x.\,\mathsf{if}\ M\ (N\,\bar x)\ (P\,\bar x)`$ and $`λ\bar x.\,\bot`$.

**Scott model.** $`D^S_B=\{\bot,tt,ff\}`$ with the flat order, and $`D^S_{σ\to σ'}`$ the monotone
maps $`D^S_σ\to D^S_{σ'}`$, ordered pointwise. Every $`D^S_σ`$ is finite, so monotone maps are
continuous and this is Plotkin's continuous-function model restricted to these types. The
constants denote $`tt`$, $`ff`$, $`\bot`$, the conditional strict in its first argument
($`\mathsf{if}\ \bot\ y\ z=\bot`$, $`\mathsf{if}\ tt\ y\ z=y`$, $`\mathsf{if}\ ff\ y\ z=z`$), and
$`⟦Y_σ⟧(f)=\bigsqcup_n f^n(\bot)`$. A closed term $`t:σ`$ **defines** $`⟦t⟧\in D^S_σ`$.

**The carriers of the computations.** $`D_1=D^S_{B\to B}`$ has 11 elements, all definable; an
element is written $`f(\bot)f(tt)f(ff)`$, e.g. $`\bot tf`$. $`D_2\subseteq D^S_{τ_1}`$ is the set of
the 355 definable elements, with the order inherited from $`D^S_{τ_1}`$ (pointwise on
$`D_1`$). A table $`h:D_2\to B`$ is **definable** when some closed $`t:τ_0`$ has
$`⟦t⟧(F)=h(F)`$ for every $`F\in D_2`$. The **support** of $`h`$ is
$`\mathrm{supp}(h)=\{F\in D_2 \mid h(F)\neq\bot\}`$.

## 2. Fixpoints at finite types

**Lemma 1 (fixpoint elimination).** For every closed term $`t`$ of finitary PCF with fixpoints
there is a closed term $`t'`$ without $`Y`$ with $`⟦t'⟧=⟦t⟧`$.

*Proof (proved).* Let $`\ell_σ`$ be the length of the longest strictly increasing chain in the
finite poset $`D^S_σ`$. For monotone $`f:D^S_σ\to D^S_σ`$ the sequence $`f^n(\bot)`$ is
increasing, and once two consecutive terms are equal it is constant. It therefore becomes
constant after at most $`\ell_σ`$ steps, and
```math
⟦Y_σ⟧(f)=f^{\ell_σ}(\bot)=⟦λf.\,\underbrace{f(\cdots f}_{\ell_σ}(Ω_σ)\cdots)⟧(f),
\qquad Ω_σ=λ\bar x.\,\bot .
```
So $`Y_σ`$ and the $`Y`$-free term $`λf.\,f^{\ell_σ}(Ω_σ)`$ have the same denotation.
Replacing every occurrence of every $`Y_σ`$ in $`t`$ by the corresponding term gives $`t'`$;
$`⟦t'⟧=⟦t⟧`$ because the semantics is compositional. ∎

From here on all terms are $`Y`$-free.

## 3. Normal forms

Treat $`\mathsf{tt},\mathsf{ff},\bot,\mathsf{if}`$ as free variables of their types. A $`Y`$-free
term is then a term of the simply typed λ-calculus over the base type $`B`$.

**Cited facts.**
- *Weak normalisation.* Every term of the simply typed λ-calculus, open terms included, has a
  β-normal form: Girard, Lafont, Taylor, *Proofs and Types*, Cambridge University Press 1989,
  ch. 4 ("The Normalisation Theorem"), stated there for $`\to`$ and $`\times`$; strong
  normalisation is ch. 6, and Tait, "Intensional interpretations of functionals of finite type
  I", *J. Symbolic Logic* 32 (1967). Scope: pure simply typed terms with free variables. It
  transfers unchanged, because the constants are treated as free variables and only β is used.
- *Soundness of β.* If $`M\to_β M'`$ then $`⟦M⟧=⟦M'⟧`$ in the Scott model. This is the
  substitution lemma $`⟦M[N/x]⟧ρ=⟦M⟧ρ[x\mapsto⟦N⟧ρ]`$, proved by induction on $`M`$; it holds
  in every cartesian closed model of the simply typed λ-calculus, and the Scott model is one
  (Plotkin, "LCF considered as a programming language", *Theoret. Comput. Sci.* 5 (1977),
  223–255, for the continuous-function model of PCF; the finitary fragment is a sublanguage
  interpreted in the same way).

**Lemma 2 (shape of β-normal terms; proved).** A β-normal term is $`λ\bar x.\,y\,M_1\cdots M_k`$
with $`y`$ a variable or constant and each $`M_i`$ β-normal.

*Proof.* By induction on the term. An abstraction $`λx.M`$ has $`M`$ normal. Otherwise the
term is an application spine $`a\,M_1\cdots M_k`$ whose head $`a`$ is not an application; $`a`$
is not an abstraction, since $`(λx.M)M_1`$ would be a redex, so $`a`$ is a variable or a
constant. ∎

**Corollary 3 (proved).** Let $`G:B`$ be β-normal with free variables among $`F:τ_1`$ and the
constants. Then $`G`$ is one of
```math
\mathsf{tt},\qquad \mathsf{ff},\qquad \bot,\qquad F\,ψ,\qquad \mathsf{if}\ C\ N\ P,
```
where $`ψ:B\to B`$ and $`C,N,P:B`$ are β-normal with free variables among $`F`$ and the
constants. Every closed β-normal term of type $`τ_0`$ is $`λF.\,G`$ with such a $`G`$.

*Proof.* By Lemma 2, $`G=y\,M_1\cdots M_k`$ (no outer λ, since $`G`$ has type $`B`$). The
head's type has $`k`$ arguments and result $`B`$: for $`\mathsf{tt},\mathsf{ff},\bot`$ this
forces $`k=0`$, for $`F`$ it forces $`k=1`$ with $`M_1:B\to B`$, and for $`\mathsf{if}`$ it
forces $`k=3`$ with $`M_1,M_2,M_3:B`$. A closed normal term of type $`τ_0`$ is not a spine:
the heads $`\mathsf{tt},\mathsf{ff},\bot`$ have type $`B`$, and the partial applications of
$`\mathsf{if}`$ have types $`B\to\cdots\to B`$, whose first argument type is $`B\neq τ_1`$. So
it is $`λF.\,G`$, and $`G`$ is as above. ∎

The argument $`ψ`$ of $`F`$ is a λ-abstraction $`λz.M`$ or a partial application
$`\mathsf{if}\ C\ N`$; the latter η-expands to $`λz.\,\mathsf{if}\ C\ N\ z`$ with the same
denotation, so $`ψ`$ may always be taken of the form $`λz.M`$, where $`M`$ may mention $`F`$.

## 4. The head-call lemma

**Lemma 4 (head-call lemma; proved).** Let $`t`$ be a closed term of type $`τ_0`$ of finitary
PCF over $`B`$, with or without fixpoints, and let $`λF.G`$ be the β-normal form of its
fixpoint-free version (§2, §3). Then either $`⟦t⟧`$ is a constant function on
$`D^S_{τ_1}`$, or there is a term $`ψ=λz.M:B\to B`$ whose only free variable is $`F:τ_1`$ such
that, writing $`ψ_F=⟦ψ⟧[F\mapsto F]\in D_1`$ and
```math
t^\ast=λF.\ \mathsf{if}\ F\,ψ\ \mathsf{then}\ G\ \mathsf{else}\ G ,
```
1. for every $`F\in D^S_{τ_1}`$, $`⟦t⟧(F)\neq\bot`$ implies $`F(ψ_F)\neq\bot`$;
2. $`⟦t^\ast⟧=⟦t⟧`$, and the first evaluated action of $`t^\ast`$ is the strict call
   $`F\,ψ`$;
3. the map $`F\mapsto ψ_F`$ is $`⟦λF.\,ψ⟧\in D^S_{τ_1\to(B\to B)}`$, a definable element; in
   particular it is monotone.

*Proof.* By Lemma 1 and the cited facts, $`t`$ has a $`Y`$-free β-normal form with the same
denotation, which is $`λF.G`$ by Corollary 3. We prove, by induction on β-normal $`G:B`$ with
free variables among $`F`$ and the constants:

> (∗) either $`F\mapsto⟦G⟧`$ is constant, or some $`ψ:B\to B`$ with free variables among $`F`$
> and the constants has $`⟦G⟧\neq\bot\Rightarrow F(ψ_F)\neq\bot`$ for every $`F`$.

The cases are those of Corollary 3.
- $`G=\mathsf{tt},\mathsf{ff},\bot`$: constant.
- $`G=F\,ψ`$: then $`⟦G⟧=F(ψ_F)`$, so this $`ψ`$ works.
- $`G=\mathsf{if}\ C\ N\ P`$: apply (∗) to $`C`$.
  - If $`⟦C⟧`$ is the constant $`\bot`$, then $`⟦G⟧`$ is constantly $`\bot`$.
  - If $`⟦C⟧`$ is the constant $`tt`$, then $`⟦G⟧=⟦N⟧`$ for every $`F`$; apply (∗) to $`N`$.
    The constant $`ff`$ is symmetric, with $`P`$.
  - Otherwise (∗) gives $`ψ`$ for $`C`$. If $`⟦G⟧\neq\bot`$ then $`⟦C⟧\neq\bot`$, because the
    conditional is strict in its first argument, and so $`F(ψ_F)\neq\bot`$.

Applied to the body $`G`$, (∗) gives the alternative of the lemma and item 1. After
η-expansion $`ψ`$ has the form $`λz.M`$ (§3).

Item 2: if $`F(ψ_F)=\bot`$ then $`⟦t^\ast⟧(F)=\bot`$ and, by item 1, $`⟦t⟧(F)=\bot`$. If
$`F(ψ_F)\in\{tt,ff\}`$ then both branches give $`⟦G⟧(F)=⟦t⟧(F)`$.

Item 3: $`⟦λF.ψ⟧(F)=ψ_F`$ by the definition of the semantics of abstraction, and every
element of the Scott model is monotone. ∎

**Corollary 5 (proved).** If $`h:D_2\to B`$ is definable and $`h(\bot_{D_2})=\bot`$, then there is
a monotone $`Ψ:D_2\to D_1`$, the restriction of a definable element of
$`D^S_{τ_1\to(B\to B)}`$, with $`F(Ψ(F))\neq\bot`$ for every $`F\in\mathrm{supp}(h)`$.

*Proof.* Let $`t`$ define $`h`$. If $`⟦t⟧`$ is constant, its value is $`⟦t⟧(\bot)=h(\bot_{D_2})=\bot`$,
so $`\mathrm{supp}(h)=\emptyset`$ and any $`Ψ`$ works. Otherwise Lemma 4 gives $`ψ`$; take
$`Ψ(F)=ψ_F`$, restricted to $`D_2`$ (which contains $`\bot_{D_2}`$, the denotation of
$`λf.\bot`$). ∎

For a monotone $`h`$, the condition $`h(\bot_{D_2})=\bot`$ is equivalent to $`h`$ being
non-constant or constantly $`\bot`$.

**Remark (cited, used only in §5.3).** $`Ψ`$ in Corollary 5 also preserves every Sieber
relation, because it is the restriction of a definable element and definable elements are
invariant under all sequentiality relations: Sieber, "Reasoning about sequential functions via
logical relations", in *Applications of Categories in Computer Science*, LMS Lecture Note
Series 177 (1992), 258–269. Scope: Sieber's sequentiality relations and PCF terms; it applies
to finitary PCF over $`B`$ as a sublanguage.

## 5. The first-call compatibility test

Two elements $`a,b\in D_1`$ are **compatible**, written $`a\uparrow b`$, when they have an upper
bound in $`D_1`$. Since the pointwise join of two monotone maps $`B\to B`$ is monotone,
$`a\uparrow b`$ holds exactly when no input $`x`$ has $`a(x),b(x)`$ both defined and different.
For $`m\in D_2`$ let $`\mathrm{Allowed}(m)=\{a\in D_1 \mid m(a)\neq\bot\}`$.

### 5.1 Statement

**Theorem 6 (first-call compatibility test; proved).** Let $`h:D_2\to B`$ with
$`h(\bot_{D_2})=\bot`$. Let $`m_0,\dots,m_k\in\mathrm{supp}(h)`$, and let $`P`$ be a set of pairs
$`(i,j)`$ such that $`m_i`$ and $`m_j`$ have a common upper bound in $`D_2`$. If no choice
$`a_i\in\mathrm{Allowed}(m_i)`$ ($`0\le i\le k`$) has $`a_i\uparrow a_j`$ for all $`(i,j)\in P`$,
then $`h`$ is not definable.

*Proof.* Suppose $`h`$ is definable, and take $`Ψ`$ from Corollary 5. Put $`a_i=Ψ(m_i)`$; then
$`m_i(a_i)\neq\bot`$, so $`a_i\in\mathrm{Allowed}(m_i)`$. For $`(i,j)\in P`$ with common upper
bound $`u\in D_2`$, monotonicity gives $`a_i,a_j\le Ψ(u)`$, so $`a_i\uparrow a_j`$. This
contradicts the hypothesis. ∎

The test is sound and finite: it is a constraint problem over the finite sets
$`\mathrm{Allowed}(m_i)`$. It is not complete; a table can pass it and still be non-definable.

### 5.2 Application to $`h_3`$

$`h_3`$ is $`ff`$ on $`{\uparrow}129\cup{\uparrow}272\cup{\uparrow}321`$ and $`\bot`$ elsewhere
(`gpu/data/candidate_3cone_h.npy`); $`h_3(\bot_{D_2})=\bot`$. Take $`m_0=129`$, $`m_1=272`$,
$`m_2=321`$ and $`P=\{(0,1),(0,2)\}`$, with common upper bounds $`281\ge 129,272`$ and
$`333\ge 129,321`$. The allowed sets are
```math
\mathrm{Allowed}(129)=\{\bot tf,\ \bot ft,\ \bot ff,\ fff\},\quad
\mathrm{Allowed}(272)=\{\bot t\bot,\ \bot tt,\ \bot tf,\ ttt\},\quad
\mathrm{Allowed}(321)=\{\bot\bot t,\ \bot tt,\ \bot ft,\ ttt,\ fff\}.
```
- Every element of $`\mathrm{Allowed}(272)`$ has value $`t`$ at input $`tt`$. Among
  $`\mathrm{Allowed}(129)`$ only $`\bot tf`$ is $`t`$ (or undefined) at $`tt`$, so $`a_0\uparrow a_1`$
  forces $`a_0=\bot tf`$.
- $`\bot tf`$ is compatible with no element of $`\mathrm{Allowed}(321)`$: it conflicts with
  $`\bot\bot t`$, $`\bot tt`$ and $`ttt`$ at input $`ff`$, and with $`\bot ft`$ and $`fff`$ at input
  $`tt`$.

By Theorem 6, $`h_3`$ is not definable (proved). The order facts, the allowed sets and the
absence of a compatible choice are checked by `gpu/verify_candidate.py` (check 3), which also
runs the same test on the 20-cone table `gpu/data/bad_state_h.npy`.

### 5.3 Strengthened form

By the Remark after Corollary 5, $`Ψ`$ may further be required to be monotone on all of
$`D_2`$ and to preserve every Sieber relation. The test then asks whether some monotone
$`Ψ:D_2\to D_1`$ preserving a chosen set of Sieber relations has $`m(Ψ(m))\neq\bot`$ at every
minimal $`m`$ of $`\mathrm{supp}(h)`$; if none exists, $`h`$ is not definable (proved, from
Corollary 5 and the cited fundamental lemma; requiring the condition only at minimal points
suffices because $`Ψ`$ is monotone and $`m\le m'`$ gives $`m'(Ψ(m'))\ge m(Ψ(m))`$). Any subset
of the relations gives a sound test, since dropping constraints only enlarges the set of
admissible $`Ψ`$. `gpu/root_obstruction.py` decides this form with all arity-3 tests, adding
them lazily.
