# O’Hearn–Riecke full abstraction for PCF in Lean 4

This repository is a Lean 4 formalisation of Peter W. O’Hearn and Jon G. Riecke, **“Kripke Logical Relations and PCF” (1995)**, including the construction of the relational model, finite definability, separation, computational adequacy, and the resulting inequational and equational full-abstraction theorems for PCF.

The final theorem (`OR/Adequacy.lean`) is:

```lean
theorem full_abstraction_op {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualOpLE M N ↔ denote M ≤ denote N :=
  (contextual_op_iff_den M N).trans (full_abstraction_den M N)
```

For terms `M N : Γ ⊢ τ`, `ContextualOpLE M N` says that every closing single-hole PCF context of ground result type that evaluates `M` to a numeral evaluates `N` to the same numeral. The order on denotations is pointwise over all semantic environments.

## Formalisation status, provenance, and relation to the paper

**Kernel status.** The complete development builds successfully under Lean 4.19.0 and the pinned Mathlib revision. The first fully successful proof build was **Lean CI #26** at commit `1c6e484`. After the exact SURFACE paper was read and the formalisation was changed to match its finite-world category and Kripke-test definitions, **Lean CI #53** at commit `e705bf6` again passed the full build, source audit, and selected-theorem transitive axiom audit; CI repeats all three on every push. The audited results depend only on `propext`, `Classical.choice`, and `Quot.sound`; the source audit rejects `sorry`, `admit`, custom `axiom`, `unsafe`, and `native_decide`, among other escape hatches.

**How it was developed.** The **initial formalisation was produced before the exact source paper had been obtained and read in full**. Its source alignment was based on bibliographic metadata and on a reconstructed proof-level specification, rather than on a line-by-line audit of the paper itself. After the SURFACE PDF was supplied, the development entered a second phase: the actual paper became the specification of record, and definitions/proofs were changed to match it except where a difference is documented below.

The complete development was also written without access to a local Lean/Lake installation. After it was committed, GitHub Actions was used as the compiler feedback loop: source was edited from the diagnostics of one CI run, committed, and checked by the next run. The first full compile attempt was **CI #10**; the first green full build was **CI #26**. Thus the complete draft took **17 full CI runs (#10–#26), i.e. 16 compile/repair iterations after the first failed check**, to reach a kernel-checked result. Earlier workflow runs were repository/staging checks rather than iterations on the complete development.

The repair iterations were overwhelmingly proof-engineering and elaboration repairs rather than changes to the mathematical statement. They included:

- making directed-supremum and product/function-space proof arguments explicit where elaboration chose the wrong obligation;
- repairing dependent renaming/substitution equalities and binder bookkeeping in the intrinsically typed syntax;
- making flat-domain evaluation, conditional monotonicity, and stabilization proofs explicit;
- repairing finite-interpolation/sequentiality proofs exposed once the lower layers compiled;
- exposing bundled relational-object carriers and preserving object identity so Lean's coercion/typeclass inference could see the intended domains;
- making dependent semantic environments, projections, finite worlds, and their induction motives explicit;
- repairing the higher-type definability induction without weakening its arbitrary-related-argument requirement;
- generalizing recursive context/type indices in semantic separation;
- spelling out impossible ground cases and variable cases in computational adequacy; and
- finishing regression examples and strengthening CI so a green run requires source audit, kernel compilation, and the axiom whitelist.

**Relation to O'Hearn--Riecke.** The mathematical architecture is the paper's: Kripke/sequentiality relations define the higher-type model; finite projections give finite definability; finite approximation and definability give a separating PCF context; adequacy connects denotational and operational observations. The proof of Lemma 12 is followed step by step: as in the paper, finite definability is proved through the stronger finite-world tuple claim, the forward arrow case applies the tuple to a fresh variable and substitutes the domain projection, and the reverse arrow case projects an arbitrary related argument tuple to finite level (printed p. 13) before input absorption removes the projection.

The Lean development is not, however, a line-by-line transcription. These are the differences, all of representation, generality or added detail:

- **worlds.** The paper's tests range over subcategories of `Finset`. A Lean `Test` is any small concrete category of finite types: an index type of worlds, a finite type `El w` at each world, and a class of functions as morphisms. This contains every subcategory of `Finset`, and every `Test` is a subcategory of `Finset` up to relabelling its elements, so objects and morphisms of `SR` are unchanged; the relabelling argument itself is not formalised, since Lean simply uses the larger class throughout;
- **universes.** A test carries a small world type and finite element types at each world, so `Test` lives in `Type 1` while carriers stay in `Type 0`; preserving every test is a proposition, so `Hom A B` remains small enough to serve at the next arrow type, with no resizing axiom or universe-encoding theorem;
- **the selected test `C_n`, `R_n`.** Its worlds are typed contexts `Γ`, with elements the finite environments of level `n` (listed newest variable first), and its morphisms are exactly the paper's prefix projections, represented by typed context-extension witnesses (`Extension`). A tuple in `R_n` is represented by an open term `Γ ⊢ nat` evaluated at the environment, where the paper uses a closed curried term `s₁ → … → sₘ → nat` applied via `uncurry`; λ-abstraction and application translate between the two. The same open-term representation is used in the Lemma 12 claim;
- **the ground projection term.** The paper's `Pⁿ_nat` is a nested `ifz (predᵏ x)`; Lean uses a recursive `ifz`/`succ`/`pred` term. Both denote the cut at `n` (`projection_nat`); the arrow projection is the paper's `λx.λy. Pⁿ_t (x (Pⁿ_s y))`;
- **contexts.** `PCtx` contexts have exactly one hole, and the hole carries a type-preserving renaming of `Γ` into the variables in scope, which is how de Bruijn syntax says which binders capture the plugged term's free variables. This admits some contexts with no named-syntax counterpart (a renaming may identify variables). The direction `⟦M⟧ ⊑ ⟦N⟧ ⇒ M ≼ N` is proved for all of them. For the converse, the separating contexts constructed by the proof use only the identity renaming at the hole, so they are ordinary contexts; that the converse therefore also holds with only ordinary contexts quantified is not stated as a separate Lean theorem;
- **separation.** The paper says Theorem 14 "follows from Lemma 10, Lemma 12, and continuity". Lean spells this out as an explicit separating context, by induction on the result type (section 5 below);
- **operational adequacy.** The paper only remarks that adequacy "can be shown using the standard computability method". Lean defines the call-by-name operational semantics and proves adequacy and operational full abstraction;
- **finite interpolation.** The primitive-closure characterisation of sequentiality relations (Proposition 2) is proved in the development, not assumed.

These are **explications or proof-representation changes, not changes to the full-abstraction claim**. No external formalisation of O'Hearn--Riecke is imported: apart from Mathlib, every result above has a local proof. Two claims in the paper are formalised only as far as the rest of the development uses them: the bifunctoriality of `×` and exponentials in Lemma 8(a) and the naturality in Lemma 8(b) (Lean has the exponential action on morphisms, `curry`/`uncurry` and their inverse laws), and the cpo-enrichment in Proposition 9 (Lean proves the hom-sets are directed-complete and that `curry`/`uncurry` are monotone, but not that composition is continuous).

One point needs careful wording. **Lemma 12 itself is stated as the closed finite-definability theorem, but its proof immediately strengthens the induction hypothesis.** On printed pp. 12--13 the paper says, after stating Lemma 12, “We prove the following claim by induction on the type t,” and quantifies over an arbitrary finite world `w = [Dⁿ_s₁, …, Dⁿ_sₘ]` and tuple `g : w → ⟦t⟧` with `g = g;ψⁿ_t`, proving relatedness iff representability. The Lean theorem `strong_finite_definability` is therefore not an invention needed to repair the paper: it formalizes the stronger claim that the paper itself uses inside the proof. The closed theorem `finite_definability` corresponds to Lemma 12's stated conclusion.

### Source audit against the paper

The authoritative comparison source is the **SURFACE copy committed at [`paper/OHearn-Riecke-Kripke-Logical-Relations-and-PCF.pdf`](paper/OHearn-Riecke-Kripke-Logical-Relations-and-PCF.pdf)** (from https://surface.syr.edu/lcsmith_other/3): Peter W. O'Hearn and Jon G. Riecke, *Kripke Logical Relations and PCF*, Information and Computation 120(1):107--116, 1995, DOI [10.1006/inco.1995.1103](https://doi.org/10.1006/inco.1995.1103). Its title page says “To appear in Information and Computation” and “Accepted, October 1994”; SURFACE catalogs it as the 1995 article. The paper text has its own printed pagination 1--18; the SURFACE PDF has an additional repository cover page, so PDF page numbers are offset by one.

The correspondence now uses exact numbered statements and printed pages:

| Paper | Printed page(s) | Lean/formalisation correspondence | Audit note |
|---|---:|---|---|
| Definition 1; Proposition 2 | 4 | `Elementary`, `finite_interpolation`, `sequential_iff_primitive_closed` | Proposition 2 is Sieber's finite-arity characterization used later by Proposition 6. |
| Definition 3 | 6 | `KRel` | Completeness means bottom plus directed-lub closure; Kripke monotonicity is reindexing along world morphisms. |
| Definitions 4--5; Proposition 6 | 7 | `Test`, ground sequentiality closure | Proposition 6 reduces finitary Kripke sequentiality to preservation by 0, succ, pred and ifz. |
| Definition of `SR` | 8 | `Obj`, `Uniform`, `Hom` | The paper quantifies over subcategories of `Finset` and finitary Kripke sequentiality relations, with explicit concreteness and uniformity conditions. Lean's `Test` generalises the subcategories to small concrete categories of finite types (see above). |
| Lemma 7 | 9 | hom-space dcpo/exponential-relation closure and concreteness | The paper proves concreteness and calls the other parts routine/from the definition; Lean proves all parts. |
| Lemma 8 | 9--10 | products/exponentials, curry/uncurry | Lean proves the product and exponential structure and the `curry`/`uncurry` bijection (with its continuity and uniformity obligations); bifunctoriality (8a) and naturality are not stated. |
| Proposition 9; the fixed-point map `Y` after it | 10 | CCC structure, order extensionality (`le_iff_global`), `Hom.fixMap` | Lean separates these into named constructions/lemmas. Cpo-enrichment (continuity of composition) is not stated. |
| Lemma 10 (Milner) | 11 | projection approximation and idempotence | Lean proves the projection algebra explicitly. |
| Definition of `C_n`, `R_n`; Lemma 11 | 12 | `finiteTest`, selected ground relation | Worlds are typed contexts with finite environments as elements; the morphisms are exactly the paper's prefix projections, encoded by `Extension`. `R_n` tuples are represented by open terms `Γ ⊢ nat` rather than closed curried terms. Lemma 11 is proved by the fields of `finiteTest`. |
| Lemma 12 and its proof-strengthened claim | 12--13 | `strong_finite_definability`, `finite_definability` | The *statement* of Lemma 12 is closed finite definability. The *proof itself* strengthens to arbitrary finite worlds and finite-level tuples and proves relatedness iff representability by induction on type. Lean mirrors this proof structure. |
| Definition 13 | 14 | `ContextualDenLE` (and, via adequacy, `ContextualOpLE`) | The paper defines observable approximation denotationally and remarks that adequacy for the operational semantics can be shown by the standard computability method. Lean contexts are single-hole with a renaming at the hole (see above). |
| Theorem 14 (Full Abstraction) | 14 | `full_abstraction_den`; with explicit adequacy, `full_abstraction_op` | The paper gives the theorem and says its proof follows from Lemmas 10, 12 and continuity; Lean expands the separating-context and operational arguments. |

This matters for the interpretation of “formalizing the paper.” There are three distinct cases to audit separately: (1) details suppressed by ordinary mathematical convention; (2) a theorem whose stated conclusion is weaker than the induction claim explicitly used in its proof, as with Lemma 12; and (3) an actual change of construction. There is no category-(3) change: in particular `finiteTest` uses exactly the paper's prefix projections. (An earlier version used all type-preserving renamings as morphisms of `C_n`; this was removed once the paper was read.)

The repository should therefore not claim that every Lean definition is a literal transcription. It claims a checked formalization of the same full-abstraction argument, with deviations identified and audited against the exact source statements above.

## 1. Language and theorem

Types are

```math
\tau ::= \mathsf{nat} \mid \sigma \to \tau.
```

Terms are intrinsically typed and include variables, abstraction, application, fixed points, zero, successor, predecessor, and a ground-result conditional. The development follows the paper’s convention

```math
\mathrm{pred}(0)=\bot,
```

rather than truncated predecessor.

For `M,N : Γ ⊢ τ`, operational contextual approximation is

```math
M \preceq_{\mathrm{ctx}} N
\quad\Longleftrightarrow\quad
\forall C[-] : (\Gamma,\tau) \rightsquigarrow \mathsf{nat},\ \forall n,
\ C[M]\Downarrow n \Rightarrow C[N]\Downarrow n.
```

The goal is

```math
\boxed{
M \preceq_{\mathrm{ctx}} N
\quad\Longleftrightarrow\quad
\forall\rho\in⟦\Gamma⟧,
⟦M⟧\rho
\sqsubseteq
⟦N⟧\rho.
}
```

Hence contextual equivalence is equality of denotations.

The development separates the denotational full-abstraction theorem from the operational adequacy theorem rather than silently identifying the two notions of observation.

## 2. The relational model

The crucial point is that the function-space carrier is **not** the set of all continuous functions followed by a quotient. Arrow denotations are relationally constrained from the outset.

### Ground tests

For a finite world `w` and `A ⊆ B ⊆ w`, define the elementary sequentiality relation

```math
S^w_{A,B}(g)
\quad\Longleftrightarrow\quad
\bigl(\exists i\in A,\ g(i)=\bot\bigr)
\ \lor\
\bigl(\forall i,j\in B,\ g(i)=g(j)\bigr).
```

A sequentiality relation is an intersection of elementary relations. A ground test supplies such a relation at every finite world; the family contains the bottom tuple, is closed under directed suprema, and is stable under reindexing along world morphisms.

The Lean development also proves the equivalent characterization by closure under the PCF ground operations. The finite decision-tree interpolation argument is represented directly rather than assumed as an external characterization theorem.

### Objects and morphisms

An object `A` contains:

- a pointed directed-complete partial order `|A|`, and
- for every ground test `R`, an admissible Kripke relation `A(R)`.

It satisfies concreteness:

```math
\forall R,w,a\in|A|,
\qquad A(R)^w(\lambda i.a).
```

A morphism `f : A → B` is Scott-continuous and uniformly preserves every ground test:

```math
\forall R,w,g,
\qquad A(R)^w(g) \Rightarrow B(R)^w(f\circ g).
```

Thus the carrier of an exponential is

```math
|B^A| = \mathrm{Hom}_{\mathsf{SR}}(A,B)
```

with pointwise order.

Its relation is

```math
\begin{aligned}
(B^A)(R)^w(g) \Longleftrightarrow {}&
\forall(v,\varphi:v\to w),\ \forall h:v\to|A|,\\
& A(R)^v(h) \Rightarrow
B(R)^v\bigl(\lambda i.\,g(\varphi i)(h(i))\bigr).
\end{aligned}
```

Two different universal quantifications are important here:

1. membership in the **arrow carrier** requires preservation of every ground test;
2. membership in the **arrow relation at one test** requires quantification over every future-world reindexing inside that test.

The files prove the closure properties needed for products, exponentials, evaluation, currying, and least fixed points. Term interpretation therefore returns a uniform morphism, not a bare function plus a later unproved relational obligation.

## 3. Finite projections

For ground type,

```math
p_{\mathsf{nat}}^n(\bot)=\bot,
\qquad
p_{\mathsf{nat}}^n(\uparrow k)=
\begin{cases}
\uparrow k & k\le n,\\
\bot & k>n.
\end{cases}
```

For arrows,

```math
p_{\sigma\to\tau}^n(f)(x)
=
p_\tau^n\bigl(f(p_\sigma^n(x))\bigr).
```

Each projection is denoted by a closed PCF term. The development proves the four structural laws used throughout the argument:

```math
p_\tau^n(d)\sqsubseteq d,
```

```math
n\le m \Rightarrow p_\tau^n(d)\sqsubseteq p_\tau^m(d),
```

```math
p_\tau^m(p_\tau^n(d)) = p_\tau^{\min(m,n)}(d),
```

and

```math
\bigsqcup_n p_\tau^n(d)=d.
```

Put

```math
D_\tau^n = \{d\in D_\tau \mid p_\tau^n(d)=d\}.
```

For finite-level functions two consequences are isolated explicitly:

```math
\boxed{f(p_\sigma^n(x))=f(x)}
\qquad\text{(input absorption)}
```

and

```math
\boxed{p_\tau^n(f(x))=f(x)}
\qquad\text{(output fixedness)}.
```

The finite-level sets are proved finite. At arrow type, restriction yields an injection

```math
D_{\sigma\to\tau}^n
\hookrightarrow
(D_\sigma^n\to D_\tau^n).
```

No surjectivity claim is needed.

## 4. Strengthened finite definability

The naive closed statement

```math
p_\tau^n(d)=d
\Rightarrow
\exists M:\varnothing\vdash\tau,\ ⟦M⟧=d
```

is too weak to support induction at higher type. As in the paper's proof of Lemma 12, the formalisation proves a stronger tuple theorem over arbitrary finite worlds.

For

```math
\Gamma=x_1:\sigma_1,\ldots,x_m:\sigma_m,
```

define the finite-environment world

```math
W_{n,\Gamma}
=
D_{\sigma_1}^n\times\cdots\times D_{\sigma_m}^n.
```

The empty context yields a singleton world. World maps are context projections.

Let

```math
\iota_\Gamma:W_{n,\Gamma}\to⟦\Gamma⟧
```

be componentwise inclusion. Define the selected ground relation by representability:

```math
R_n^\Gamma(g)
\Longleftrightarrow
\exists M:\Gamma\vdash\mathsf{nat},
\forall\rho\in W_{n,\Gamma},
⟦M⟧(\iota_\Gamma\rho)=g(\rho).
```

The range of `g` is the whole flat natural domain; only the environments are finite-level. Restricting outputs to `D_nat^n` would break closure under successor.

The strong theorem proved by induction on type is, schematically:

```math
\boxed{
\mathrm{Rel}_{n,\Gamma,\tau}(g)
\Longleftrightarrow
\exists M:\Gamma\vdash\tau,
\forall\rho,\ ⟦M⟧(\iota_\Gamma\rho)=g(\rho)
}
```

under the pointwise finite-level condition `p_τ^n(g ρ)=g ρ`.

### Arrow case: related implies representable

Suppose

```math
g:W_{n,\Gamma}\to D_{\sigma\to\tau}
```

is related and pointwise fixed. Extend the world by a variable of type `σ`. The tuple

```math
h(\rho,a)=a
```

is represented by the newest variable and therefore related by the reverse induction hypothesis.

Apply the arrow relation to `g` and `h`; this produces

```math
g'(\rho,a)=g(\rho)(a)
```

at type `τ`. Output fixedness makes `g'` finite-level, so the induction hypothesis yields

```math
L:\Gamma,x:\sigma\vdash\tau
```

representing it.

Define

```math
Q=\lambda x:\sigma.\,L[x:=P_\sigma^n x].
```

For arbitrary semantic `d`,

```math
\begin{aligned}
⟦Q⟧(\iota_\Gamma\rho)(d)
&=⟦L⟧(\iota_\Gamma\rho,p_\sigma^n(d))\\
&=g(\rho)(p_\sigma^n(d))\\
&=g(\rho)(d),
\end{aligned}
```

where the last step is input absorption. This is equality on the entire semantic function domain, not merely on finite arguments.

### Arrow case: representable implies related

Suppose `M : Γ ⊢ σ → τ` represents a pointwise fixed tuple `g`. Take an arbitrary future world and arbitrary related argument tuple

```math
h:W_{n,\Gamma,\Delta}\to D_\sigma.
```

No finite-level assumption is made on `h`.

Project it:

```math
k=p_\sigma^n\circ h.
```

Uniformity of the projection preserves relatedness, while idempotence gives pointwise fixedness. The induction hypothesis then provides a term representing `k`. Applying the weakened `M` to that term represents

```math
\rho\mapsto
 g(\mathrm{drop}\rho)(p_\sigma^n(h(\rho)))
 =
 g(\mathrm{drop}\rho)(h(\rho)),
```

again by input absorption. The result is pointwise fixed by output fixedness, so the reverse induction hypothesis at `τ` yields relatedness.

The closed finite-definability theorem is recovered from this stronger theorem by using the constant tuple at the singleton empty-context world. **Concreteness is exactly what supplies relatedness of that constant tuple.**

## 5. Explicit separation

To prove reflection of contextual approximation, suppose

```math
⟦M⟧\not\sqsubseteq⟦N⟧.
```

Pointwise order gives an environment `ρ` with `⟦M⟧ρ ⋢ ⟦N⟧ρ`. The environment is the supremum of its finite projections, and an order failure at the supremum of a chain already occurs at some finite stage (`Chain.failure_at_finite_stage`), so there is a level `n` with

```math
⟦M⟧(p^n\rho)\not\sqsubseteq⟦N⟧(p^n\rho).
```

Finite definability represents `pⁿρ` by closed terms `T_1, …, T_m`, and the closing context `(λx_1…x_m.[-]) T_1 ⋯ T_m` (`PCtx.closing`) turns this into an order failure between closed terms (`semantic_separator`).

For closed terms, `closed_separator` proceeds by induction on the type. At `nat`, failure of `⟦M⟧ ⊑ ⟦N⟧` means `⟦M⟧ = ↑q` and `⟦N⟧ ≠ ↑q`, and the hole itself separates. At `σ → τ`, there is an argument `a` with `⟦M⟧a ⋢ ⟦N⟧a`; again the failure persists at a finite projection `p^k a`, with its own level `k`, and finite definability gives a closed term `A` with `⟦A⟧ = p^k a`. Then `⟦M A⟧ ⋢ ⟦N A⟧`, and the induction hypothesis at `τ` gives a context for `M A` and `N A`, which is composed with `[-] A`. Each level is shared by the two sides `M` and `N`. The resulting context has the shape

```math
\boxed{
C[-]
=
(\lambda x_1\ldots x_m.\,[-])\,
T_1\cdots T_m\,
U_1\cdots U_k,
}
```

with

```math
⟦C[M]⟧=\uparrow q,
\qquad
⟦C[N]⟧\ne\uparrow q.
```

Thus semantic order failure yields an explicit contextual separator. Preservation in the other direction is a structural induction on contexts using monotonicity of every semantic constructor.

## 6. Operational adequacy

The operational layer is proved separately, using call-by-name reduction and the computational logical relation

```math
d\triangleleft_{\mathsf{nat}}M
\Longleftrightarrow
\forall n,\ d=\uparrow n\Rightarrow M\Downarrow n,
```

and

```math
f\triangleleft_{\sigma\to\tau}M
\Longleftrightarrow
\forall a,N,
\ a\triangleleft_\sigma N
 \Rightarrow
 f(a)\triangleleft_\tau MN.
```

For each term this relation contains bottom and is closed under directed suprema; it is also backward closed under reduction.

The fixed-point case is explicit: from `f △ F`, prove by induction that

```math
f^k(\bot)\triangleleft \mathrm{fix}F.
```

The successor step uses

```math
\mathrm{fix}F\longrightarrow F(\mathrm{fix}F),
```

and directed closure yields

```math
Y(f)\triangleleft\mathrm{fix}F.
```

Together with reduction soundness, this proves ground adequacy:

```math
M\Downarrow n
\Longleftrightarrow
⟦M⟧=\uparrow n.
```

Combining adequacy with the denotational separator yields operational full abstraction.

## Repository layout

| Files | Contents |
|---|---|
| `OR.lean` | Root module importing the development. |
| `OR/Order.lean`, `OR/Flat.lean` | Directed completeness, continuous maps, products, function spaces, joint evaluation, fixed points, flat naturals. |
| `OR/Sequential.lean`, `OR/Worlds.lean` | Elementary sequentiality relations, finite interpolation, primitive-closure characterization, finite-world tests. |
| `OR/SR.lean` | Concrete relational objects, uniform morphisms, products, exponentials, evaluation, currying, fixed points. |
| `OR/Syntax.lean`, `OR/Interpretation.lean` | Intrinsically typed PCF, renaming/substitution, morphism-valued denotational semantics. |
| `OR/Projections.lean`, `OR/FiniteWorlds.lean` | Finite projections, absorption laws, finite images, approximation, selected finite-environment tests. |
| `OR/Definability.lean`, `OR/Compactness.lean` | Strong higher-type definability, closed definability, compactness, definable density/algebraicity. |
| `OR/FullAbstraction.lean` | Typed one-hole contexts, context monotonicity, explicit separation, denotational full abstraction. |
| `OR/Operational.lean`, `OR/Adequacy.lean` | Call-by-name semantics, logical relation, adequacy, operational full abstraction. |
| `OR/Observations.lean`, `OR/Examples.lean` | Numeral/termination observations and regression examples, including exclusion of parallel-or (a regression test for the uniform arrow carrier: it would fail for the full Scott-continuous function space). |
| `OR/AxiomAudit.lean` | Selected theorem axiom inspection. |
| `paper/` | The SURFACE copy of the paper used for the source audit. |
| `scripts/` | `check.sh` (full local check), the static source audit, and the axiom-audit checker. |

## Build and validation

The project currently targets Lean/Mathlib `v4.19.0`, as pinned in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

```sh
python3 scripts/static_audit.py
lake exe cache get
lake build
lake env lean OR/AxiomAudit.lean > axioms.log
python3 scripts/check_axioms.py axioms.log
```

Or run the combined checks (this is what CI runs; on macOS 26 it also works around the Mathlib cache tool failing to start, by running it through the interpreter):

```sh
bash scripts/check.sh
```

The source-level audit rejects `sorry`, `admit`, custom `axiom` declarations, `unsafe`, `native_decide`, `implemented_by`/`extern`, and interactive search tactics, checks the local import graph, and inventories declarations. It is **not** a substitute for elaboration and kernel checking.

Changes to the development should keep these properties, which the formalisation was built to respect:

- the relational carrier and the observation relation are not weakened to make proofs go through;
- finite definability, separation, and adequacy are proved, never assumed, and the axiom audit stays within `propext`, `Classical.choice`, and `Quot.sound`;
- `pred zero` diverges;
- arrows are uniform continuous morphisms;
- the selected finite test restricts environments, not outputs;
- strong definability quantifies over arbitrary contexts/tuples;
- reverse arrow definability first projects an arbitrary related argument tuple;
- each finite approximation level in the separation proof is shared by both sides.
