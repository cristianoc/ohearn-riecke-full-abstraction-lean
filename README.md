# O’Hearn–Riecke full abstraction for PCF in Lean 4

This repository is a tentative Lean 4 formalisation of Peter W. O’Hearn and Jon G. Riecke, **“Kripke Logical Relations and PCF” (1995)**, including the construction of the relational model, finite definability, separation, computational adequacy, and the resulting inequational and equational full-abstraction theorems for PCF.

The intended final theorem is:

```lean
theorem full_abstraction_op {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualOpLE M N ↔ denote M ≤ denote N :=
  (contextual_op_iff_den M N).trans (full_abstraction_den M N)
```

For terms `M N : Γ ⊢ τ`, `ContextualOpLE M N` says that every closing PCF context of ground result type that evaluates `M` to a numeral evaluates `N` to the same numeral. The order on denotations is pointwise over all semantic environments.

> **Status.** Every theorem declaration in the current source has an attempted proof body. The project was generated in an environment without Lean/Lake, so it has **not yet been parsed, elaborated, or kernel-checked**. There are no intentional `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` escapes. The next step is to run `lake build` and repair the first compiler errors in dependency order.

## 1. Language and theorem

Types are

[
\tau ::= \mathsf{nat} \mid \sigma \to \tau.
]

Terms are intrinsically typed and include variables, abstraction, application, fixed points, zero, successor, predecessor, and a ground-result conditional. The development follows the paper’s convention

[
\operatorname{pred}(0)=\bot,
]

rather than truncated predecessor.

For `M,N : Γ ⊢ τ`, operational contextual approximation is

[
M \preceq_{\mathrm{ctx}} N
\quad\Longleftrightarrow\quad
\forall C[-] : (\Gamma,\tau) \rightsquigarrow \mathsf{nat},\ \forall n,
\ C[M]\Downarrow n \Rightarrow C[N]\Downarrow n.
]

The goal is

[
\boxed{
M \preceq_{\mathrm{ctx}} N
\quad\Longleftrightarrow\quad
\forall\rho\in\llbracket\Gamma\rrbracket,
\llbracket M\rrbracket\rho
\sqsubseteq
\llbracket N\rrbracket\rho.
}
]

Hence contextual equivalence is equality of denotations.

The development separates the denotational full-abstraction theorem from the operational adequacy theorem rather than silently identifying the two notions of observation.

## 2. The relational model

The crucial point is that the function-space carrier is **not** the set of all continuous functions followed by a quotient. Arrow denotations are relationally constrained from the outset.

### Ground tests

For a finite world `w` and `A ⊆ B ⊆ w`, define the elementary sequentiality relation

[
S^w_{A,B}(g)
\quad\Longleftrightarrow\quad
\bigl(\exists i\in A,\ g(i)=\bot\bigr)
\ \lor\
\bigl(\forall i,j\in B,\ g(i)=g(j)\bigr).
]

A sequentiality relation is an intersection of elementary relations. A ground test supplies such a relation at every finite world and is stable under reindexing.

The Lean development also proves the equivalent characterization by closure under the PCF ground operations. The finite decision-tree interpolation argument is represented directly rather than assumed as an external characterization theorem.

### Objects and morphisms

An object `A` contains:

- a pointed directed-complete partial order `|A|`, and
- for every ground test `R`, an admissible Kripke relation `A(R)`.

It satisfies concreteness:

[
\forall R,w,a\in|A|,
\qquad A(R)^w(\lambda i.a).
]

A morphism `f : A → B` is Scott-continuous and uniformly preserves every ground test:

[
\forall R,w,g,
\qquad A(R)^w(g) \Rightarrow B(R)^w(f\circ g).
]

Thus the carrier of an exponential is

[
|B^A| = \operatorname{Hom}_{\mathsf{SR}}(A,B)
]

with pointwise order.

Its relation is

[
\begin{aligned}
(B^A)(R)^w(g) \Longleftrightarrow {}&
\forall(v,\varphi:v\to w),\ \forall h:v\to|A|,\\
& A(R)^v(h) \Rightarrow
B(R)^v\bigl(\lambda i.\,g(\varphi i)(h(i))\bigr).
\end{aligned}
]

Two different universal quantifications are important here:

1. membership in the **arrow carrier** requires preservation of every ground test;
2. membership in the **arrow relation at one test** requires quantification over every future-world reindexing inside that test.

The files prove the closure properties needed for products, exponentials, evaluation, currying, and least fixed points. Term interpretation therefore returns a uniform morphism, not a bare function plus a later unproved relational obligation.

## 3. Finite projections

For ground type,

[
p_{\mathsf{nat}}^n(\bot)=\bot,
\qquad
p_{\mathsf{nat}}^n(\uparrow k)=
\begin{cases}
\uparrow k & k\le n,\\
\bot & k>n.
\end{cases}
]

For arrows,

[
p_{\sigma\to\tau}^n(f)(x)
=
p_\tau^n\bigl(f(p_\sigma^n(x))\bigr).
]

Each projection is denoted by a closed PCF term. The development proves the four structural laws used throughout the argument:

[
p_\tau^n(d)\sqsubseteq d,
]

[
n\le m \Rightarrow p_\tau^n(d)\sqsubseteq p_\tau^m(d),
]

[
p_\tau^m(p_\tau^n(d)) = p_\tau^{\min(m,n)}(d),
]

and

[
\bigsqcup_n p_\tau^n(d)=d.
]

Put

[
D_\tau^n = \{d\in D_\tau \mid p_\tau^n(d)=d\}.
]

For finite-level functions two consequences are isolated explicitly:

[
\boxed{f(p_\sigma^n(x))=f(x)}
\qquad\text{(input absorption)}
]

and

[
\boxed{p_\tau^n(f(x))=f(x)}
\qquad\text{(output fixedness)}.
]

The finite-level sets are proved finite. At arrow type, restriction yields an injection

[
D_{\sigma\to\tau}^n
\hookrightarrow
(D_\sigma^n\to D_\tau^n).
]

No surjectivity claim is needed.

## 4. Strengthened finite definability

The naive closed statement

[
p_\tau^n(d)=d
\Rightarrow
\exists M:\varnothing\vdash\tau,\ \llbracket M\rrbracket=d
]

is too weak to support induction at higher type. The formalisation instead uses a stronger tuple theorem with arbitrary finite environments.

For

[
\Gamma=x_1:\sigma_1,\ldots,x_m:\sigma_m,
]

define the finite-environment world

[
W_{n,\Gamma}
=
D_{\sigma_1}^n\times\cdots\times D_{\sigma_m}^n.
]

The empty context yields a singleton world. World maps are context projections.

Let

[
\iota_\Gamma:W_{n,\Gamma}\to\llbracket\Gamma\rrbracket
]

be componentwise inclusion. Define the selected ground relation by representability:

[
R_n^\Gamma(g)
\Longleftrightarrow
\exists M:\Gamma\vdash\mathsf{nat},
\forall\rho\in W_{n,\Gamma},
\llbracket M\rrbracket(\iota_\Gamma\rho)=g(\rho).
]

The range of `g` is the whole flat natural domain; only the environments are finite-level. Restricting outputs to `D_nat^n` would break closure under successor.

The strong theorem proved by induction on type is, schematically:

[
\boxed{
\operatorname{Rel}_{n,\Gamma,\tau}(g)
\Longleftrightarrow
\exists M:\Gamma\vdash\tau,
\forall\rho,\ \llbracket M\rrbracket(\iota_\Gamma\rho)=g(\rho)
}
]

under the pointwise finite-level condition `p_τ^n(g ρ)=g ρ`.

### Arrow case: related implies representable

Suppose

[
g:W_{n,\Gamma}\to D_{\sigma\to\tau}
]

is related and pointwise fixed. Extend the world by a variable of type `σ`. The tuple

[
h(\rho,a)=a
]

is represented by the newest variable and therefore related by the reverse induction hypothesis.

Apply the arrow relation to `g` and `h`; this produces

[
g'(\rho,a)=g(\rho)(a)
]

at type `τ`. Output fixedness makes `g'` finite-level, so the induction hypothesis yields

[
L:\Gamma,x:\sigma\vdash\tau
]

representing it.

Define

[
Q=\lambda x:\sigma.\,L[x:=P_\sigma^n x].
]

For arbitrary semantic `d`,

[
\begin{aligned}
\llbracket Q\rrbracket(\iota_\Gamma\rho)(d)
&=\llbracket L\rrbracket(\iota_\Gamma\rho,p_\sigma^n(d))\\
&=g(\rho)(p_\sigma^n(d))\\
&=g(\rho)(d),
\end{aligned}
]

where the last step is input absorption. This is equality on the entire semantic function domain, not merely on finite arguments.

### Arrow case: representable implies related

Suppose `M : Γ ⊢ σ → τ` represents a pointwise fixed tuple `g`. Take an arbitrary future world and arbitrary related argument tuple

[
h:W_{n,\Gamma,\Delta}\to D_\sigma.
]

No finite-level assumption is made on `h`.

Project it:

[
k=p_\sigma^n\circ h.
]

Uniformity of the projection preserves relatedness, while idempotence gives pointwise fixedness. The induction hypothesis then provides a term representing `k`. Applying the weakened `M` to that term represents

[
\rho\mapsto
 g(\operatorname{drop}\rho)(p_\sigma^n(h(\rho)))
 =
 g(\operatorname{drop}\rho)(h(\rho)),
]

again by input absorption. The result is pointwise fixed by output fixedness, so the reverse induction hypothesis at `τ` yields relatedness.

The closed finite-definability theorem is recovered from this stronger theorem by using the constant tuple at the singleton empty-context world. **Concreteness is exactly what supplies relatedness of that constant tuple.**

## 5. Explicit separation

To prove reflection of contextual approximation, suppose

[
\llbracket M\rrbracket\not\sqsubseteq\llbracket N\rrbracket.
]

Pointwise order gives an environment witnessing the failure. Unfolding function order repeatedly produces a finite sequence of semantic arguments and a natural `q` such that

[
\llbracket M\rrbracket\rho\,a_1\cdots a_k = \uparrow q,
]

but

[
\llbracket N\rrbracket\rho\,a_1\cdots a_k \ne \uparrow q.
]

Collect the environment and arguments into one product element `z`, and let `z_n` be its componentwise finite projection. Then

[
z_n\sqsubseteq z_{n+1}\sqsubseteq z,
\qquad
\bigsqcup_n z_n=z.
]

Joint continuity of interpretation and evaluation gives

[
\bigsqcup_n F_M(z_n)=F_M(z)=\uparrow q.
]

Compactness of the numeral produces one finite level `n` with

[
F_M(z_n)=\uparrow q.
]

At that **same** level,

[
F_N(z_n)\sqsubseteq F_N(z),
]

so `F_N(z_n) ≠ ↑q`; otherwise flatness would force `F_N(z)=↑q`.

Every coordinate of `z_n` is finite-level fixed, so finite definability supplies closed terms for every environment coordinate and every semantic argument. These terms are assembled into an actual PCF closing context

[
\boxed{
C[-]
=
(\lambda x_1\ldots x_m.\,[-])\,
T_1\cdots T_m\,
U_1\cdots U_k.
}
]

Substitution and interpretation laws give

[
\llbracket C[M]\rrbracket=\uparrow q,
\qquad
\llbracket C[N]\rrbracket\ne\uparrow q.
]

Thus semantic order failure yields an explicit contextual separator. Preservation in the other direction is a structural induction on contexts using monotonicity of every semantic constructor.

## 6. Operational adequacy

The operational layer is proved separately, using call-by-name reduction and the computational logical relation

[
d\triangleleft_{\mathsf{nat}}M
\Longleftrightarrow
\forall n,\ d=\uparrow n\Rightarrow M\Downarrow n,
]

and

[
f\triangleleft_{\sigma\to\tau}M
\Longleftrightarrow
\forall a,N,
\ a\triangleleft_\sigma N
 \Rightarrow
 f(a)\triangleleft_\tau MN.
]

For each term this relation contains bottom and is closed under directed suprema; it is also backward closed under reduction.

The fixed-point case is explicit: from `f △ F`, prove by induction that

[
f^k(\bot)\triangleleft \operatorname{fix}F.
]

The successor step uses

[
\operatorname{fix}F\longrightarrow F(\operatorname{fix}F),
]

and directed closure yields

[
Y(f)\triangleleft\operatorname{fix}F.
]

Together with reduction soundness, this proves ground adequacy:

[
M\Downarrow n
\Longleftrightarrow
\llbracket M\rrbracket=\uparrow n.
]

Combining adequacy with the denotational separator yields operational full abstraction.

## Repository layout

| Files | Contents |
|---|---|
| `OR/Order.lean`, `OR/Flat.lean` | Directed completeness, continuous maps, products, function spaces, joint evaluation, fixed points, flat naturals. |
| `OR/Sequential.lean`, `OR/Worlds.lean` | Elementary sequentiality relations, finite interpolation, primitive-closure characterization, finite-world tests. |
| `OR/SR.lean` | Concrete relational objects, uniform morphisms, products, exponentials, evaluation, currying, fixed points. |
| `OR/Syntax.lean`, `OR/Interpretation.lean` | Intrinsically typed PCF, renaming/substitution, morphism-valued denotational semantics. |
| `OR/Projections.lean`, `OR/FiniteWorlds.lean` | Finite projections, absorption laws, finite images, approximation, selected finite-environment tests. |
| `OR/Definability.lean`, `OR/Compactness.lean` | Strong higher-type definability, closed definability, compactness, definable density/algebraicity. |
| `OR/FullAbstraction.lean` | Typed one-hole contexts, context monotonicity, explicit separation, denotational full abstraction. |
| `OR/Operational.lean`, `OR/Adequacy.lean` | Call-by-name semantics, logical relation, adequacy, operational full abstraction. |
| `OR/Observations.lean`, `OR/Examples.lean` | Numeral/termination observations and regression examples, including exclusion of parallel-or. |
| `OR/AxiomAudit.lean` | Selected theorem axiom inspection. |
| `PROOF_MAP.md` | Dependency/proof map. |
| `THEOREM_INDEX.md` | Named theorem inventory. |
| `SOURCES.md` | Source references used while drafting. |

## Build and validation

The project currently targets Lean/Mathlib `v4.19.0`, as pinned in `lean-toolchain` and `lakefile.toml`.

```sh
lake update
lake exe cache get
lake build
lake env lean OR/AxiomAudit.lean
```

Or run the combined checks:

```sh
bash scripts/check.sh
```

The source-level audit rejects `sorry`, `admit`, custom `axiom` declarations, `unsafe`, and `native_decide`, checks the local import graph, and inventories declarations. It is **not** a substitute for elaboration and kernel checking.

The intended validation discipline is:

1. repair compile errors in dependency order;
2. do not weaken the relational carrier or observation relation to make proofs go through;
3. do not replace finite definability, separation, or adequacy by assumptions;
4. after `lake build` succeeds, run `OR/AxiomAudit.lean` and inspect the transitive theorem dependencies.

In particular, a successful repair should preserve these semantic invariants:

- `pred zero` diverges;
- arrows are uniform continuous morphisms;
- the selected finite test restricts environments, not outputs;
- strong definability quantifies over arbitrary contexts/tuples;
- reverse arrow definability first projects an arbitrary related argument tuple;
- the separation proof uses one common finite approximation index on both sides.
