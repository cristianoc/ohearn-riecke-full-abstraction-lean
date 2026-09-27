# Proof map and representation choices

All references below identify attempted Lean proofs. This map does not certify
that the scripts elaborate.

## The closing dependency chain

```text
nonempty-directed order theory
    → flat ground domain and finite-arity stabilization
    → elementary sequentiality / finite interpolation
    → syntax-independent ground tests
    → concrete relational objects and uniform exponentials
    → PCF morphism-valued interpretation
    → definable projections and their finite images
    → selected finite-environment test
    → strong finite definability
    → closed finite definability
    → explicit semantic separation
    → denotational full abstraction

independent PCF reduction + interpretation
    → reduction soundness
    → bottom/admissibility/backward closure of Comp
    → fundamental computational logical relation
    → ground adequacy

full abstraction + adequacy
    → operational full abstraction
    → equality corollary
    → termination-only observation equivalence
```

`OR/Examples.lean` is downstream of these proofs, not an assumption used by them.

## Correspondence to the earlier specification

| Specification | Source implementation |
|---|---|
| D1–D2; L1–L5 | `DComplete`, `dSup`, `CMap`, product/Pi/subtype instances, `CMap.pointSup`, `CMap.eval`, `lfp`. Directed-supremum interchange is replaced by explicit upper-bound proofs inside `pointSup` and `eval`; no interchange theorem is assumed. |
| D3; L6 | `Flat`, its `DComplete` instance, `Stabilizing`, and `stabilizingPi`. |
| D4; L7–L9 | `Elementary`, `Elementary.primitiveClosed`, `Ground.casesUpTo`, `finite_interpolation`, `sequential_iff_primitive_closed`. |
| D5–D7 | `Test`, `KRel`, `Test.groundRel`. The world-coding construction is replaced by the explicit universe arrangement below. |
| D8–D11; L10–L14 | `Obj`, `Uniform`, `Hom`, `Obj.one/prod/arr/nat`, homspace completeness, curry/evaluation laws, global elements, `Hom.fixMap`, `typeObj`. |
| D12–D14; L15–L17 | `Var`, `Tm`, `Ren`, `Sub`, their administrative laws, `Env`, `denote`, `denote_rename`, `denote_subst`, `denote_apply_close`. |
| D15–D16; L18–L21 | `projectionTerm`, `projection`, `projection_comp`, `projection_approximates`, both absorption laws, `Level`, `finite_level`, environment projections. |
| D17–D19; L22–L24 | `FEnv`, `finiteTest`, `Def`, `Rel`, `rel_nat`, `rel_arr`. No encode/decode maps are required by the selected representation. |
| D20; L25–L27 | `Fixed`, `strong_finite_definability`, `finite_definability`, `definable_density`. |
| L28 | `finite_level_compact`, `compact_iff_finite_level`, `compact_definability`, `algebraic_definable`. |
| D21–D23; L29–L32 | `PCtx`, all context constructors, `PCtx.denote_mono`, `PCtx.closing`, `closed_separator`, `semantic_separator`. Explicit spine data are replaced by induction on the result type. |
| T1; C1 | `full_abstraction_den`, `full_abstraction_den_eq`. |
| D24–D25; L33–L36 | `Step`, `Red`, `Eval`, their soundness theorems, `Comp`, `Comp.bottom/dsup/backward`, `fundamental`. |
| D26; T2–T3 | `adequacy`, `ContextualOpLE`, `ContextualOpEq`, `full_abstraction_op`, `full_abstraction_op_eq`. |

## 1. Universes instead of world encodings

`Test` contains a small world type and a finite small element type at each world:

```lean
structure Test where
  World : Type
  El : World → Type
  finite : ∀ w, Finite (El w)
  -- remaining ground-relation and reindexing fields
```

Consequently `Test` itself is in `Type 1`. `Domain.Carrier` is in `Type 0`.
The condition that a continuous map preserves every test is a proposition,
so universal quantification over `Test` does not raise the universe of the
subtype of maps. Thus `Hom A B` remains a small carrier usable at the next
PCF arrow type.

The test type is defined before PCF syntax and before relational objects.
The later `finiteTest n` is just one inhabitant of that previously defined type.
Its worlds are actual typed contexts; contexts with equally many finite
environments are not identified.

No resizing axiom, quotient by contextual equivalence, or assumed universe
encoding theorem is introduced.

## 2. All renamings in the selected test

The selected finite test has arrows induced by **all type-preserving renamings**,
not only prefix projections. Its ground relation is preserved by every such
arrow because syntactic renaming commutes with interpretation.

Weakening is one of these arrows, so the forward arrow step of strong
finite definability uses the same context extension as the specification.
In the reverse step, the representing function term is renamed along the
arbitrary test arrow before applying the representing argument term.

`rel_arr` exposes the exact universal quantifier used in this induction.

## 3. The higher-type definability proof

For a tuple fixed at level `n`, the forward arrow proof extends the context by
one variable, applies the relational tuple to that variable, and uses the
codomain induction hypothesis. The resulting lambda substitutes the domain
projection for the newest variable. `finite_input_absorption` proves agreement
at every semantic argument, not just at finite-level arguments.

Conversely, a representing function is tested against an arbitrary related
argument tuple in any renaming world. The argument tuple is first projected.
`rel_projection` supplies relatedness; idempotence supplies fixedness. The
domain induction hypothesis then supplies its representing term. Input
absorption removes the projection, and output fixedness makes the codomain
induction hypothesis applicable.

The closed theorem uses the constant tuple at the singleton empty-context
world. Relatedness comes from the **concreteness** field proved for the
constructed type objects.

## 4. Separation without a separate spine datatype

For closed terms, `closed_separator` inducts on their type. At an arrow type,
pointwise order failure supplies one semantic argument. The generic theorem
`Chain.failure_at_finite_stage` supplies a common finite approximation at which
failure persists. That approximation is definable, so the induction continues
at the codomain with an actual closed argument term.

For open terms, `semantic_separator` first performs the same common-index
approximation on the environment. A closed substitution represents the finite
environment. `PCtx.closing` is an actual syntactic context built by abstraction
and application—not an assumed substitution closure principle. The closed
separator is then composed with it.

## 5. Operational adequacy is independent

`Step` and `Eval` are defined from syntax, without referring to denotation.
`Comp` is a separate semantic/syntactic logical relation. In the fixed-point
case of `fundamental`, every finite semantic iterate is related to the same
syntactic fixed-point term; the induction step uses one operational unfolding
and backward closure. Directed admissibility passes to the least fixed point.

The final observation bridge does not assume a context lemma or a CIU theorem.

## 6. Regression obligations

The examples check the two projection boundary equations, predecessor-zero
and fixed-point divergence, the singleton empty context, unbounded selected-test
outputs, beta/eta/fixed-point contextual equations, and the exclusion of a
parallel-or behavior by a nontrivial three-coordinate relation.

The no-parallel-or theorem is a regression for the **uniform arrow carrier**.
It would be false for the ordinary full Scott-continuous function space.

## Scope

The target is the relational model, finite definability, and full abstraction,
with the operational bridge and the consequences listed above. Historical
comparisons, a separate game model, and Milner's independent uniqueness theorem
are not claimed as additional formalized results.
