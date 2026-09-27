import OR.Projections
import OR.Sieber.Model

/-!
# Boolean Sieber model and level 1 of the natural-number model

Proof skeleton for the bridge needed in `SIEBER.md`, Section 4.

There are two distinct type languages in the repository:

* `OR.Sieber.Ty`, for finitary Boolean PCF;
* `OR.Ty`, for PCF over `ℕ⊥`.

`natTy` translates the former into the latter.  The intended result is that
Sieber's ordinary Boolean carrier at `τ` is isomorphic to the level-1 fixed
points of the natural-number projection at `natTy τ`.

The proofs are intentionally left as `sorry`: this file fixes the definitions,
interfaces and proof obligations for a Lean-enabled follow-up.

Important: this file does *not* identify `Sieber.Test` with the Kripke
`OR.Test`.  The carrier equivalence and the compatibility of ordinary
single-world relations should be proved as separate statements.
-/

set_option autoImplicit false

noncomputable section

namespace OR.Sieber.LevelOne

namespace S := OR.Sieber

/-- Translate Boolean-PCF types to natural-number PCF types. -/
def natTy : S.Ty → OR.Ty
  | .B => .nat
  | .arr σ τ => .arr (natTy σ) (natTy τ)

@[simp] theorem natTy_B : natTy .B = .nat := rfl
@[simp] theorem natTy_arr (σ τ : S.Ty) :
    natTy (σ ⇒ τ) = (natTy σ ⇒ natTy τ) := rfl

/-- Boolean ground values embedded in level 1 of `ℕ⊥`.
    Convention: `tt ↦ 0`, `ff ↦ 1`. -/
def valToLevel : S.Val → OR.Level .nat 1
  | .bot => ⟨.bot, by simp [OR.projection_nat, OR.Ground.cut]⟩
  | .tt  => ⟨.val 0, by simp [OR.projection_nat, OR.Ground.cut]⟩
  | .ff  => ⟨.val 1, by simp [OR.projection_nat, OR.Ground.cut]⟩

/-- Every level-1 natural is one of bottom, zero, or one. -/
def levelToVal : OR.Level .nat 1 → S.Val := by
  intro x
  -- Use `OR.finite_nat_bound x`: if `x.val = .val k`, then `k ≤ 1`.
  sorry

@[simp] theorem levelToVal_valToLevel (v : S.Val) :
    levelToVal (valToLevel v) = v := by
  sorry

@[simp] theorem valToLevel_levelToVal (x : OR.Level .nat 1) :
    valToLevel (levelToVal x) = x := by
  sorry

/--
Embedding of Sieber's Boolean carrier into the level-1 natural carrier.

At arrow type the underlying natural function should be the extension
`x ↦ toLevel (f (fromLevel (ψ¹ x)))`.  Equivalently, once the induction
hypothesis is available, extend the function from level-1 inputs and make it
absorb `projection _ 1` on arbitrary inputs.

The main proof obligation is that this extension is an element of the
*ordinary Sieber* natural carrier / the corresponding uniform carrier used by
`D`; do not silently assume that every monotone finite table belongs to `D`.
-/
def toLevel : (τ : S.Ty) → S.SieberBool τ → OR.Level (natTy τ) 1 := by
  intro τ
  induction τ with
  | B =>
      exact valToLevel
  | arr σ ρ ihσ ihρ =>
      intro f
      -- Construct a natural semantic arrow, prove uniformity, then prove it is
      -- fixed by `OR.projection (natTy (σ ⇒ ρ)) 1`.
      sorry

/--
Restriction of a level-1 natural element to the Boolean carrier.

For arrows use `OR.finite_input_absorption` and
`OR.finite_output_fixed`: a level-1 function is determined by level-1 inputs
and produces level-1 outputs.
-/
def fromLevel : (τ : S.Ty) → OR.Level (natTy τ) 1 → S.SieberBool τ := by
  intro τ
  induction τ with
  | B =>
      exact levelToVal
  | arr σ ρ ihσ ihρ =>
      intro f
      -- Restrict `f.val` to inputs in the image of `toLevel`; use
      -- `finite_output_fixed` to package the result at level 1, and prove
      -- monotonicity + preservation of every Boolean Sieber test.
      sorry

@[simp] theorem fromLevel_toLevel :
    ∀ (τ : S.Ty) (x : S.SieberBool τ), fromLevel τ (toLevel τ x) = x := by
  intro τ
  induction τ with
  | B =>
      exact levelToVal_valToLevel x
  | arr σ ρ ihσ ihρ =>
      -- Extensionality, then the induction hypotheses.
      sorry

@[simp] theorem toLevel_fromLevel :
    ∀ (τ : S.Ty) (x : OR.Level (natTy τ) 1), toLevel τ (fromLevel τ x) = x := by
  intro τ
  induction τ with
  | B =>
      exact valToLevel_levelToVal x
  | arr σ ρ ihσ ihρ =>
      -- Extensionality on arbitrary natural inputs.  Reduce the input with
      -- `OR.finite_input_absorption x.property`, then use the induction
      -- hypotheses and `OR.finite_output_fixed x.property`.
      sorry

/-- The carrier-level equivalence central to the transfer argument. -/
def carrierEquiv (τ : S.Ty) : S.SieberBool τ ≃ OR.Level (natTy τ) 1 where
  toFun := toLevel τ
  invFun := fromLevel τ
  left_inv := fromLevel_toLevel τ
  right_inv := toLevel_fromLevel τ

/-! ## Order compatibility -/

/-- The equivalence preserves the intrinsic orders. -/
theorem toLevel_le_iff {τ : S.Ty} (x y : S.SieberBool τ) :
    (S.Model τ).le x y ↔ (toLevel τ x).val ≤ (toLevel τ y).val := by
  sorry

/-! ## Projection characterization -/

/--
The inclusion/retraction induced by `carrierEquiv` is exactly the existing
level-1 projection.

This formulation avoids introducing a second independently defined `i ∘ r`.
-/
theorem projection_one_characterization (τ : S.Ty) (d : OR.D (natTy τ)) :
    OR.projection (natTy τ) 1 d =
      (toLevel τ (fromLevel τ
        ⟨OR.projection (natTy τ) 1 d, OR.projection_idem (natTy τ) 1 d⟩)).val := by
  -- Follows immediately from `toLevel_fromLevel` on the projected element.
  sorry

/-! ## Compactness consequence -/

/--
Any element in the Boolean image is compact in the natural model.

The exact repository notion of compactness should replace this proposition if
one is introduced.  For now the statement spells out the directed-set property
needed by Milner's compact-definability theorem.
-/
def CompactAt {α : Type} [PartialOrder α] [DComplete α] (x : α) : Prop :=
  ∀ (s : Set α) (hs : Dir s), x ≤ dSup s hs → ∃ y ∈ s, x ≤ y

theorem toLevel_compact (τ : S.Ty) (x : S.SieberBool τ) :
    CompactAt (toLevel τ x).val := by
  -- Apply `projection _ 1` to a directed supremum.  Its image lies in the
  -- finite type `Level (natTy τ) 1`, hence the projected directed set has a
  -- greatest member.  Use `projection_le`.
  sorry

/-!
## Relational compatibility still required

The carrier equivalence above is only useful for the open problem after proving
that it is the restriction of the *ordinary single-world Sieber construction*
over `ℕ⊥`, not merely a set/order coincidence.

The natural-number development represents ground sequentiality relations
through `OR.Test` / `KRel`, whereas the Boolean development represents an
ordinary test directly as `S.Test w`.  Do not identify these types.

A follow-up file should define an ordinary natural test corresponding to
`d : S.Test w` and prove, simultaneously on `τ`, that related Boolean tuples
correspond exactly to related level-1 natural tuples.  The target mathematical
statement is:

  R^B_τ(g) ↔ R^N_{natTy τ}(toLevel ∘ g)

for the same finite intersection of elementary `S^w_{A,B}` relations.

That theorem supplies the uniformity obligations in `toLevel` and
`fromLevel`, and is the key semantic lemma connecting the two models.
-/

end OR.Sieber.LevelOne
