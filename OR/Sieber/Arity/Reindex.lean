import OR.Sieber.Model

/-!
# Ground reindexing of Sieber tests

`ARITY.md` §2.1, Lemma R1, and the composition identity used in `R7.md`, Lemma M2.

For a map `π : Fin w → Fin k`, the pullback of a relation `R` on `w`-tuples is
`π^* R = {x : Fin k → α | x ∘ π ∈ R}`.

* `Elem.pullback` (R1): `π^* S^w_{A,B} = S^k_{π(A),π(B)}`, and `π(A) ⊆ π(B)` when `A ⊆ B`.
* `Test.holds_pullback` (corollary): the pullback of the relation denoted by a test `d`
  is the relation denoted by the test `d.pullback π`.
* `pullback_comp`, `Test.holds_pullback_comp` (M2): `σ^* (ρ^* R) = (σ ∘ ρ)^* R`.
-/

set_option autoImplicit false

namespace OR.Sieber

/-- The pullback `π^* R = {x | x ∘ π ∈ R}` of a relation on `w`-tuples along `π : w → k`. -/
def pullback {α : Type*} {w k : ℕ} (π : Fin w → Fin k) (R : (Fin w → α) → Prop) :
    (Fin k → α) → Prop :=
  fun x => R (x ∘ π)

/-- Pullback composes contravariantly: `σ^* (ρ^* R) = (σ ∘ ρ)^* R`. -/
theorem pullback_comp {α : Type*} {w m k : ℕ} (ρ : Fin w → Fin m) (σ : Fin m → Fin k)
    (R : (Fin w → α) → Prop) :
    pullback σ (pullback ρ R) = pullback (σ ∘ ρ) R :=
  rfl

/-- Lemma R1: `π^* S^w_{A,B} = S^k_{π(A),π(B)}`. -/
theorem Elem.pullback {w k : ℕ} (π : Fin w → Fin k) (A B : Finset (Fin w)) :
    OR.Sieber.pullback π (Elem A B) = Elem (A.image π) (B.image π) := by
  funext x
  simp only [OR.Sieber.pullback, Elem, Function.comp_apply, Finset.mem_image,
    exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- The pair `(π(A), π(B))` satisfies the side condition of a test when `(A, B)` does. -/
theorem image_subset_image_of_subset {w k : ℕ} (π : Fin w → Fin k) {A B : Finset (Fin w)}
    (hAB : A ⊆ B) : A.image π ⊆ B.image π :=
  Finset.image_subset_image hAB

/-- The pullback of a test: each pair `(A, B)` with `A ⊆ B` becomes `(π(A), π(B))`. -/
def Test.pullback {w k : ℕ} (π : Fin w → Fin k) (d : Test w) : Test k :=
  (d.filter (fun p => p.1 ⊆ p.2)).image (fun p => (p.1.image π, p.2.image π))

/-- Corollary of R1: the pullback of a test is a test, `π^* d = d.pullback π`. -/
theorem Test.holds_pullback {w k : ℕ} (π : Fin w → Fin k) (d : Test w) :
    OR.Sieber.pullback π d.holds = (d.pullback π).holds := by
  funext x
  apply propext
  constructor
  · intro h q hq _
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hpd, hAB⟩ := Finset.mem_filter.mp hp
    have := h p hpd hAB
    rwa [← Elem.pullback]
  · intro h p hpd hAB
    have hq : (p.1.image π, p.2.image π) ∈ d.pullback π :=
      Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hpd, hAB⟩, rfl⟩
    have := h _ hq (image_subset_image_of_subset π hAB)
    rwa [← Elem.pullback] at this

/-- The composition identity of M2 on tests: `σ^* (ρ^* d) = (σ ∘ ρ)^* d`. -/
theorem Test.holds_pullback_comp {w m k : ℕ} (ρ : Fin w → Fin m) (σ : Fin m → Fin k)
    (d : Test w) :
    ((d.pullback ρ).pullback σ).holds = (d.pullback (σ ∘ ρ)).holds := by
  rw [← Test.holds_pullback, ← Test.holds_pullback, ← Test.holds_pullback, pullback_comp]

end OR.Sieber
