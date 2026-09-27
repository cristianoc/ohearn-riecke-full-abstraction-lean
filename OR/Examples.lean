import OR.Observations
import OR.Compactness

/-!
# Regression theorems

These are intended to be built with the main development. Besides syntax and
projection boundary checks, `no_parallel_or` exercises a genuinely nontrivial
three-coordinate test, guarding against replacement of the uniform arrow
carrier by the full continuous function space.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR
namespace Examples

 theorem pred_zero_diverges (n : ℕ) : ¬ Eval (.pred .zero) n := by
  intro h
  have hd := h.sound
  change (Flat.bot : Ground) = .val n at hd
  cases hd

 theorem omega_diverges (n : ℕ) : ¬ Eval (Tm.omega .nat) n := by
  intro h
  have hd := h.sound
  simp only [denoteClosed, denote_omega] at hd
  change (Flat.bot : Ground) = .val n at hd
  cases hd

 theorem empty_context_world_unique (n : ℕ) (ρ : (finiteTest n).El []) :
    ρ = PUnit.unit :=
  @Subsingleton.elim PUnit inferInstance ρ PUnit.unit

 theorem projection_includes_boundary (n : ℕ) :
    projection .nat n (.val n) = .val n := by
  simp [projection_nat, Ground.cut]

 theorem projection_excludes_next (n : ℕ) :
    projection .nat n (.val (n + 1)) = .bot := by
  simp [projection_nat, Ground.cut]

/-- Finite environments do not impose a finite range on the selected ground test. -/
 theorem ground_test_has_unbounded_outputs (n k : ℕ) (Γ : Ctx) :
    (finiteTest n).ground Γ (fun _ => .val k) := by
  refine ⟨Tm.numeral k, ?_⟩
  intro ρ
  exact denote_numeral k (includeEnv ρ)

 theorem beta_valid {Γ : Ctx} {σ τ : Ty} (M : Tm (σ :: Γ) τ) (N : Tm Γ σ) :
    ContextualOpEq (.app (.lam M) N) (Tm.subst (Sub.single N) M) := by
  apply (full_abstraction_op_eq _ _).mpr
  apply Hom.ext
  intro ρ
  exact denote_beta M N ρ

 theorem eta_valid {Γ : Ctx} {σ τ : Ty} (M : Tm Γ (σ ⇒ τ)) :
    ContextualOpEq (.lam (.app (Tm.rename Ren.wk M) (.var .vz))) M := by
  apply (full_abstraction_op_eq _ _).mpr
  apply Hom.ext
  intro ρ
  apply Hom.ext
  intro a
  simp only [denote_lam, denote_app, denote_rename, pull_wk, denote_var, lookup]

 theorem fix_unfold_valid {Γ : Ctx} {τ : Ty} (M : Tm Γ (τ ⇒ τ)) :
    ContextualOpEq (.fix M) (.app M (.fix M)) := by
  apply (full_abstraction_op_eq _ _).mpr
  apply Hom.ext
  intro ρ
  exact (Hom.fixMap_unfold (typeObj τ) (denote M ρ)).symm

 def porA : Finset (Fin 3) := {0, 1}
 def porB : Finset (Fin 3) := {0, 1, 2}

 theorem por_subset : porA ⊆ porB := by decide

/-- One finite world; its only reindexing is the identity. -/
 def porTest : Test where
  World := PUnit
  El := fun _ => Fin 3
  finite _ := inferInstance
  Hom φ := φ = (fun i => i)
  identity _ := rfl
  composition := by
    intro u v w φ ψ hφ hψ
    subst φ
    subst ψ
    rfl
  ground _ := Elementary porA porB
  ground_bottom _ := (Elementary.primitiveClosed por_subset).bottom
  ground_sup _ s hs h := h _ (Stabilizing.sup_mem (α := Fin 3 → Ground) s hs)
  reindex := by
    intro v w φ hφ g hg
    subst φ
    exact hg
  sequential _ :=
    (sequential_iff_primitive_closed (Elementary porA porB)).mpr
      (Elementary.primitiveClosed por_subset)

 def porLeft : Fin 3 → Ground := ![.val 0, .bot, .val 1]
 def porRight : Fin 3 → Ground := ![.bot, .val 0, .val 1]

 theorem porLeft_related : Obj.nat.R porTest PUnit.unit porLeft := by
  left
  exact ⟨1, by decide, rfl⟩

 theorem porRight_related : Obj.nat.R porTest PUnit.unit porRight := by
  left
  exact ⟨0, by decide, rfl⟩

/-- The uniform semantic carrier excludes the characteristic parallel-or equations. -/
 theorem no_parallel_or (p : D (.nat ⇒ .nat ⇒ .nat))
    (hl : p (.val 0) .bot = .val 0)
    (hr : p .bot (.val 0) = .val 0)
    (hb : p (.val 1) (.val 1) = .val 1) : False := by
  have hp := p.uniform porTest PUnit.unit porLeft porLeft_related
  have hout := hp PUnit.unit (fun i => i) rfl porRight porRight_related
  change Elementary porA porB (fun i => p (porLeft i) (porRight i)) at hout
  rcases hout with ⟨i, hi, hbot⟩ | hconst
  · have hi' : i = 0 ∨ i = 1 := by
      simpa only [porA, Finset.mem_insert, Finset.mem_singleton] using hi
    rcases hi' with rfl | rfl
    · simpa [porLeft, porRight, hl] using hbot
    · simpa [porLeft, porRight, hr] using hbot
  · have h := hconst 0 (by decide) 2 (by decide)
    simpa [porLeft, porRight, hl, hb] using h

end Examples
end OR
