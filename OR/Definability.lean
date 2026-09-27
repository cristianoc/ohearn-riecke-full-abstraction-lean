import OR.FiniteWorlds

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

noncomputable section

namespace OR

 def Fixed {ι : Type} (n : ℕ) (τ : Ty) (g : ι → D τ) : Prop :=
  ∀ i, projection τ n (g i) = g i

 def projectLastSub {Γ : Ctx} (n : ℕ) (σ : Ty) : Sub (σ :: Γ) (σ :: Γ)
  | _, .vz => .app (Tm.closed (projectionTerm σ n)) (.var .vz)
  | _, .vs x => .var (.vs x)

 theorem subenv_projectLast {Γ : Ctx} (n : ℕ) (σ : Ty) (ρ : Env Γ) (a : D σ) :
    subenv (projectLastSub n σ) (ρ, a) = (ρ, projection σ n a) := by
  apply env_ext
  intro τ x
  rw [lookup_subenv]
  cases x with
  | vz =>
      simp only [projectLastSub, denote_app, denote_closed, denote_var, lookup] <;> rfl
  | vs x =>
      simp only [projectLastSub, denote_var, lookup]

/--
The strengthened definability theorem. Both implications are proved together,
with arbitrary contexts and arbitrary related argument tuples in the arrow case.
-/
 theorem strong_finite_definability (n : ℕ) : ∀ (τ : Ty) (Γ : Ctx)
    (g : FEnv n Γ → D τ), Fixed n τ g → (Rel n Γ τ g ↔ Def n Γ τ g) := by
  intro τ
  induction τ with
  | nat =>
      intro Γ g _
      exact rel_nat n Γ g
  | arr σ τ ihσ ihτ =>
      intro Γ g hfixed
      constructor
      · intro hg
        let argument : FEnv n (σ :: Γ) → D σ := fun ρ => ρ.2.val
        have hargFixed : Fixed n σ argument := fun ρ => ρ.2.property
        have hargDef : Def n (σ :: Γ) σ argument := ⟨.var .vz, fun _ => rfl⟩
        have hargRel : Rel n (σ :: Γ) σ argument :=
          (ihσ (σ :: Γ) argument hargFixed).mpr hargDef
        let body : FEnv n (σ :: Γ) → D τ := fun ρ => g ρ.1 ρ.2.val
        have hbodyRel : Rel n (σ :: Γ) τ body := by
          have e : Extension Γ (σ :: Γ) := .cons σ (.refl Γ)
          have h := (rel_arr n Γ σ τ g).mp hg (σ :: Γ) e argument hargRel
          simpa only [Extension.ren_cons, Extension.ren_refl, Ren.comp, Ren.wk, fpull_wk] using h
        have hbodyFixed : Fixed n τ body :=
          fun ρ => finite_output_fixed (hfixed ρ.1) ρ.2.val
        obtain ⟨L, hL⟩ := (ihτ (σ :: Γ) body hbodyFixed).mp hbodyRel
        refine ⟨.lam (Tm.subst (projectLastSub n σ) L), ?_⟩
        intro ρ
        apply Hom.ext
        intro d
        rw [denote_lam, denote_subst, subenv_projectLast]
        let a : Level σ n := ⟨projection σ n d, projection_idem σ n d⟩
        have hrep := hL (ρ, a)
        change denote L (includeEnv ρ, projection σ n d) = g ρ (projection σ n d) at hrep
        exact hrep.trans (finite_input_absorption (hfixed ρ) d)
      · rintro ⟨M, hM⟩
        apply (rel_arr n Γ σ τ g).mpr
        intro Δ e h hh
        -- `h` is not assumed to be finite-level. Project it before using the IH.
        let k : FEnv n Δ → D σ := fun ρ => projection σ n (h ρ)
        have hkRel : Rel n Δ σ k := rel_projection hh
        have hkFixed : Fixed n σ k := fun ρ => projection_idem σ n (h ρ)
        obtain ⟨N, hN⟩ := (ihσ Δ k hkFixed).mp hkRel
        let out : FEnv n Δ → D τ := fun ρ => g (fpull Extension.ren e ρ) (h ρ)
        have houtFixed : Fixed n τ out :=
          fun ρ => finite_output_fixed (hfixed (fpull Extension.ren e ρ)) (h ρ)
        apply (ihτ Δ out houtFixed).mpr
        refine ⟨.app (Tm.rename Extension.ren e M) N, ?_⟩
        intro ρ
        rw [denote_app, denote_rename, ← includeEnv_fpull, hM, hN]
        exact finite_input_absorption (hfixed (fpull Extension.ren e ρ)) (h ρ)

/-- The empty context is a singleton world; concreteness supplies its constant tuple. -/
 theorem finite_definability (τ : Ty) (n : ℕ) (d : D τ)
    (hd : projection τ n d = d) : ∃ M : Tm [] τ, denoteClosed M = d := by
  have hr : Rel n [] τ (fun _ => d) := rel_constant n [] τ d
  obtain ⟨M, hM⟩ := (strong_finite_definability n τ [] (fun _ => d) (fun _ => hd)).mp hr
  exact ⟨M, hM PUnit.unit⟩

 theorem approximant_definable (τ : Ty) (n : ℕ) (d : D τ) :
    ∃ M : Tm [] τ, denoteClosed M = projection τ n d :=
  finite_definability τ n _ (projection_idem τ n d)

/-- One coherent sequence of syntactic representatives of every semantic element. -/
 theorem definable_density (τ : Ty) (d : D τ) :
    ∃ M : ℕ → Tm [] τ,
      (∀ n, denoteClosed (M n) = projection τ n d) ∧
      Monotone (fun n => denoteClosed (M n)) ∧
      ∃ h : Monotone (fun n => denoteClosed (M n)),
        (Chain.mk (fun n => denoteClosed (M n)) h).sup = d := by
  choose M hM using (fun n => approximant_definable τ n d)
  have hmono : Monotone (fun n => denoteClosed (M n)) := by
    intro n m hnm
    change denoteClosed (M n) ≤ denoteClosed (M m)
    rw [hM n, hM m]
    exact projection_index_mono τ d hnm
  refine ⟨M, hM, hmono, hmono, ?_⟩
  have hc : (Chain.mk (fun n => denoteClosed (M n)) hmono) = projectionChain τ d :=
    Chain.ext hM
  rw [hc, projection_approximates]

/-- Closed substitutions representing arbitrary finite semantic environments. -/
 theorem finite_environment_definability (n : ℕ) (Γ : Ctx) (ρ : FEnv n Γ) :
    ∃ θ : Sub Γ [], subenv θ PUnit.unit = includeEnv ρ := by
  let θ : Sub Γ [] := fun {τ} x =>
    Classical.choose (finite_definability τ n (flookup x ρ).val (flookup x ρ).property)
  refine ⟨θ, ?_⟩
  apply env_ext
  intro τ x
  rw [lookup_subenv, lookup_includeEnv]
  exact Classical.choose_spec (finite_definability τ n (flookup x ρ).val (flookup x ρ).property)

end OR
