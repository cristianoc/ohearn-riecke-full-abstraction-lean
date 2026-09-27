import OR.Sieber.Model

/-!
# Soundness facts about Sieber's model

* `Tm.obs_eq_den`: Sieber's model observes closed ground terms exactly as the
  standard model does (a logical relation between the two models).
* `finite_car`: every carrier is finite.
* `separate`: distinct elements are separated by an element of type `τ ⇒ B`.
* `universal_fully_abstract`: if every element is definable, observational
  equivalence coincides with equality of denotations.
-/

set_option autoImplicit false

namespace OR.Sieber

/-! ## Agreement with the standard model -/

def Agree : (τ : Ty) → (Model τ).car → Std τ → Prop
  | .B, a, x => a = x
  | .arr σ τ, f, g => ∀ a x, Agree σ a x → Agree τ (f.1 a) (g x)

def EnvAgree : (Γ : Ctx) → Env Γ → StdEnv Γ → Prop
  | [], _, _ => True
  | σ :: Γ, ρ, η => EnvAgree Γ ρ.1 η.1 ∧ Agree σ ρ.2 η.2

theorem Var.agree : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) (η : StdEnv Γ),
    EnvAgree Γ ρ η → Agree τ (x.sem.1 ρ) (x.std η)
  | _ :: _, _, .vz, _, _, h => h.2
  | _ :: _, _, .vs x, _, _, h => Var.agree x _ _ h.1

theorem Tm.agree : ∀ {Γ : Ctx} {τ : Ty} (M : Tm Γ τ) (ρ : Env Γ) (η : StdEnv Γ),
    EnvAgree Γ ρ η → Agree τ (M.sem.1 ρ) (M.std η)
  | _, _, .var x, ρ, η, h => by simp only [Tm.sem, Tm.std]; exact Var.agree x ρ η h
  | _, .arr _ _, .lam M, ρ, η, h => by
      simp only [Tm.sem, Tm.std]
      exact fun a x hax => Tm.agree M (ρ, a) (η, x) ⟨h, hax⟩
  | _, _, .app M N, ρ, η, h => by
      simp only [Tm.sem, Tm.std]
      exact Tm.agree M ρ η h _ _ (Tm.agree N ρ η h)
  | _, _, .tt, _, _, _ => by simp only [Tm.sem, Tm.std, constSem]; rfl
  | _, _, .ff, _, _, _ => by simp only [Tm.sem, Tm.std, constSem]; rfl
  | _, _, .bot, _, _, _ => by simp only [Tm.sem, Tm.std, constSem]; rfl
  | _, _, .ite C M N, ρ, η, h => by
      have hC : C.sem.1 ρ = C.std η := Tm.agree C ρ η h
      have hM : M.sem.1 ρ = M.std η := Tm.agree M ρ η h
      have hN : N.sem.1 ρ = N.std η := Tm.agree N ρ η h
      simp only [Tm.sem, Tm.std]
      show Val.ite (C.sem.1 ρ) (M.sem.1 ρ) (N.sem.1 ρ) = Val.ite (C.std η) (M.std η) (N.std η)
      rw [hC, hM, hN]

/-- Sieber's model and the standard model observe closed ground terms identically. -/
theorem Tm.obs_eq_den (M : Tm [] .B) : M.obs = M.den :=
  (Tm.agree M PUnit.unit PUnit.unit trivial).symm

/-! ## Finiteness -/

theorem finite_car : ∀ τ : Ty, Finite (Model τ).car
  | .B => (inferInstance : Finite Val)
  | .arr σ τ => by
      haveI := finite_car σ
      haveI := finite_car τ
      exact Subtype.finite

/-! ## Separation and full abstraction under universality -/

/-- Distinct elements are separated by an element of type `τ ⇒ B`. -/
theorem separate : ∀ (τ : Ty) (x y : SieberBool τ), x ≠ y →
    ∃ t : SieberBool (τ ⇒ .B), t.1 x ≠ t.1 y
  | .B, x, y, hxy =>
      ⟨⟨fun a => a, fun _ _ h => h, fun _ _ _ h => h⟩, hxy⟩
  | .arr σ ρ, x, y, hxy => by
      have hex : ∃ a, x.1 a ≠ y.1 a := by
        by_contra hall
        push_neg at hall
        exact hxy (Subtype.ext (funext hall))
      obtain ⟨a, ha⟩ := hex
      obtain ⟨t, ht⟩ := separate ρ _ _ ha
      refine ⟨⟨fun f => t.1 (f.1 a), fun f g hfg => t.2.1 _ _ (hfg a), fun w d F hF =>
        t.2.2 w d _ (hF (fun _ => a) (Model.concrete σ w d a))⟩, ht⟩

theorem Tm.den_app {σ τ : Ty} (K : Tm [] (σ ⇒ τ)) (M : Tm [] σ) :
    (Tm.app K M).den = K.den.1 M.den := by simp only [Tm.den, Tm.sem]

/-- **Universality gives full abstraction**: if every element of Sieber's model is
definable, observational equivalence is equality of denotations. -/
theorem universal_fully_abstract (U : Universal) {τ : Ty} (M N : Tm [] τ) :
    ObsEquiv M N ↔ M.den = N.den := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨t, ht⟩ := separate τ _ _ hne
    obtain ⟨K, hK⟩ := U _ t
    have hobs := h K
    rw [Tm.obs_eq_den, Tm.obs_eq_den, Tm.den_app, Tm.den_app, hK] at hobs
    exact ht hobs
  · intro h K
    rw [Tm.obs_eq_den, Tm.obs_eq_den, Tm.den_app, Tm.den_app, h]

end OR.Sieber
