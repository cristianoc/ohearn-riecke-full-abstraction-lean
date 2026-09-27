import OR.Projections

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR

 def FEnv (n : ℕ) : Ctx → Type
  | [] => PUnit
  | σ :: Γ => FEnv n Γ × Level σ n

instance fenvEmptySubsingleton (n : ℕ) : Subsingleton (FEnv n []) := by
  change Subsingleton PUnit
  infer_instance

instance fenvFinite (n : ℕ) (Γ : Ctx) : Finite (FEnv n Γ) := by
  induction Γ with
  | nil => change Finite PUnit; infer_instance
  | cons σ Γ ih =>
      letI : Finite (FEnv n Γ) := ih
      change Finite (FEnv n Γ × Level σ n)
      infer_instance

instance fenvInhabited (n : ℕ) (Γ : Ctx) : Inhabited (FEnv n Γ) := by
  induction Γ with
  | nil => exact ⟨PUnit.unit⟩
  | cons σ Γ ih => exact ⟨(ih.default, default)⟩

 def flookup {n : ℕ} {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : FEnv n Γ → Level τ n :=
  match x with
  | .vz => Prod.snd
  | .vs x => fun ρ => flookup x ρ.1

 def fenvOf {n : ℕ} : {Γ : Ctx} → (∀ {τ : Ty}, Var Γ τ → Level τ n) → FEnv n Γ
  | [], _ => PUnit.unit
  | _ :: _, f => (fenvOf (fun x => f (.vs x)), f .vz)

@[simp] theorem flookup_fenvOf {n : ℕ} {Γ : Ctx} {τ : Ty}
    (x : Var Γ τ) (f : ∀ {τ : Ty}, Var Γ τ → Level τ n) :
    flookup x (fenvOf f) = f x := by
  induction x with
  | vz => rfl
  | vs x ih => exact ih (fun x => f (.vs x))

 theorem fenv_ext {n : ℕ} {Γ : Ctx} {ρ η : FEnv n Γ}
    (h : ∀ {τ : Ty}, ∀ x : Var Γ τ, flookup x ρ = flookup x η) : ρ = η := by
  induction Γ with
  | nil => exact Subsingleton.elim _ _
  | cons σ Γ ih => exact Prod.ext (ih (fun x => h (.vs x))) (h .vz)

 def fpull {n : ℕ} {Γ Δ : Ctx} (r : Ren Γ Δ) (ρ : FEnv n Δ) : FEnv n Γ :=
  fenvOf (fun x => flookup (r x) ρ)


/-- Paper §4, p. 12: a world morphism in C_n is exactly a projection from
an extended context back to its prefix.  Because contexts are represented
newest-variable first, `Extension Γ Δ` means that `Δ` is obtained from `Γ`
by repeatedly consing new types. -/
inductive Extension : Ctx → Ctx → Type
  | refl (Γ : Ctx) : Extension Γ Γ
  | cons {Γ Δ : Ctx} (σ : Ty) : Extension Γ Δ → Extension Γ (σ :: Δ)

namespace Extension

 def ren : {Γ Δ : Ctx} → Extension Γ Δ → Ren Γ Δ
  | _, _, .refl _ => fun x => x
  | _, _, .cons _ e => fun x => .vs (ren e x)

 def comp : {Γ Δ Θ : Ctx} → Extension Γ Δ → Extension Δ Θ → Extension Γ Θ
  | _, _, _, e, .refl _ => e
  | _, _, _, e, .cons σ f => .cons σ (comp e f)

@[simp] theorem ren_refl {Γ : Ctx} (x : Var Γ τ) :
    ren (.refl Γ) x = x := rfl

@[simp] theorem ren_cons {Γ Δ : Ctx} (σ : Ty) (e : Extension Γ Δ) (x : Var Γ τ) :
    ren (.cons σ e) x = .vs (ren e x) := rfl

 theorem ren_comp_apply {Γ Δ Θ : Ctx} (e : Extension Γ Δ) (f : Extension Δ Θ)
    {τ : Ty} (x : Var Γ τ) :
    ren (comp e f) x = ren f (ren e x) := by
  induction f with
  | refl => rfl
  | cons σ f ih =>
      simp only [comp, ren_cons, ih]

 theorem ren_comp {Γ Δ Θ : Ctx} (e : Extension Γ Δ) (f : Extension Δ Θ) :
    ren (comp e f) = Ren.comp (ren f) (ren e) := by
  funext τ x
  exact ren_comp_apply e f x

end Extension

@[simp] theorem flookup_fpull {n : ℕ} {Γ Δ : Ctx} {τ : Ty}
    (r : Ren Γ Δ) (x : Var Γ τ) (ρ : FEnv n Δ) :
    flookup x (fpull r ρ) = flookup (r x) ρ := flookup_fenvOf x _

@[simp] theorem fpull_id {n : ℕ} {Γ : Ctx} (ρ : FEnv n Γ) : fpull Ren.id ρ = ρ := by
  apply fenv_ext
  intro τ x
  simp only [flookup_fpull, Ren.id]

 theorem fpull_comp {n : ℕ} {Γ Δ Θ : Ctx} (r : Ren Γ Δ) (s : Ren Δ Θ) (ρ : FEnv n Θ) :
    fpull r (fpull s ρ) = fpull (Ren.comp s r) ρ := by
  apply fenv_ext
  intro τ x
  simp only [flookup_fpull, Ren.comp]

@[simp] theorem fpull_wk {n : ℕ} {Γ : Ctx} {σ : Ty} (ρ : FEnv n (σ :: Γ)) :
    fpull Ren.wk ρ = ρ.1 := by
  apply fenv_ext
  intro τ x
  simp only [flookup_fpull, Ren.wk, flookup]

 def includeEnv {n : ℕ} : {Γ : Ctx} → FEnv n Γ → Env Γ
  | [], _ => PUnit.unit
  | _ :: _, ρ => (includeEnv ρ.1, ρ.2.val)

@[simp] theorem lookup_includeEnv {n : ℕ} {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (ρ : FEnv n Γ) :
    lookup x (includeEnv ρ) = (flookup x ρ).val := by
  induction x with
  | vz => rfl
  | vs x ih => exact ih ρ.1

 theorem includeEnv_fpull {n : ℕ} {Γ Δ : Ctx} (r : Ren Γ Δ) (ρ : FEnv n Δ) :
    includeEnv (fpull r ρ) = pull r (includeEnv ρ) := by
  apply env_ext
  intro τ x
  simp only [lookup_includeEnv, flookup_fpull, lookup_pull]

 def approximateEnv (n : ℕ) : {Γ : Ctx} → Env Γ → FEnv n Γ
  | [], _ => PUnit.unit
  | σ :: _, ρ => (approximateEnv n ρ.1, ⟨projection σ n ρ.2, projection_idem σ n ρ.2⟩)

@[simp] theorem include_approximateEnv (n : ℕ) : ∀ {Γ : Ctx} (ρ : Env Γ),
    includeEnv (approximateEnv n ρ) = envProjection Γ n ρ := by
  intro Γ
  induction Γ with
  | nil => intro ρ; exact Subsingleton.elim _ _
  | cons σ Γ ih => intro ρ; exact Prod.ext (ih ρ.1) rfl

/-- Only environments are finite-level. The range is the entire semantic type. -/
def Def (n : ℕ) (Γ : Ctx) (τ : Ty) (g : FEnv n Γ → D τ) : Prop :=
  ∃ M : Tm Γ τ, ∀ ρ, denote M (includeEnv ρ) = g ρ

namespace Def

 theorem rename {n : ℕ} {Γ Δ : Ctx} {τ : Ty} {g : FEnv n Γ → D τ}
    (hg : Def n Γ τ g) (r : Ren Γ Δ) : Def n Δ τ (fun ρ => g (fpull r ρ)) := by
  rcases hg with ⟨M, hM⟩
  refine ⟨Tm.rename r M, ?_⟩
  intro ρ
  rw [denote_rename, ← includeEnv_fpull, hM]

 theorem app {n : ℕ} {Γ : Ctx} {σ τ : Ty}
    {f : FEnv n Γ → D (σ ⇒ τ)} {a : FEnv n Γ → D σ}
    (hf : Def n Γ (σ ⇒ τ) f) (ha : Def n Γ σ a) :
    Def n Γ τ (fun ρ => f ρ (a ρ)) := by
  rcases hf with ⟨M, hM⟩
  rcases ha with ⟨N, hN⟩
  exact ⟨.app M N, fun ρ => by rw [denote_app, hM, hN]⟩

 theorem closed (n : ℕ) (Γ : Ctx) {τ : Ty} (M : Tm [] τ) :
    Def n Γ τ (fun _ => denoteClosed M) :=
  ⟨Tm.closed M, fun ρ => denote_closed M (includeEnv ρ)⟩

end Def

/--
The selected test R_n over the paper's category C_n (paper §4, p. 12).
Worlds are finite products D^n_s encoded by typed contexts.  Its morphisms are
*only* the projections from an extended context to its prefix, exactly as in
O'Hearn--Riecke; arbitrary renamings are deliberately not admitted here.
-/
 def finiteTest (n : ℕ) : Test where
  World := Ctx
  El := FEnv n
  finite Γ := fenvFinite n Γ
  Hom {Δ Γ} φ := ∃ e : Extension Γ Δ, φ = fpull Extension.ren e
  identity Γ := ⟨Extension.refl Γ, funext (fun ρ => (fpull_id ρ).symm)⟩
  composition := by
    intro u v w φ ψ hφ hψ
    rcases hφ with ⟨e, rfl⟩
    rcases hψ with ⟨f, rfl⟩
    refine ⟨Extension.comp e f, ?_⟩
    funext ρ
    rw [Extension.ren_comp, fpull_comp]
  ground Γ := Def n Γ .nat
  primitive Γ := {
    zero := ⟨.zero, fun _ => rfl⟩
    succ := by
      rintro g ⟨M, hM⟩
      exact ⟨.succ M, fun ρ => by rw [denote_succ, hM]⟩
    pred := by
      rintro g ⟨M, hM⟩
      exact ⟨.pred M, fun ρ => by rw [denote_pred, hM]⟩
    ifz := by
      rintro c a b ⟨C, hC⟩ ⟨M, hM⟩ ⟨N, hN⟩
      exact ⟨.ifz C M N, fun ρ => by rw [denote_ifz, hC, hM, hN]⟩ }
  reindex := by
    rintro Δ Γ φ ⟨e, rfl⟩ g hg
    exact hg.rename Extension.ren e

/-- Relations displayed directly on finite environments. No encoding casts occur here. -/
def Rel (n : ℕ) (Γ : Ctx) (τ : Ty) (g : FEnv n Γ → D τ) : Prop :=
  (typeObj τ).R (finiteTest n) Γ g

@[simp] theorem rel_nat (n : ℕ) (Γ : Ctx) (g : FEnv n Γ → Ground) :
    Rel n Γ .nat g ↔ Def n Γ .nat g := Iff.rfl

 theorem rel_arr (n : ℕ) (Γ : Ctx) (σ τ : Ty) (g : FEnv n Γ → D (σ ⇒ τ)) :
    Rel n Γ (σ ⇒ τ) g ↔
      ∀ (Δ : Ctx) (e : Extension Γ Δ) (a : FEnv n Δ → D σ),
        Rel n Δ σ a → Rel n Δ τ (fun ρ => g (fpull Extension.ren e ρ) (a ρ)) := by
  constructor
  · intro hg Δ e a ha
    exact hg Δ (fpull Extension.ren e) ⟨e, rfl⟩ a ha
  · intro hg Δ φ hφ a ha
    rcases hφ with ⟨e, rfl⟩
    exact hg Δ e a ha

 theorem rel_constant (n : ℕ) (Γ : Ctx) (τ : Ty) (d : D τ) :
    Rel n Γ τ (fun _ => d) := (typeObj τ).concrete (finiteTest n) Γ d

 theorem rel_projection {n : ℕ} {Γ : Ctx} {τ : Ty} {g : FEnv n Γ → D τ}
    (hg : Rel n Γ τ g) : Rel n Γ τ (fun ρ => projection τ n (g ρ)) :=
  (projection τ n).uniform (finiteTest n) Γ g hg

 theorem rel_reindex {n : ℕ} {Γ Δ : Ctx} {τ : Ty} {g : FEnv n Γ → D τ}
    (hg : Rel n Γ τ g) (e : Extension Γ Δ) :
    Rel n Δ τ (fun ρ => g (fpull Extension.ren e ρ)) :=
  ((typeObj τ).rel (finiteTest n)).reindex ⟨e, rfl⟩ g hg

end OR
