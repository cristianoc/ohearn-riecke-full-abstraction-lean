import OR.SR
import OR.Syntax

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR

 def typeObj : Ty → Obj
  | .nat => Obj.nat
  | .arr σ τ => Obj.arr (typeObj σ) (typeObj τ)

abbrev D (τ : Ty) : Type := (typeObj τ).domain.Carrier

/-- Expose semantic application without erasing the relational type indices. -/
instance dArrCoeFun (σ τ : Ty) : CoeFun (D (σ ⇒ τ)) (fun _ => D σ → D τ) :=
  ⟨fun f => (show Hom (typeObj σ) (typeObj τ) from f).val.toFun⟩

 def envObj : Ctx → Obj
  | [] => Obj.one
  | σ :: Γ => Obj.prod (envObj Γ) (typeObj σ)

abbrev Env (Γ : Ctx) : Type := (envObj Γ).domain.Carrier

instance emptyEnvSubsingleton : Subsingleton (Env []) := by
  change Subsingleton PUnit
  infer_instance

 def lookup {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Env Γ → D τ :=
  match x with
  | .vz => Prod.snd
  | .vs x => fun ρ => lookup x ρ.1

 def lookupHom {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Hom (envObj Γ) (typeObj τ) :=
  match x with
  | .vz => Hom.snd
  | .vs x => (lookupHom x).comp Hom.fst

@[simp] theorem lookupHom_apply {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) :
    lookupHom x ρ = lookup x ρ := by
  induction x with
  | vz => rfl
  | vs x ih => exact ih ρ.1

 def envOf : {Γ : Ctx} → (∀ {τ : Ty}, Var Γ τ → D τ) → Env Γ
  | [], _ => PUnit.unit
  | _ :: _, f => (envOf (fun x => f (.vs x)), f .vz)

@[simp] theorem lookup_envOf {Γ : Ctx} {τ : Ty}
    (x : Var Γ τ) (f : ∀ {τ : Ty}, Var Γ τ → D τ) : lookup x (envOf f) = f x := by
  induction x with
  | vz => rfl
  | vs x ih => exact ih (fun x => f (.vs x))

 theorem env_ext {Γ : Ctx} {ρ η : Env Γ}
    (h : ∀ {τ : Ty}, ∀ x : Var Γ τ, lookup x ρ = lookup x η) : ρ = η := by
  induction Γ with
  | nil => exact Subsingleton.elim _ _
  | cons σ Γ ih =>
      apply Prod.ext
      · apply ih
        intro τ x
        exact h (.vs x)
      · exact h .vz

@[simp] theorem envOf_lookup {Γ : Ctx} (ρ : Env Γ) : envOf (fun x => lookup x ρ) = ρ := by
  apply env_ext
  intro τ x
  exact lookup_envOf x _

 theorem lookup_mono {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Monotone (lookup x) := by
  intro ρ η h
  simpa only [lookupHom_apply] using (lookupHom x).mono h

 theorem env_le_of_lookup {Γ : Ctx} {ρ η : Env Γ}
    (h : ∀ {τ : Ty}, ∀ x : Var Γ τ, lookup x ρ ≤ lookup x η) : ρ ≤ η := by
  induction Γ with
  | nil => exact (Subsingleton.elim ρ η).le
  | cons σ Γ ih =>
      exact ⟨ih (fun x => h (.vs x)), h .vz⟩

 def pull {Γ Δ : Ctx} (r : Ren Γ Δ) (η : Env Δ) : Env Γ :=
  envOf (fun x => lookup (r x) η)

@[simp] theorem lookup_pull {Γ Δ : Ctx} {τ : Ty} (r : Ren Γ Δ) (x : Var Γ τ) (η : Env Δ) :
    lookup x (pull r η) = lookup (r x) η := lookup_envOf x _

@[simp] theorem pull_id {Γ : Ctx} (ρ : Env Γ) : pull Ren.id ρ = ρ := by
  apply env_ext
  intro τ x
  simp only [lookup_pull, Ren.id]

 theorem pull_comp {Γ Δ Θ : Ctx} (r : Ren Γ Δ) (s : Ren Δ Θ) (ρ : Env Θ) :
    pull r (pull s ρ) = pull (Ren.comp s r) ρ := by
  apply env_ext
  intro τ x
  simp only [lookup_pull, Ren.comp]

@[simp] theorem pull_lift {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (ρ : Env Δ) (a : D σ) :
    pull (Ren.lift r) (ρ, a) = (pull r ρ, a) := by
  apply env_ext
  intro τ x
  rw [lookup_pull]
  cases x <;> simp only [Ren.lift, lookup, lookup_pull]

@[simp] theorem pull_wk {Γ : Ctx} {σ : Ty} (ρ : Env Γ) (a : D σ) :
    pull Ren.wk (ρ, a) = ρ := by
  apply env_ext
  intro τ x
  simp only [lookup_pull, Ren.wk, lookup]

/-- Interpretation is morphism-valued; continuity and uniformity are never assumed later. -/
 def denote {Γ : Ctx} {τ : Ty} (M : Tm Γ τ) : Hom (envObj Γ) (typeObj τ) :=
  match M with
  | .var x => lookupHom x
  | .lam M => Hom.curry (denote M)
  | .app M N => Hom.eval.comp ((denote M).pair (denote N))
  | .fix M => (Hom.fixMap _).comp (denote M)
  | .zero => Hom.const (.val 0)
  | .succ M => Hom.successor.comp (denote M)
  | .pred M => Hom.predecessor.comp (denote M)
  | .ifz C M N => Hom.conditional.comp ((denote C).pair ((denote M).pair (denote N)))

abbrev denoteClosed {τ : Ty} (M : Tm [] τ) : D τ := denote M PUnit.unit

@[simp] theorem denote_var {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) :
    denote (.var x) ρ = lookup x ρ := lookupHom_apply x ρ
@[simp] theorem denote_lam {Γ : Ctx} {σ τ : Ty} (M : Tm (σ :: Γ) τ) (ρ : Env Γ) (a : D σ) :
    denote (.lam M) ρ a = denote M (ρ, a) := rfl
@[simp] theorem denote_app {Γ : Ctx} {σ τ : Ty} (M : Tm Γ (σ ⇒ τ)) (N : Tm Γ σ) (ρ : Env Γ) :
    denote (.app M N) ρ = denote M ρ (denote N ρ) := rfl
@[simp] theorem denote_fix {Γ : Ctx} {τ : Ty} (M : Tm Γ (τ ⇒ τ)) (ρ : Env Γ) :
    denote (.fix M) ρ = Hom.fixMap (typeObj τ) (denote M ρ) := rfl
@[simp] theorem denote_zero {Γ : Ctx} (ρ : Env Γ) : denote (Tm.zero : Tm Γ .nat) ρ = .val 0 := rfl
@[simp] theorem denote_succ {Γ : Ctx} (M : Tm Γ .nat) (ρ : Env Γ) :
    denote (.succ M) ρ = Ground.succ (denote M ρ) := rfl
@[simp] theorem denote_pred {Γ : Ctx} (M : Tm Γ .nat) (ρ : Env Γ) :
    denote (.pred M) ρ = Ground.pred (denote M ρ) := rfl
@[simp] theorem denote_ifz {Γ : Ctx} (C M N : Tm Γ .nat) (ρ : Env Γ) :
    denote (.ifz C M N) ρ = Ground.ifz (denote C ρ) (denote M ρ) (denote N ρ) := rfl

 theorem denote_rename {Γ Δ : Ctx} {τ : Ty} (M : Tm Γ τ)
    (r : Ren Γ Δ) (η : Env Δ) : denote (Tm.rename r M) η = denote M (pull r η) := by
  induction M generalizing Δ with
  | var x => simp only [Tm.rename, denote_var, lookup_pull]
  | lam M ih =>
      apply Hom.ext
      intro a
      change denote (Tm.rename (Ren.lift r) M) (η, a) = denote M (pull r η, a)
      rw [ih, pull_lift]
  | app M N ihM ihN => simp only [Tm.rename, denote_app, ihM, ihN]
  | fix M ih => simp only [Tm.rename, denote_fix, ih]
  | zero => rfl
  | succ M ih => simp only [Tm.rename, denote_succ, ih]
  | pred M ih => simp only [Tm.rename, denote_pred, ih]
  | ifz C M N ihC ihM ihN => simp only [Tm.rename, denote_ifz, ihC, ihM, ihN]

@[simp] theorem denote_closed {Γ : Ctx} {τ : Ty} (M : Tm [] τ) (ρ : Env Γ) :
    denote (Tm.closed M) ρ = denoteClosed M := by
  rw [Tm.closed, denote_rename]
  exact congrArg (denote M) (Subsingleton.elim _ _)

 def subenv {Γ Δ : Ctx} (θ : Sub Γ Δ) (η : Env Δ) : Env Γ :=
  envOf (fun x => denote (θ x) η)

@[simp] theorem lookup_subenv {Γ Δ : Ctx} {τ : Ty}
    (θ : Sub Γ Δ) (x : Var Γ τ) (η : Env Δ) :
    lookup x (subenv θ η) = denote (θ x) η := lookup_envOf x _

@[simp] theorem subenv_lift {Γ Δ : Ctx} {σ : Ty} (θ : Sub Γ Δ) (η : Env Δ) (a : D σ) :
    subenv (Sub.lift θ) (η, a) = (subenv θ η, a) := by
  apply env_ext
  intro τ x
  rw [lookup_subenv]
  cases x with
  | vz => simp only [Sub.lift, denote_var, lookup]
  | vs x => simp only [Sub.lift, denote_rename, pull_wk, lookup, lookup_subenv]

@[simp] theorem subenv_id {Γ : Ctx} (ρ : Env Γ) : subenv Sub.id ρ = ρ := by
  apply env_ext
  intro τ x
  simp only [lookup_subenv, Sub.id, denote_var]

@[simp] theorem subenv_single {Γ : Ctx} {σ : Ty} (N : Tm Γ σ) (ρ : Env Γ) :
    subenv (Sub.single N) ρ = (ρ, denote N ρ) := by
  apply env_ext
  intro τ x
  rw [lookup_subenv]
  cases x <;> simp only [Sub.single, denote_var, lookup]

@[simp] theorem subenv_extend {Γ Δ : Ctx} {σ : Ty}
    (θ : Sub Γ Δ) (N : Tm Δ σ) (ρ : Env Δ) :
    subenv (Sub.extend θ N) ρ = (subenv θ ρ, denote N ρ) := by
  apply env_ext
  intro τ x
  rw [lookup_subenv]
  cases x <;> simp only [Sub.extend, lookup, lookup_subenv]

 theorem denote_subst {Γ Δ : Ctx} {τ : Ty} (M : Tm Γ τ)
    (θ : Sub Γ Δ) (η : Env Δ) : denote (Tm.subst θ M) η = denote M (subenv θ η) := by
  induction M generalizing Δ with
  | var x => simp only [Tm.subst, lookup_subenv, denote_var]
  | lam M ih =>
      apply Hom.ext
      intro a
      change denote (Tm.subst (Sub.lift θ) M) (η, a) = denote M (subenv θ η, a)
      rw [ih, subenv_lift]
  | app M N ihM ihN => simp only [Tm.subst, denote_app, ihM, ihN]
  | fix M ih => simp only [Tm.subst, denote_fix, ih]
  | zero => rfl
  | succ M ih => simp only [Tm.subst, denote_succ, ih]
  | pred M ih => simp only [Tm.subst, denote_pred, ih]
  | ifz C M N ihC ihM ihN => simp only [Tm.subst, denote_ifz, ihC, ihM, ihN]

 theorem denote_beta {Γ : Ctx} {σ τ : Ty} (M : Tm (σ :: Γ) τ)
    (N : Tm Γ σ) (ρ : Env Γ) :
    denote (.app (.lam M) N) ρ = denote (Tm.subst (Sub.single N) M) ρ := by
  simp only [denote_app, denote_lam, denote_subst, subenv_single]

@[simp] theorem denote_numeral {Γ : Ctx} (n : ℕ) (ρ : Env Γ) :
    denote (Tm.numeral n) ρ = .val n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Tm.numeral, denote_succ, ih, Ground.succ_val]

@[simp] theorem denote_omega {Γ : Ctx} (τ : Ty) (ρ : Env Γ) :
    denote (Tm.omega τ) ρ = ⊥ := by
  have hid : denote (Tm.lam (Tm.var (Var.vz : Var (τ :: Γ) τ))) ρ =
      (Hom.id : Hom (typeObj τ) (typeObj τ)) := by
    apply Hom.ext
    intro a
    rfl
  rw [Tm.omega, denote_fix, hid, Hom.fixMap_id]

/-- Curried closure follows the order of the nested semantic environment products. -/
 def CloseTy : Ctx → Ty → Ty
  | [], τ => τ
  | σ :: Γ, τ => CloseTy Γ (σ ⇒ τ)

 def Tm.close : {Γ : Ctx} → {τ : Ty} → Tm Γ τ → Tm [] (CloseTy Γ τ)
  | [], _, M => M
  | _ :: Γ, _, M => Tm.close (Γ := Γ) (.lam M)

 def Tm.applyEnv {Δ : Ctx} : (Γ : Ctx) → {τ : Ty} →
    Tm Δ (CloseTy Γ τ) → Sub Γ Δ → Tm Δ τ
  | [], _, Q, _ => Q
  | _ :: Γ, _, Q, θ => .app (Tm.applyEnv Γ Q (fun x => θ (.vs x))) (θ .vz)

 theorem denote_apply_close : ∀ (Γ : Ctx) {τ : Ty} (M : Tm Γ τ)
    {Δ : Ctx} (θ : Sub Γ Δ) (η : Env Δ),
    denote (Tm.applyEnv Γ (Tm.closed (Tm.close M)) θ) η = denote M (subenv θ η) := by
  intro Γ
  induction Γ with
  | nil =>
      intro τ M Δ θ η
      change denote (Tm.closed M) η = denote M (subenv θ η)
      rw [denote_closed]
      exact congrArg (denote M) (Subsingleton.elim _ _)
  | cons σ Γ ih =>
      intro τ M Δ θ η
      change denote (.app (Tm.applyEnv Γ (Tm.closed (Tm.close (.lam M)))
        (fun x => θ (.vs x))) (θ .vz)) η = _
      rw [denote_app, ih, denote_lam]
      rfl

end OR
