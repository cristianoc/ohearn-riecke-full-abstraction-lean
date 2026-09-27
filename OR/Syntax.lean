import Mathlib

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace OR

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

infixr:60 " ⇒ " => Ty.arr

/-- Newest variable first; environments will store its value in the right component. -/
abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | vz {Γ : Ctx} {σ : Ty} : Var (σ :: Γ) σ
  | vs {Γ : Ctx} {σ τ : Ty} : Var Γ τ → Var (σ :: Γ) τ

inductive Tm : Ctx → Ty → Type where
  | var {Γ : Ctx} {τ : Ty} : Var Γ τ → Tm Γ τ
  | lam {Γ : Ctx} {σ τ : Ty} : Tm (σ :: Γ) τ → Tm Γ (σ ⇒ τ)
  | app {Γ : Ctx} {σ τ : Ty} : Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  | fix {Γ : Ctx} {τ : Ty} : Tm Γ (τ ⇒ τ) → Tm Γ τ
  | zero {Γ : Ctx} : Tm Γ .nat
  | succ {Γ : Ctx} : Tm Γ .nat → Tm Γ .nat
  | pred {Γ : Ctx} : Tm Γ .nat → Tm Γ .nat
  | ifz {Γ : Ctx} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat → Tm Γ .nat

abbrev Ren (Γ Δ : Ctx) := ∀ {τ : Ty}, Var Γ τ → Var Δ τ
abbrev Sub (Γ Δ : Ctx) := ∀ {τ : Ty}, Var Γ τ → Tm Δ τ

namespace Ren

variable {Γ Δ Θ : Ctx} {σ : Ty}

 def id : Ren Γ Γ := fun x => x
 def comp (s : Ren Δ Θ) (r : Ren Γ Δ) : Ren Γ Θ := fun x => s (r x)
 def wk : Ren Γ (σ :: Γ) := Var.vs
 def empty : Ren [] Γ := fun x => nomatch x
 def lift (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .vz => .vz
  | _, .vs x => .vs (r x)

/-- Keep the implicit type index abstract in equalities of renaming families. -/
@[simp] theorem lift_id : @lift Γ Γ σ (@id Γ) = @id (σ :: Γ) := by
  funext τ x
  cases x <;> rfl

 theorem lift_comp (s : Ren Δ Θ) (r : Ren Γ Δ) :
    @lift Γ Θ σ (@comp Γ Δ Θ s r) =
      @comp (σ :: Γ) (σ :: Δ) (σ :: Θ) (@lift Δ Θ σ s) (@lift Γ Δ σ r) := by
  funext τ x
  cases x <;> rfl

end Ren

namespace Tm

 def rename {Γ Δ : Ctx} {τ : Ty} (r : Ren Γ Δ) (M : Tm Γ τ) : Tm Δ τ :=
  match M with
  | .var x => .var (r x)
  | .lam M => .lam (rename (Ren.lift r) M)
  | .app M N => .app (rename r M) (rename r N)
  | .fix M => .fix (rename r M)
  | .zero => .zero
  | .succ M => .succ (rename r M)
  | .pred M => .pred (rename r M)
  | .ifz C M N => .ifz (rename r C) (rename r M) (rename r N)

variable {Γ Δ Θ : Ctx} {σ τ : Ty}

@[simp] theorem rename_id (M : Tm Γ τ) : rename Ren.id M = M := by
  induction M <;> simp_all [rename, Ren.lift_id, Ren.id]

 theorem rename_comp (M : Tm Γ τ) (r : Ren Γ Δ) (s : Ren Δ Θ) :
    rename s (rename r M) = rename (Ren.comp s r) M := by
  induction M generalizing Δ Θ <;> simp_all [rename, Ren.lift_comp, Ren.comp]

 theorem rename_wk (M : Tm Γ τ) (r : Ren Γ Δ) :
    rename (Ren.lift (σ := σ) r) (rename Ren.wk M) = rename Ren.wk (rename r M) := by
  rw [rename_comp, rename_comp]
  rfl

end Tm

namespace Sub

variable {Γ Δ Θ : Ctx} {σ : Ty}

 def id : Sub Γ Γ := Tm.var
 def ofRen (r : Ren Γ Δ) : Sub Γ Δ := fun x => .var (r x)
 def lift (θ : Sub Γ Δ) : Sub (σ :: Γ) (σ :: Δ)
  | _, .vz => .var .vz
  | _, .vs x => Tm.rename Ren.wk (θ x)
 def single {σ : Ty} (N : Tm Γ σ) : Sub (σ :: Γ) Γ
  | _, .vz => N
  | _, .vs x => .var x
 def extend {σ : Ty} (θ : Sub Γ Δ) (N : Tm Δ σ) : Sub (σ :: Γ) Δ
  | _, .vz => N
  | _, .vs x => θ x

@[simp] theorem lift_id : @lift Γ Γ σ (@id Γ) = @id (σ :: Γ) := by
  funext τ x
  cases x <;> rfl

 theorem lift_precomp (θ : Sub Δ Θ) (r : Ren Γ Δ) :
    (fun {τ} (x : Var (σ :: Γ) τ) => lift θ (Ren.lift r x)) =
      @lift Γ Θ σ (fun {τ} (x : Var Γ τ) => θ (r x)) := by
  funext τ x
  cases x <;> rfl

 theorem lift_postrename (r : Ren Δ Θ) (θ : Sub Γ Δ) :
    (fun {τ} (x : Var (σ :: Γ) τ) => Tm.rename (Ren.lift r) (lift θ x)) =
      @lift Γ Θ σ (fun {τ} (x : Var Γ τ) => Tm.rename r (θ x)) := by
  funext τ x
  cases x with
  | vz => rfl
  | vs x => exact Tm.rename_wk (θ x) r

 theorem lift_ofRen (r : Ren Γ Δ) :
    @lift Γ Δ σ (@ofRen Γ Δ r) = @ofRen (σ :: Γ) (σ :: Δ) (@Ren.lift Γ Δ σ r) := by
  funext τ x
  cases x <;> rfl

end Sub

namespace Tm

 def subst {Γ Δ : Ctx} {τ : Ty} (θ : Sub Γ Δ) (M : Tm Γ τ) : Tm Δ τ :=
  match M with
  | .var x => θ x
  | .lam M => .lam (subst (Sub.lift θ) M)
  | .app M N => .app (subst θ M) (subst θ N)
  | .fix M => .fix (subst θ M)
  | .zero => .zero
  | .succ M => .succ (subst θ M)
  | .pred M => .pred (subst θ M)
  | .ifz C M N => .ifz (subst θ C) (subst θ M) (subst θ N)

variable {Γ Δ Θ : Ctx} {σ τ : Ty}

@[simp] theorem subst_id (M : Tm Γ τ) : subst Sub.id M = M := by
  induction M with
  | var x => rfl
  | lam M ih => simp only [subst, Sub.lift_id, ih]
  | app M N ihM ihN => simp only [subst, ihM, ihN]
  | fix M ih => simp only [subst, ih]
  | zero => rfl
  | succ M ih => simp only [subst, ih]
  | pred M ih => simp only [subst, ih]
  | ifz C M N ihC ihM ihN => simp only [subst, ihC, ihM, ihN]

 theorem subst_rename (M : Tm Γ τ) (r : Ren Γ Δ) (θ : Sub Δ Θ) :
    subst θ (rename r M) = subst (fun x => θ (r x)) M := by
  induction M generalizing Δ Θ with
  | var x => rfl
  | lam M ih =>
      simp only [rename, subst]
      rw [ih]
      rw [Sub.lift_precomp]
  | app M N ihM ihN => simp only [rename, subst, ihM, ihN]
  | fix M ih => simp only [rename, subst, ih]
  | zero => rfl
  | succ M ih => simp only [rename, subst, ih]
  | pred M ih => simp only [rename, subst, ih]
  | ifz C M N ihC ihM ihN => simp only [rename, subst, ihC, ihM, ihN]

 theorem rename_subst (M : Tm Γ τ) (θ : Sub Γ Δ) (r : Ren Δ Θ) :
    rename r (subst θ M) = subst (fun x => rename r (θ x)) M := by
  induction M generalizing Δ Θ with
  | var x => rfl
  | lam M ih =>
      simp only [rename, subst]
      rw [ih]
      rw [Sub.lift_postrename]
  | app M N ihM ihN => simp only [rename, subst, ihM, ihN]
  | fix M ih => simp only [rename, subst, ih]
  | zero => rfl
  | succ M ih => simp only [rename, subst, ih]
  | pred M ih => simp only [rename, subst, ih]
  | ifz C M N ihC ihM ihN => simp only [rename, subst, ihC, ihM, ihN]

 theorem subst_lift_wk (M : Tm Γ τ) (θ : Sub Γ Δ) :
    subst (Sub.lift (σ := σ) θ) (rename Ren.wk M) = rename Ren.wk (subst θ M) := by
  rw [subst_rename, rename_subst]
  rfl

 theorem subst_comp (M : Tm Γ τ) (θ : Sub Γ Δ) (η : Sub Δ Θ) :
    subst η (subst θ M) = subst (fun x => subst η (θ x)) M := by
  induction M generalizing Δ Θ with
  | var x => rfl
  | @lam Γ σ τ M ih =>
      simp only [subst]
      apply congrArg Tm.lam
      rw [ih]
      apply congrArg (fun ξ : Sub (σ :: Γ) (σ :: Θ) => subst ξ M)
      funext υ x
      cases x with
      | vz => rfl
      | vs x => exact subst_lift_wk (θ x) η
  | app M N ihM ihN => simp only [subst, ihM, ihN]
  | fix M ih => simp only [subst, ih]
  | zero => rfl
  | succ M ih => simp only [subst, ih]
  | pred M ih => simp only [subst, ih]
  | ifz C M N ihC ihM ihN => simp only [subst, ihC, ihM, ihN]

 theorem rename_eq_subst (M : Tm Γ τ) (r : Ren Γ Δ) :
    rename r M = subst (Sub.ofRen r) M := by
  induction M generalizing Δ with
  | var x => rfl
  | lam M ih => simp only [rename, subst, ih, Sub.lift_ofRen]
  | app M N ihM ihN => simp only [rename, subst, ihM, ihN]
  | fix M ih => simp only [rename, subst, ih]
  | zero => rfl
  | succ M ih => simp only [rename, subst, ih]
  | pred M ih => simp only [rename, subst, ih]
  | ifz C M N ihC ihM ihN => simp only [rename, subst, ihC, ihM, ihN]

@[simp] theorem subst_single_wk (M : Tm Γ τ) (N : Tm Γ σ) :
    subst (Sub.single N) (rename Ren.wk M) = M := by
  rw [subst_rename]
  change subst Sub.id M = M
  exact subst_id M

/-- The binder equation used in the lambda case of computational adequacy. -/
 theorem subst_lift_single (M : Tm (σ :: Γ) τ) (θ : Sub Γ Δ) (N : Tm Δ σ) :
    subst (Sub.single N) (subst (Sub.lift θ) M) = subst (Sub.extend θ N) M := by
  rw [subst_comp]
  congr 1
  funext υ x
  cases x with
  | vz => rfl
  | vs x => exact subst_single_wk (θ x) N

 def closed {Γ : Ctx} {τ : Ty} (M : Tm [] τ) : Tm Γ τ := rename Ren.empty M

@[simp] theorem closed_empty (M : Tm [] τ) : closed (Γ := []) M = M := by
  unfold closed
  have he : @Ren.empty [] = @Ren.id [] := by
    funext υ x
    exact nomatch x
  rw [he, rename_id]

@[simp] theorem rename_closed (M : Tm [] τ) (r : Ren Γ Δ) :
    rename r (closed (Γ := Γ) M) = closed (Γ := Δ) M := by
  rw [closed, rename_comp, closed]
  congr 1
  funext υ x
  exact nomatch x

@[simp] theorem subst_closed (M : Tm [] τ) (θ : Sub Γ Δ) :
    subst θ (closed (Γ := Γ) M) = closed (Γ := Δ) M := by
  rw [closed, subst_rename, closed, rename_eq_subst]
  congr 1
  funext υ x
  exact nomatch x

 def numeral {Γ : Ctx} : ℕ → Tm Γ .nat
  | 0 => .zero
  | n + 1 => .succ (numeral n)

 def omega {Γ : Ctx} (τ : Ty) : Tm Γ τ := .fix (.lam (.var .vz))

@[simp] theorem rename_numeral (n : ℕ) (r : Ren Γ Δ) :
    rename r (numeral n) = numeral n := by induction n <;> simp_all [numeral, rename]

@[simp] theorem subst_numeral (n : ℕ) (θ : Sub Γ Δ) :
    subst θ (numeral n) = numeral n := by induction n <;> simp_all [numeral, subst]

end Tm

end OR
