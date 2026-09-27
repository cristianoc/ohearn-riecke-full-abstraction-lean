import OR.Sieber.Model

/-!
# Normal forms

Every term has a β-normal, η-long form with the same denotation in Sieber's
model (`Tm.nf_sound`). The normal form is computed by normalisation by
evaluation, and its soundness is proved with a Kripke logical relation between
evaluation values and Sieber's semantics.

Normal forms have the subformula property: every variable and argument in a
closed normal form of type `τ` has a subformula of `τ` as its type.
-/

set_option autoImplicit false

namespace OR.Sieber

/-! ## Renamings -/

def Ren (Γ Δ : Ctx) : Type := ∀ τ, Var Γ τ → Var Δ τ

def Ren.id (Γ : Ctx) : Ren Γ Γ := fun _ x => x
def Ren.wk {Γ : Ctx} {σ : Ty} : Ren Γ (σ :: Γ) := fun _ x => .vs x
def Ren.comp {Γ Δ Θ : Ctx} (s : Ren Δ Θ) (r : Ren Γ Δ) : Ren Γ Θ := fun τ x => s τ (r τ x)
def Ren.lift {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .vz => .vz
  | _, .vs x => .vs (r _ x)

def Tm.rename : {Γ Δ : Ctx} → {τ : Ty} → Ren Γ Δ → Tm Γ τ → Tm Δ τ
  | _, _, _, r, .var x => .var (r _ x)
  | _, _, _, r, .lam M => .lam (M.rename r.lift)
  | _, _, _, r, .app M N => .app (M.rename r) (N.rename r)
  | _, _, _, _, .tt => .tt
  | _, _, _, _, .ff => .ff
  | _, _, _, _, .bot => .bot
  | _, _, _, r, .ite C M N => .ite (C.rename r) (M.rename r) (N.rename r)

/-- Pull an environment back along a renaming. -/
def Env.ren : {Γ Δ : Ctx} → Ren Γ Δ → Env Δ → Env Γ
  | [], _, _, _ => PUnit.unit
  | σ :: _, _, r, ρ => (Env.ren (fun τ x => r τ (.vs x)) ρ, (r σ .vz).sem.1 ρ)

theorem Var.sem_ren : ∀ {Γ Δ : Ctx} {τ : Ty} (r : Ren Γ Δ) (x : Var Γ τ) (ρ : Env Δ),
    x.sem.1 (Env.ren r ρ) = (r τ x).sem.1 ρ
  | _ :: _, _, _, _, .vz, _ => rfl
  | _ :: _, _, _, r, .vs x, ρ => Var.sem_ren (fun τ y => r τ (.vs y)) x ρ

theorem Env.ren_wk : ∀ {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (ρ : Env Δ) (a : (Model σ).car),
    Env.ren (fun τ x => .vs (r τ x)) ((ρ, a) : Env (σ :: Δ)) = Env.ren r ρ
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, r, ρ, a => by
      simp only [Env.ren]
      rw [Env.ren_wk (fun τ y => r τ (.vs y)) ρ a]
      rfl

theorem Env.ren_id : ∀ {Γ : Ctx} (ρ : Env Γ), Env.ren (Ren.id Γ) ρ = ρ
  | [], _ => rfl
  | _ :: _, ρ => by
      obtain ⟨ρ₁, a⟩ := ρ
      simp only [Env.ren]
      rw [show (fun τ (x : Var _ τ) => Ren.id _ τ (.vs x)) = (fun τ x => .vs (Ren.id _ τ x)) from rfl,
        Env.ren_wk, Env.ren_id]
      rfl

theorem Env.ren_lift {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (ρ : Env Δ) (a : (Model σ).car) :
    Env.ren (r.lift (σ := σ)) ((ρ, a) : Env (σ :: Δ)) = (Env.ren r ρ, a) := by
  simp only [Env.ren]
  rw [show (fun τ (x : Var Γ τ) => r.lift τ (.vs x)) = (fun τ x => .vs (r τ x)) from rfl, Env.ren_wk]
  rfl

theorem Env.ren_comp : ∀ {Γ Δ Θ : Ctx} (s : Ren Δ Θ) (r : Ren Γ Δ) (ρ : Env Θ),
    Env.ren (Ren.comp s r) ρ = Env.ren r (Env.ren s ρ)
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, s, r, ρ => by
      simp only [Env.ren]
      rw [show (fun τ (x : Var _ τ) => Ren.comp s r τ (.vs x)) = Ren.comp s (fun τ x => r τ (.vs x)) from rfl,
        Env.ren_comp s (fun τ x => r τ (.vs x)) ρ, Var.sem_ren]
      rfl

theorem Model.arr_ext {σ τ : Ty} {f g : (Model (σ ⇒ τ)).car} (h : ∀ a, f.1 a = g.1 a) : f = g :=
  Subtype.ext (funext h)

theorem Tm.sem_rename : ∀ {Γ Δ : Ctx} {τ : Ty} (r : Ren Γ Δ) (M : Tm Γ τ) (ρ : Env Δ),
    (M.rename r).sem.1 ρ = M.sem.1 (Env.ren r ρ)
  | _, _, _, r, .var x, ρ => by simp only [Tm.rename, Tm.sem]; exact (Var.sem_ren r x ρ).symm
  | _, _, .arr _ _, r, .lam M, ρ => by
      apply Model.arr_ext
      intro a
      simp only [Tm.rename, Tm.sem]
      rw [Tm.sem_rename r.lift M (ρ, a), Env.ren_lift]
  | _, _, _, r, .app M N, ρ => by
      simp only [Tm.rename, Tm.sem]
      rw [Tm.sem_rename r M ρ, Tm.sem_rename r N ρ]
  | _, _, _, _, .tt, _ => by simp only [Tm.rename, Tm.sem, constSem]
  | _, _, _, _, .ff, _ => by simp only [Tm.rename, Tm.sem, constSem]
  | _, _, _, _, .bot, _ => by simp only [Tm.rename, Tm.sem, constSem]
  | _, _, _, r, .ite C M N, ρ => by
      simp only [Tm.rename, Tm.sem]
      rw [Tm.sem_rename r C ρ, Tm.sem_rename r M ρ, Tm.sem_rename r N ρ]

/-! ## Normal forms -/

/-- `Norm Γ τ true` are β-normal η-long forms; `Norm Γ τ false` are neutral terms. -/
inductive Norm : Ctx → Ty → Bool → Type where
  | var {Γ : Ctx} {τ : Ty} : Var Γ τ → Norm Γ τ false
  | app {Γ : Ctx} {σ τ : Ty} : Norm Γ (σ ⇒ τ) false → Norm Γ σ true → Norm Γ τ false
  | up {Γ : Ctx} : Norm Γ .B false → Norm Γ .B true
  | lam {Γ : Ctx} {σ τ : Ty} : Norm (σ :: Γ) τ true → Norm Γ (σ ⇒ τ) true
  | tt {Γ : Ctx} : Norm Γ .B true
  | ff {Γ : Ctx} : Norm Γ .B true
  | bot {Γ : Ctx} : Norm Γ .B true
  | ite {Γ : Ctx} : Norm Γ .B true → Norm Γ .B true → Norm Γ .B true → Norm Γ .B true

def Norm.embed : {Γ : Ctx} → {τ : Ty} → {b : Bool} → Norm Γ τ b → Tm Γ τ
  | _, _, _, .var x => .var x
  | _, _, _, .app n m => .app n.embed m.embed
  | _, _, _, .up n => n.embed
  | _, _, _, .lam n => .lam n.embed
  | _, _, _, .tt => .tt
  | _, _, _, .ff => .ff
  | _, _, _, .bot => .bot
  | _, _, _, .ite c a b => .ite c.embed a.embed b.embed

def Norm.rename : {Γ Δ : Ctx} → {τ : Ty} → {b : Bool} → Ren Γ Δ → Norm Γ τ b → Norm Δ τ b
  | _, _, _, _, r, .var x => .var (r _ x)
  | _, _, _, _, r, .app n m => .app (n.rename r) (m.rename r)
  | _, _, _, _, r, .up n => .up (n.rename r)
  | _, _, _, _, r, .lam n => .lam (n.rename r.lift)
  | _, _, _, _, _, .tt => .tt
  | _, _, _, _, _, .ff => .ff
  | _, _, _, _, _, .bot => .bot
  | _, _, _, _, r, .ite c a b => .ite (c.rename r) (a.rename r) (b.rename r)

theorem Norm.embed_rename : ∀ {Γ Δ : Ctx} {τ : Ty} {b : Bool} (r : Ren Γ Δ) (n : Norm Γ τ b),
    (n.rename r).embed = n.embed.rename r
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, r, .app n m => by
      simp only [Norm.rename, Norm.embed, Tm.rename, Norm.embed_rename r n, Norm.embed_rename r m]
  | _, _, _, _, r, .up n => by simp only [Norm.rename, Norm.embed, Norm.embed_rename r n]
  | _, _, _, _, r, .lam n => by
      simp only [Norm.rename, Norm.embed, Tm.rename, Norm.embed_rename r.lift n]
  | _, _, _, _, _, .tt => rfl
  | _, _, _, _, _, .ff => rfl
  | _, _, _, _, _, .bot => rfl
  | _, _, _, _, r, .ite c a b => by
      simp only [Norm.rename, Norm.embed, Tm.rename, Norm.embed_rename r c,
        Norm.embed_rename r a, Norm.embed_rename r b]

/-! ## Normalisation by evaluation -/

/-- Kripke semantic values. -/
def V : Ty → Ctx → Type
  | .B, Γ => Norm Γ .B true
  | .arr σ τ, Γ => ∀ Δ, Ren Γ Δ → V σ Δ → V τ Δ

def V.ren : {τ : Ty} → {Γ Δ : Ctx} → Ren Γ Δ → V τ Γ → V τ Δ
  | .B, _, _, r, v => Norm.rename r v
  | .arr _ _, _, _, r, v => fun Θ s a => v Θ (Ren.comp s r) a

/-- Reflection of neutral terms and reification of values, by recursion on types. -/
def rr : (τ : Ty) → (∀ Γ, Norm Γ τ false → V τ Γ) × (∀ Γ, V τ Γ → Norm Γ τ true)
  | .B => (fun _ n => .up n, fun _ v => v)
  | .arr σ τ =>
      (fun _ n => fun Δ r a => (rr τ).1 Δ (.app (n.rename r) ((rr σ).2 Δ a)),
       fun Γ v => .lam ((rr τ).2 (σ :: Γ) (v (σ :: Γ) Ren.wk ((rr σ).1 (σ :: Γ) (.var .vz)))))

def reflect {Γ : Ctx} {τ : Ty} (n : Norm Γ τ false) : V τ Γ := (rr τ).1 Γ n
def reify {Γ : Ctx} {τ : Ty} (v : V τ Γ) : Norm Γ τ true := (rr τ).2 Γ v

def VEnv (Γ Δ : Ctx) : Type := ∀ τ, Var Γ τ → V τ Δ

def VEnv.cons {Γ Δ : Ctx} {σ : Ty} (ρ : VEnv Γ Δ) (a : V σ Δ) : VEnv (σ :: Γ) Δ
  | _, .vz => a
  | _, .vs x => ρ _ x

def VEnv.ren {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (ρ : VEnv Γ Δ) : VEnv Γ Θ := fun _ x => V.ren r (ρ _ x)

def eval : {Γ Δ : Ctx} → {τ : Ty} → Tm Γ τ → VEnv Γ Δ → V τ Δ
  | _, _, _, .var x, ρ => ρ _ x
  | _, _, .arr _ _, .lam M, ρ => fun _ r a => eval M (VEnv.cons (VEnv.ren r ρ) a)
  | _, Δ, _, .app M N, ρ => (eval M ρ) Δ (Ren.id Δ) (eval N ρ)
  | _, _, _, .tt, _ => (Norm.tt : Norm _ .B true)
  | _, _, _, .ff, _ => (Norm.ff : Norm _ .B true)
  | _, _, _, .bot, _ => (Norm.bot : Norm _ .B true)
  | _, _, _, .ite C M N, ρ =>
      (Norm.ite (eval C ρ : Norm _ .B true) (eval M ρ : Norm _ .B true) (eval N ρ : Norm _ .B true) :
        Norm _ .B true)

/-- The normal form of a term. -/
def Tm.nf {Γ : Ctx} {τ : Ty} (M : Tm Γ τ) : Norm Γ τ true :=
  reify (eval M (fun _ x => reflect (.var x)))

/-! ## Soundness -/

/-- The Kripke logical relation between values and Sieber semantics. -/
def Rel : (τ : Ty) → (Γ : Ctx) → V τ Γ → (Env Γ → (Model τ).car) → Prop
  | .B, _, v, f => ∀ ρ, (Norm.embed (v : Norm _ .B true)).sem.1 ρ = f ρ
  | .arr σ τ, Γ, v, f => ∀ Δ (r : Ren Γ Δ) a g, Rel σ Δ a g →
      Rel τ Δ (v Δ r a) (fun ρ => (f (Env.ren r ρ)).1 (g ρ))

theorem Rel.congr : ∀ {τ : Ty} {Γ : Ctx} {v : V τ Γ} {f g : Env Γ → (Model τ).car},
    (∀ ρ, f ρ = g ρ) → Rel τ Γ v f → Rel τ Γ v g
  | .B, _, _, _, _, hfg, h => fun ρ => (h ρ).trans (hfg ρ)
  | .arr _ _, _, _, _, _, hfg, h => fun Δ r a k hak => by
      have := h Δ r a k hak
      simp only [hfg] at this
      exact this

theorem Rel.ren : ∀ {τ : Ty} {Γ Δ : Ctx} (r : Ren Γ Δ) {v : V τ Γ} {f : Env Γ → (Model τ).car},
    Rel τ Γ v f → Rel τ Δ (V.ren r v) (fun ρ => f (Env.ren r ρ))
  | .B, _, _, r, v, f, h => fun ρ => by
      show (Norm.embed (Norm.rename r (v : Norm _ .B true))).sem.1 ρ = _
      rw [Norm.embed_rename, Tm.sem_rename]
      exact h _
  | .arr _ _, _, _, r, v, f, h => fun Θ s a g hag => by
      have := h Θ (Ren.comp s r) a g hag
      simp only [Env.ren_comp] at this
      exact this

theorem reflect_reify : ∀ (τ : Ty),
    (∀ (Γ : Ctx) (n : Norm Γ τ false), Rel τ Γ (reflect n) (fun ρ => n.embed.sem.1 ρ)) ∧
    (∀ (Γ : Ctx) (v : V τ Γ) (f : Env Γ → (Model τ).car), Rel τ Γ v f →
      ∀ ρ, (reify v).embed.sem.1 ρ = f ρ)
  | .B => ⟨fun _ n ρ => rfl, fun _ _ _ h => h⟩
  | .arr σ τ => by
      obtain ⟨reflσ, reifσ⟩ := reflect_reify σ
      obtain ⟨reflτ, reifτ⟩ := reflect_reify τ
      constructor
      · intro Γ n Δ r a g hag
        apply Rel.congr _ (reflτ Δ (.app (n.rename r) (reify a)))
        intro ρ
        simp only [Norm.embed, Tm.sem]
        rw [Norm.embed_rename, Tm.sem_rename, reifσ Δ a g hag ρ]
      · intro Γ v f h ρ
        apply Model.arr_ext
        intro a
        have hvz : Rel σ (σ :: Γ) (reflect (.var .vz)) (fun ρ' => ρ'.2) := by
          apply Rel.congr _ (reflσ (σ :: Γ) (.var .vz))
          intro ρ'; simp only [Norm.embed, Tm.sem, Var.sem]
        have key := reifτ (σ :: Γ) _ _ (h (σ :: Γ) Ren.wk _ _ hvz) (ρ, a)
        show ((Norm.embed (Norm.lam (reify (v (σ :: Γ) Ren.wk (reflect (.var .vz)))))).sem.1 ρ).1 a = _
        simp only [Norm.embed, Tm.sem]
        rw [key]
        show (f (Env.ren (fun τ x => .vs (Ren.id Γ τ x)) ((ρ, a) : Env (σ :: Γ)))).1 a = (f ρ).1 a
        rw [Env.ren_wk, Env.ren_id]

theorem eval_rel : ∀ {Γ Δ : Ctx} {τ : Ty} (M : Tm Γ τ) (ρv : VEnv Γ Δ) (ρs : Env Δ → Env Γ),
    (∀ τ (x : Var Γ τ), Rel τ Δ (ρv τ x) (fun ρ => x.sem.1 (ρs ρ))) →
    Rel τ Δ (eval M ρv) (fun ρ => M.sem.1 (ρs ρ))
  | _, _, _, .var x, ρv, ρs, h => by
      simp only [eval, Tm.sem]; exact h _ x
  | _, _, .arr σ τ, .lam M, ρv, ρs, h => by
      intro Θ r a g hag
      simp only [eval]
      apply Rel.congr _ (eval_rel M (VEnv.cons (VEnv.ren r ρv) a)
        (fun ρ => (ρs (Env.ren r ρ), g ρ)) ?_)
      · intro ρ; simp only [Tm.sem]
      · intro τ' x
        cases x with
        | vz => exact Rel.congr (fun ρ => rfl) hag
        | vs x => exact Rel.ren r (h _ x)
  | _, Δ, _, .app M N, ρv, ρs, h => by
      simp only [eval]
      have hM := eval_rel M ρv ρs h Δ (Ren.id Δ) _ _ (eval_rel N ρv ρs h)
      apply Rel.congr _ hM
      intro ρ
      simp only [Tm.sem, Env.ren_id]
  | _, _, _, .tt, _, _, _ => fun _ => by simp only [eval, Norm.embed, Tm.sem, constSem]
  | _, _, _, .ff, _, _, _ => fun _ => by simp only [eval, Norm.embed, Tm.sem, constSem]
  | _, _, _, .bot, _, _, _ => fun _ => by simp only [eval, Norm.embed, Tm.sem, constSem]
  | _, _, _, .ite C M N, ρv, ρs, h => fun ρ => by
      have hC := eval_rel C ρv ρs h ρ
      have hM := eval_rel M ρv ρs h ρ
      have hN := eval_rel N ρv ρs h ρ
      simp only [eval, Norm.embed, Tm.sem] at hC hM hN ⊢
      rw [hC, hM, hN]

/-- **Normalisation is sound**: a term and its normal form have the same denotation. -/
theorem Tm.nf_sound {Γ : Ctx} {τ : Ty} (M : Tm Γ τ) (ρ : Env Γ) :
    M.nf.embed.sem.1 ρ = M.sem.1 ρ := by
  have hrel := eval_rel M (fun _ x => reflect (.var x)) (fun ρ => ρ) (fun τ x =>
    Rel.congr (fun ρ => by simp only [Norm.embed, Tm.sem]) ((reflect_reify τ).1 _ (.var x)))
  exact (reflect_reify τ).2 _ _ _ hrel ρ

/-- Definable elements are definable by normal forms. -/
theorem Definable.nf {τ : Ty} {f : SieberBool τ} (h : Definable f) :
    ∃ n : Norm [] τ true, n.embed.den = f := by
  obtain ⟨M, rfl⟩ := h
  exact ⟨M.nf, Tm.nf_sound M PUnit.unit⟩

end OR.Sieber
