import OR.Sieber.Transfer

/-!
# Grade-1 game terms and their Boolean reading (Lemma 11)

`SIEBER.md`, Section 4.6.  A grade-1 game term is built from `⊥`, the numerals `0`
and `1`, variables, abstraction, application and the strict case `case₁(z; N₀, N₁)`.
These are exactly the images of Boolean terms under `embed`, which reads `tt` as
`0`, `ff` as `1` and `ite z N₀ N₁` as `case₁(z; N₀, N₁)`.  So the Boolean
translation `G ↦ Gᴮ` of the paper is the inverse of `embed`.

Equation (16) of the paper, `⟦G⟧ₙ(iρ) = i(⟦Gᴮ⟧_B ρ)`, fails at arrow types
(`⟦λx. x⟧ₙ` is the identity, while `i id = ψ¹`).  What the argument uses holds
all the same, through the logical relation `LRel`: `LRel (i a) a`, and `LRel x b`
implies `r x = b`.
-/

namespace OR.Sieber

open OR.NS

def natCtx : Ctx → OR.Ctx
  | [] => []
  | σ :: Γ => natTy σ :: natCtx Γ

def natVar : {Γ : Ctx} → {τ : Ty} → Var Γ τ → OR.Var (natCtx Γ) (natTy τ)
  | _ :: _, _, .vz => .vz
  | _ :: _, _, .vs x => .vs (natVar x)

/-- `case₁(z; N₀, N₁)`: `N₀` on `0`, `N₁` on `1`, divergence otherwise. -/
def case1 {Γ : OR.Ctx} (z n0 n1 : OR.Tm Γ .nat) : OR.Tm Γ .nat :=
  .ifz z n0 (.ifz (.pred z) n1 (.omega .nat))

/-- The grade-1 game term denoted by a Boolean term. -/
def embed : {Γ : Ctx} → {τ : Ty} → Tm Γ τ → OR.Tm (natCtx Γ) (natTy τ)
  | _, _, .var x => .var (natVar x)
  | _, .arr _ _, .lam M => .lam (embed M)
  | _, _, .app M N => .app (embed M) (embed N)
  | _, _, .tt => .zero
  | _, _, .ff => .succ .zero
  | _, _, .bot => .omega .nat
  | _, _, .ite C M N => case1 (embed C) (embed M) (embed N)

/-- The logical relation between the natural and the Boolean model. -/
def LRel : (τ : Ty) → NS.D (natTy τ) → SieberBool τ → Prop
  | .B, x, b => qv x = b
  | .arr σ ρ, F, f =>
      ∀ x a, LRel σ x a → LRel ρ ((show NS.D (natTy σ ⇒ natTy ρ) from F) x) (f.1 a)

theorem lrel_i_r : ∀ τ : Ty, (∀ a, LRel τ ((tr τ).i a) a) ∧ (∀ x b, LRel τ x b → (tr τ).r x = b)
  | .B => ⟨fun a => qv_jv a, fun _ _ h => h⟩
  | .arr σ ρ => by
      obtain ⟨hσi, hσr⟩ := lrel_i_r σ
      obtain ⟨hρi, hρr⟩ := lrel_i_r ρ
      refine ⟨fun f x a hxa => ?_, fun F f hF => ?_⟩
      · change LRel ρ ((tr ρ).i (f.1 ((tr σ).r x))) (f.1 a)
        rw [hσr x a hxa]
        exact hρi _
      · apply Subtype.ext
        funext a
        exact hρr _ _ (hF _ a (hσi a))

theorem lrel_i (τ : Ty) (a : SieberBool τ) : LRel τ ((tr τ).i a) a := (lrel_i_r τ).1 a

theorem lrel_r (τ : Ty) {x : NS.D (natTy τ)} {b : SieberBool τ} (h : LRel τ x b) :
    (tr τ).r x = b := (lrel_i_r τ).2 x b h

def LEnvRel : (Γ : Ctx) → NS.Env (natCtx Γ) → Env Γ → Prop
  | [], _, _ => True
  | σ :: Γ, η, ρ =>
      LEnvRel Γ (show NS.Env (natCtx Γ) × NS.D (natTy σ) from η).1 ρ.1 ∧
        LRel σ (show NS.Env (natCtx Γ) × NS.D (natTy σ) from η).2 ρ.2

theorem Var.lrel : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (η : NS.Env (natCtx Γ)) (ρ : Env Γ),
    LEnvRel Γ η ρ → LRel τ (NS.lookup (natVar x) η) (x.sem.1 ρ)
  | _ :: _, _, .vz, _, _, h => h.2
  | _ :: _, _, .vs x, _, _, h => Var.lrel x _ _ h.1

theorem case1_rel {z n0 n1 : Ground} {c a b : Val} (hz : qv z = c) (h0 : qv n0 = a)
    (h1 : qv n1 = b) :
    qv (Ground.ifz z n0 (Ground.ifz (Ground.pred z) n1 ⊥)) = Val.ite c a b := by
  subst hz h0 h1
  rcases z with _ | _ | _ | k <;> rfl

/-- **Lemma 11**, in logical-relation form. -/
theorem Tm.lrel : ∀ {Γ : Ctx} {τ : Ty} (M : Tm Γ τ) (η : NS.Env (natCtx Γ)) (ρ : Env Γ),
    LEnvRel Γ η ρ → LRel τ (NS.denote (embed M) η) (M.sem.1 ρ)
  | _, _, .var x, η, ρ, h => by
      simp only [embed, NS.denote_var, Tm.sem]
      exact Var.lrel x η ρ h
  | _, .arr _ _, .lam M, η, ρ, h => fun x a hxa => Tm.lrel M (η, x) (ρ, a) ⟨h, hxa⟩
  | _, _, .app M N, η, ρ, h => by
      simp only [embed, Tm.sem]
      exact Tm.lrel M η ρ h _ _ (Tm.lrel N η ρ h)
  | _, _, .tt, _, _, _ => rfl
  | _, _, .ff, _, _, _ => rfl
  | _, _, .bot, _, _, _ => by
      change qv (NS.denote (OR.Tm.omega .nat) _) = .bot
      rw [NS.denote_omega]
      rfl
  | _, _, .ite C M N, η, ρ, h => by
      change qv (NS.denote (case1 (embed C) (embed M) (embed N)) η) = Val.ite _ _ _
      simp only [case1, NS.denote_ifz, NS.denote_pred, NS.denote_omega]
      exact case1_rel (Tm.lrel C η ρ h) (Tm.lrel M η ρ h) (Tm.lrel N η ρ h)

/-- For a closed Boolean term `G`, `⟦embed G⟧ₙ = i h` forces `⟦G⟧_B = h`. -/
theorem den_of_embed {τ : Ty} (G : Tm [] τ) (h : SieberBool τ)
    (hG : NS.denoteClosed (embed G) = (tr τ).i h) : G.den = h := by
  have hrel := Tm.lrel G PUnit.unit PUnit.unit trivial
  have hx : NS.denote (embed G) PUnit.unit = NS.denoteClosed (embed G) := rfl
  rw [hx, hG] at hrel
  change G.sem.1 PUnit.unit = h
  rw [← lrel_r τ hrel, (tr τ).r_i]

end OR.Sieber
