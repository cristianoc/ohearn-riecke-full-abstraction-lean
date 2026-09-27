import Mathlib

/-!
# Finitary PCF

Loader's finitary PCF: the simply typed λ-calculus over a single ground type
`B`, with constants `tt`, `ff`, `⊥` of ground type and a conditional
`if · then · else ·` on ground terms. There is no fixed-point operator.

Terms are intrinsically typed with de Bruijn variables. `Tm.code` is an
injective numbering of terms, used to state decidability questions about terms
with Mathlib's computability predicates on `ℕ`.
-/

set_option autoImplicit false

namespace OR.Sieber

inductive Ty where
  | B : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq

infixr:70 " ⇒ " => Ty.arr

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | vz {Γ : Ctx} {σ : Ty} : Var (σ :: Γ) σ
  | vs {Γ : Ctx} {σ τ : Ty} : Var Γ τ → Var (σ :: Γ) τ

inductive Tm : Ctx → Ty → Type where
  | var {Γ : Ctx} {τ : Ty} : Var Γ τ → Tm Γ τ
  | lam {Γ : Ctx} {σ τ : Ty} : Tm (σ :: Γ) τ → Tm Γ (σ ⇒ τ)
  | app {Γ : Ctx} {σ τ : Ty} : Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  | tt {Γ : Ctx} : Tm Γ .B
  | ff {Γ : Ctx} : Tm Γ .B
  | bot {Γ : Ctx} : Tm Γ .B
  | ite {Γ : Ctx} : Tm Γ .B → Tm Γ .B → Tm Γ .B → Tm Γ .B

/-! ## Numbering -/

def Ty.code : Ty → ℕ
  | .B => 0
  | .arr σ τ => Nat.pair σ.code τ.code + 1

def Var.code {Γ : Ctx} {τ : Ty} : Var Γ τ → ℕ
  | .vz => 0
  | .vs x => x.code + 1

/-- Constructor tag in `n % 7`, arguments in `n / 7`. Types are recorded at
binders and applications, so a code determines the typed term. -/
def Tm.code {Γ : Ctx} {τ : Ty} : Tm Γ τ → ℕ
  | .var x => 7 * x.code
  | @Tm.lam _ σ _ M => 7 * Nat.pair σ.code M.code + 1
  | @Tm.app _ σ _ M N => 7 * Nat.pair σ.code (Nat.pair M.code N.code) + 2
  | .tt => 3
  | .ff => 4
  | .bot => 5
  | .ite C M N => 7 * Nat.pair C.code (Nat.pair M.code N.code) + 6

end OR.Sieber

namespace OR.Sieber

theorem Ty.code_injective : Function.Injective Ty.code := by
  intro σ τ h
  induction σ generalizing τ with
  | B => cases τ with
    | B => rfl
    | arr _ _ => simp [Ty.code] at h
  | arr σ₁ σ₂ ih₁ ih₂ => cases τ with
    | B => simp [Ty.code] at h
    | arr τ₁ τ₂ =>
        simp only [Ty.code, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
        rw [ih₁ h.1, ih₂ h.2]

theorem Var.code_inj : ∀ {Γ : Ctx} {τ τ' : Ty} (x : Var Γ τ) (y : Var Γ τ'),
    x.code = y.code → τ = τ' ∧ HEq x y
  | _ :: _, _, _, .vz, .vz, _ => ⟨rfl, HEq.rfl⟩
  | _ :: _, _, _, .vz, .vs _, h => by simp [Var.code] at h
  | _ :: _, _, _, .vs _, .vz, h => by simp [Var.code] at h
  | _ :: _, _, _, .vs x, .vs y, h => by
      obtain ⟨rfl, hxy⟩ := Var.code_inj x y (by simpa [Var.code] using h)
      exact ⟨rfl, by rw [eq_of_heq hxy]⟩

/-- A code determines the typed term it codes. -/
theorem Tm.code_inj {Γ : Ctx} {τ τ' : Ty} (M : Tm Γ τ) (N : Tm Γ τ') (h : M.code = N.code) :
    τ = τ' ∧ HEq M N := by
  induction M generalizing τ' with
  | var x =>
      cases N with
      | var y =>
          simp only [Tm.code] at h
          obtain ⟨rfl, hxy⟩ := Var.code_inj x y (by omega)
          exact ⟨rfl, by rw [eq_of_heq hxy]⟩
      | _ => simp only [Tm.code] at h; omega
  | @lam Γ σ _ M ih =>
      cases N with
      | @lam _ σ' _ N =>
          simp only [Tm.code] at h
          have h' := Nat.pair_eq_pair.mp (by omega : Nat.pair σ.code M.code = Nat.pair σ'.code N.code)
          obtain rfl := Ty.code_injective h'.1
          obtain ⟨rfl, hMN⟩ := ih N h'.2
          exact ⟨rfl, by rw [eq_of_heq hMN]⟩
      | _ => simp only [Tm.code] at h; omega
  | @app Γ σ _ M₁ M₂ ih₁ ih₂ =>
      cases N with
      | @app _ σ' _ N₁ N₂ =>
          simp only [Tm.code] at h
          have h' := Nat.pair_eq_pair.mp
            (by omega : Nat.pair σ.code (Nat.pair M₁.code M₂.code) = Nat.pair σ'.code (Nat.pair N₁.code N₂.code))
          obtain rfl := Ty.code_injective h'.1
          have h'' := Nat.pair_eq_pair.mp h'.2
          obtain ⟨hty, h₁⟩ := ih₁ N₁ h''.1
          obtain ⟨-, h₂⟩ := ih₂ N₂ h''.2
          cases hty
          exact ⟨rfl, by rw [eq_of_heq h₁, eq_of_heq h₂]⟩
      | _ => simp only [Tm.code] at h; omega
  | tt => cases N <;> simp only [Tm.code] at h <;> first | omega | exact ⟨rfl, HEq.rfl⟩
  | ff => cases N <;> simp only [Tm.code] at h <;> first | omega | exact ⟨rfl, HEq.rfl⟩
  | bot => cases N <;> simp only [Tm.code] at h <;> first | omega | exact ⟨rfl, HEq.rfl⟩
  | ite C M N' ihC ihM ihN =>
      cases N with
      | ite C₂ M₂ N₂ =>
          simp only [Tm.code] at h
          have h' := Nat.pair_eq_pair.mp
            (by omega : Nat.pair C.code (Nat.pair M.code N'.code) = Nat.pair C₂.code (Nat.pair M₂.code N₂.code))
          have h'' := Nat.pair_eq_pair.mp h'.2
          obtain ⟨-, hC⟩ := ihC C₂ h'.1
          obtain ⟨-, hM⟩ := ihM M₂ h''.1
          obtain ⟨-, hN⟩ := ihN N₂ h''.2
          exact ⟨rfl, by rw [eq_of_heq hC, eq_of_heq hM, eq_of_heq hN]⟩
      | _ => simp only [Tm.code] at h; omega

end OR.Sieber
