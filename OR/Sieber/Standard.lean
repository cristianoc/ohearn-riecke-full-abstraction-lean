import OR.Sieber.Syntax

/-!
# Observational equivalence of finitary PCF

Ground values are `⊥`, `tt`, `ff`. A closed term of ground type reduces to one
of the normal forms `tt`, `ff`, `⊥`; the full set-theoretic model below, in
which the conditional is strict in its test, computes exactly that normal form
(β-reduction is sound for it and the three normal forms denote themselves).
So observational equivalence can be stated with it directly.

For closed terms, observing `M` in every ground context `C[·]` is the same as
observing `K M` for every closed `K : τ ⇒ B` (take `K = λx. C[x]`).

`Loader` is the statement of Loader's theorem (TCS 266, 2001) that observational
equivalence of finitary PCF is undecidable, phrased with Mathlib's
`ComputablePred` on pairs of term codes.
-/

set_option autoImplicit false

namespace OR.Sieber

inductive Val where
  | bot | tt | ff
  deriving DecidableEq, Fintype

/-- Strict conditional. -/
def Val.ite : Val → Val → Val → Val
  | .bot, _, _ => .bot
  | .tt, a, _ => a
  | .ff, _, b => b

/-- The full set-theoretic type hierarchy over `Val`. -/
def Std : Ty → Type
  | .B => Val
  | .arr σ τ => Std σ → Std τ

def StdEnv : Ctx → Type
  | [] => PUnit
  | σ :: Γ => StdEnv Γ × Std σ

def Var.std : {Γ : Ctx} → {τ : Ty} → Var Γ τ → StdEnv Γ → Std τ
  | _ :: _, _, .vz, ρ => ρ.2
  | _ :: _, _, .vs x, ρ => x.std ρ.1

def Tm.std : {Γ : Ctx} → {τ : Ty} → Tm Γ τ → StdEnv Γ → Std τ
  | _, _, .var x, ρ => x.std ρ
  | _, _, .lam M, ρ => fun a => M.std (ρ, a)
  | _, _, .app M N, ρ => M.std ρ (N.std ρ)
  | _, _, .tt, _ => Val.tt
  | _, _, .ff, _ => Val.ff
  | _, _, .bot, _ => Val.bot
  | _, _, .ite C M N, ρ => Val.ite (C.std ρ) (M.std ρ) (N.std ρ)

/-- The observed value of a closed ground term. -/
def Tm.obs (M : Tm [] .B) : Val := M.std PUnit.unit

/-- Observational equivalence of closed terms. -/
def ObsEquiv {τ : Ty} (M N : Tm [] τ) : Prop :=
  ∀ K : Tm [] (τ ⇒ .B), (Tm.app K M).obs = (Tm.app K N).obs

/-- Observational equivalence on term codes: `a` and `b` code closed terms of
the same type that are observationally equivalent. -/
def ObsEquivCode (a b : ℕ) : Prop :=
  ∃ (τ : Ty) (M N : Tm [] τ), M.code = a ∧ N.code = b ∧ ObsEquiv M N

/-- **Loader's theorem**: observational equivalence of finitary PCF is undecidable. -/
def Loader : Prop := ¬ ComputablePred (fun p : ℕ × ℕ => ObsEquivCode p.1 p.2)

end OR.Sieber
