import OR.Interpretation

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace OR

/-- Deterministic call-by-name PCF head reduction with strict ground primitives. -/
inductive Step : {τ : Ty} → Tm [] τ → Tm [] τ → Prop where
  | beta {σ τ : Ty} (M : Tm [σ] τ) (N : Tm [] σ) :
      Step (.app (.lam M) N) (Tm.subst (Sub.single N) M)
  | app {σ τ : Ty} {M M' : Tm [] (σ ⇒ τ)} (h : Step M M') (N : Tm [] σ) :
      Step (.app M N) (.app M' N)
  | fix {τ : Ty} (M : Tm [] (τ ⇒ τ)) : Step (.fix M) (.app M (.fix M))
  | succ {M M' : Tm [] .nat} : Step M M' → Step (.succ M) (.succ M')
  | pred {M M' : Tm [] .nat} : Step M M' → Step (.pred M) (.pred M')
  | predNumeral (n : ℕ) : Step (.pred (Tm.numeral (n + 1))) (Tm.numeral n)
  | ifz {C C' : Tm [] .nat} (h : Step C C') (M N : Tm [] .nat) :
      Step (.ifz C M N) (.ifz C' M N)
  | ifzZero (M N : Tm [] .nat) : Step (.ifz .zero M N) M
  | ifzSucc (n : ℕ) (M N : Tm [] .nat) : Step (.ifz (Tm.numeral (n + 1)) M N) N

/-- Reflexive-transitive closure, stated explicitly to avoid any closure API convention. -/
inductive Red : {τ : Ty} → Tm [] τ → Tm [] τ → Prop where
  | refl {τ : Ty} (M : Tm [] τ) : Red M M
  | tail {τ : Ty} {M N P : Tm [] τ} : Red M N → Step N P → Red M P

namespace Red

variable {τ σ : Ty} {M N P : Tm [] τ}

 theorem single (h : Step M N) : Red M N := .tail (.refl M) h

 theorem trans (hMN : Red M N) (hNP : Red N P) : Red M P := by
  induction hNP with
  | refl => exact hMN
  | tail h hstep ih => exact .tail ih hstep

 theorem app {M N : Tm [] (σ ⇒ τ)} (h : Red M N) (A : Tm [] σ) :
    Red (.app M A) (.app N A) := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact .tail ih (.app hstep A)

 theorem succ {M N : Tm [] .nat} (h : Red M N) : Red (.succ M) (.succ N) := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact .tail ih (.succ hstep)

 theorem pred {M N : Tm [] .nat} (h : Red M N) : Red (.pred M) (.pred N) := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact .tail ih (.pred hstep)

 theorem ifz {C C' : Tm [] .nat} (h : Red C C') (M N : Tm [] .nat) :
    Red (.ifz C M N) (.ifz C' M N) := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact .tail ih (.ifz hstep M N)

end Red

/-- Numeral-sensitive observation; it is not defined using denotational semantics. -/
def Eval (M : Tm [] .nat) (n : ℕ) : Prop := Red M (Tm.numeral n)

namespace Eval

variable {M N C : Tm [] .nat} {n q : ℕ}

 theorem numeral (n : ℕ) : Eval (Tm.numeral n) n := Red.refl _

 theorem succ (h : Eval M n) : Eval (.succ M) (n + 1) := Red.succ h

 theorem predSucc (h : Eval M (n + 1)) : Eval (.pred M) n :=
  (Red.pred h).trans (Red.single (.predNumeral n))

 theorem ifzZero (hC : Eval C 0) (hM : Eval M q) : Eval (.ifz C M N) q :=
  (Red.ifz hC M N).trans ((Red.single (.ifzZero M N)).trans hM)

 theorem ifzSucc (hC : Eval C (n + 1)) (hN : Eval N q) : Eval (.ifz C M N) q :=
  (Red.ifz hC M N).trans ((Red.single (.ifzSucc n M N)).trans hN)

 theorem backward (h : Red M N) (hN : Eval N n) : Eval M n := h.trans hN

end Eval

noncomputable section

namespace Step

 theorem sound {τ : Ty} {M N : Tm [] τ} (h : Step M N) : denoteClosed M = denoteClosed N := by
  induction h with
  | beta M N => exact denote_beta M N PUnit.unit
  | app h N ih => exact congrArg (fun f => f (denoteClosed N)) ih
  | fix M => exact (Hom.fixMap_unfold _ (denoteClosed M)).symm
  | succ h ih => exact congrArg Ground.succ ih
  | pred h ih => exact congrArg Ground.pred ih
  | predNumeral n => simp only [denoteClosed, denote_pred, denote_numeral, Ground.pred_succ]
  | ifz h M N ih => exact congrArg (fun d => Ground.ifz d (denoteClosed M) (denoteClosed N)) ih
  | ifzZero M N => rfl
  | ifzSucc n M N => simp only [denoteClosed, denote_ifz, denote_numeral, Ground.ifz_succ]

end Step

namespace Red

 theorem sound {τ : Ty} {M N : Tm [] τ} (h : Red M N) : denoteClosed M = denoteClosed N := by
  induction h with
  | refl => rfl
  | tail h hstep ih => exact ih.trans hstep.sound

end Red

namespace Eval

 theorem sound {M : Tm [] .nat} {n : ℕ} (h : Eval M n) : denoteClosed M = .val n :=
  (Red.sound h).trans (denote_numeral (Γ := []) n PUnit.unit)

 theorem unique {M : Tm [] .nat} {m n : ℕ} (hm : Eval M m) (hn : Eval M n) : m = n :=
  Flat.val.inj (hm.sound.symm.trans hn.sound)

end Eval

end

end OR
