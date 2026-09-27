import OR.Operational
import OR.FullAbstraction

/-!
# Computational adequacy and operational full abstraction

`Comp` relates semantic elements to independently defined operational terms.
In particular, neither `Eval` nor `Comp` is defined by contextual equivalence.
The fixed-point case is proved using bottom, iteration, backward closure, and
admissibility; there is no adequacy hypothesis in the model.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

noncomputable section

namespace OR

/-- The standard call-by-name computational logical relation. -/
def Comp : (τ : Ty) → D τ → Tm [] τ → Prop
  | .nat, d, M => ∀ n : ℕ, d = .val n → Eval M n
  | .arr σ τ, f, M =>
      ∀ (a : D σ) (N : Tm [] σ), Comp σ a N → Comp τ (f a) (.app M N)

namespace Comp

 theorem bottom : ∀ (τ : Ty) (M : Tm [] τ), Comp τ ⊥ M := by
  intro τ
  induction τ with
  | nat =>
      intro M n h
      cases h
  | arr σ τ ihσ ihτ =>
      intro M a N _
      exact ihτ (.app M N)

/-- Directed closure is proved at every type, for each fixed syntactic term. -/
 theorem dsup : ∀ (τ : Ty) (M : Tm [] τ) (s : Set (D τ)) (hs : Dir s),
    (∀ d ∈ s, Comp τ d M) → Comp τ (dSup s hs) M := by
  intro τ
  induction τ with
  | nat =>
      intro M s hs h n hn
      exact h (.val n) (Flat.val_mem_of_dSup_eq hs hn) n rfl
  | arr σ τ ihσ ihτ =>
      intro M s hs h a N ha
      change Comp τ ((dSup s hs) a) (.app M N)
      rw [Hom.dSup_apply]
      apply ihτ (.app M N)
      rintro _ ⟨f, hf, rfl⟩
      exact h f hf a N ha

 theorem chain {τ : Ty} (M : Tm [] τ) (c : Chain (D τ))
    (h : ∀ n, Comp τ (c n) M) : Comp τ c.sup M := by
  apply dsup τ M (Set.range c.at) c.dir
  rintro _ ⟨n, rfl⟩
  exact h n

/-- Backward closure includes application of the same closed argument. -/
 theorem backward : ∀ (τ : Ty) {M N : Tm [] τ} {d : D τ},
    Red M N → Comp τ d N → Comp τ d M := by
  intro τ
  induction τ with
  | nat =>
      intro M N d h hN n hn
      exact Eval.backward h (hN n hn)
  | arr σ τ ihσ ihτ =>
      intro M N f h hN a A ha
      exact ihτ (Red.app h A) (hN a A ha)

 theorem backwardStep {τ : Ty} {M N : Tm [] τ} {d : D τ}
    (h : Step M N) (hN : Comp τ d N) : Comp τ d M :=
  backward τ (Red.single h) hN

end Comp

/-- A semantic environment is related pointwise to a closing substitution. -/
def EnvComp {Γ : Ctx} (ρ : Env Γ) (θ : Sub Γ []) : Prop :=
  ∀ {τ : Ty} (x : Var Γ τ), Comp τ (lookup x ρ) (θ x)

 theorem envComp_extend {Γ : Ctx} {σ : Ty} {ρ : Env Γ} {θ : Sub Γ []}
    {a : D σ} {N : Tm [] σ} (hρ : EnvComp ρ θ) (ha : Comp σ a N) :
    EnvComp (ρ, a) (Sub.extend θ N) := by
  intro τ x
  cases x with
  | vz => exact ha
  | vs x => exact hρ x

/-- Every term is computationally related to its interpretation. -/
 theorem fundamental {Γ : Ctx} {τ : Ty} (M : Tm Γ τ) :
    ∀ (ρ : Env Γ) (θ : Sub Γ []), EnvComp ρ θ →
      Comp τ (denote M ρ) (Tm.subst θ M) := by
  induction M with
  | var x =>
      intro ρ θ hρ
      exact hρ x
  | @lam Γ σ τ M ih =>
      intro ρ θ hρ a N ha
      have hb := ih (ρ, a) (Sub.extend θ N) (envComp_extend hρ ha)
      have hs : Step (.app (.lam (Tm.subst (Sub.lift θ) M)) N)
          (Tm.subst (Sub.extend θ N) M) := by
        simpa only [Tm.subst_lift_single] using
          (Step.beta (Tm.subst (Sub.lift θ) M) N)
      exact Comp.backwardStep hs hb
  | app M N ihM ihN =>
      intro ρ θ hρ
      exact ihM ρ θ hρ (denote N ρ) (Tm.subst θ N) (ihN ρ θ hρ)
  | @fix Γ τ F ih =>
      intro ρ θ hρ
      let f : Hom (typeObj τ) (typeObj τ) := denote F ρ
      let F' : Tm [] (τ ⇒ τ) := Tm.subst θ F
      let X : Tm [] τ := .fix F'
      have hf : Comp (τ ⇒ τ) f F' := ih ρ θ hρ
      have hi : ∀ n : ℕ, Comp τ (iterate f.val n) X := by
        intro n
        induction n with
        | zero => exact Comp.bottom τ X
        | succ n ihn =>
            exact Comp.backwardStep (Step.fix F') (hf (iterate f.val n) X ihn)
      have hlim : Comp τ (lfp f.val) X :=
        Comp.chain X (iterChain f.val) hi
      change Comp τ (Hom.fixMap (typeObj τ) f) X
      rw [Hom.fixMap_apply]
      exact hlim
  | zero =>
      intro ρ θ hρ n hn
      have h0 : (0 : ℕ) = n := Flat.val.inj hn
      subst n
      exact Eval.numeral 0
  | succ M ih =>
      intro ρ θ hρ n hn
      have hM := ih ρ θ hρ
      change Ground.succ (denote M ρ) = .val n at hn
      cases hd : denote M ρ with
      | bot => simp only [hd, Ground.succ] at hn
      | val k =>
          have hk : k + 1 = n := by
            simpa only [hd, Ground.succ, Flat.val.injEq] using hn
          subst n
          exact Eval.succ (hM k hd)
  | pred M ih =>
      intro ρ θ hρ n hn
      have hM := ih ρ θ hρ
      change Ground.pred (denote M ρ) = .val n at hn
      cases hd : denote M ρ with
      | bot => simp only [hd, Ground.pred] at hn
      | val k =>
          cases k with
          | zero => simp only [hd, Ground.pred] at hn
          | succ k =>
              have hk : k = n := by
                simpa only [hd, Ground.pred, Flat.val.injEq] using hn
              subst n
              exact Eval.predSucc (hM (k + 1) hd)
  | ifz C M N ihC ihM ihN =>
      intro ρ θ hρ n hn
      have hC := ihC ρ θ hρ
      have hM := ihM ρ θ hρ
      have hN := ihN ρ θ hρ
      change Ground.ifz (denote C ρ) (denote M ρ) (denote N ρ) = .val n at hn
      cases hd : denote C ρ with
      | bot => simp only [hd, Ground.ifz] at hn
      | val k =>
          cases k with
          | zero =>
              have hm : denote M ρ = .val n := by
                simpa only [hd, Ground.ifz] using hn
              exact Eval.ifzZero (hC 0 hd) (hM n hm)
          | succ k =>
              have hn' : denote N ρ = .val n := by
                simpa only [hd, Ground.ifz] using hn
              exact Eval.ifzSucc (hC (k + 1) hd) (hN n hn')

/-- The operational/denotational bridge, including recursive programs. -/
 theorem adequacy (M : Tm [] .nat) (n : ℕ) :
    Eval M n ↔ denoteClosed M = .val n := by
  constructor
  · exact Eval.sound
  · intro h
    have henv : EnvComp (Γ := []) PUnit.unit Sub.id := by
      intro τ x
      exact nomatch x
    have hm := fundamental M PUnit.unit Sub.id henv
    simpa only [Tm.subst_id] using hm n h

 def ContextualOpLE {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) : Prop :=
  ∀ C : PCtx Γ τ [] .nat, ∀ n : ℕ, Eval (C.plug M) n → Eval (C.plug N) n

 def ContextualOpEq {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) : Prop :=
  ContextualOpLE M N ∧ ContextualOpLE N M

 theorem contextual_op_iff_den {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualOpLE M N ↔ ContextualDenLE M N := by
  constructor
  · intro h C
    apply (Flat.observed_order _ _).mpr
    intro n hn
    exact (adequacy (C.plug N) n).mp (h C n ((adequacy (C.plug M) n).mpr hn))
  · intro h C n hn
    apply (adequacy (C.plug N) n).mpr
    have horder := h C
    rw [(adequacy (C.plug M) n).mp hn] at horder
    exact (Flat.val_le_iff n _).mp horder

/-- O'Hearn--Riecke full abstraction, with operational observations and open terms. -/
 theorem full_abstraction_op {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualOpLE M N ↔ denote M ≤ denote N :=
  (contextual_op_iff_den M N).trans (full_abstraction_den M N)

 theorem full_abstraction_op_eq {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualOpEq M N ↔ denote M = denote N := by
  constructor
  · rintro ⟨hMN, hNM⟩
    exact le_antisymm ((full_abstraction_op M N).mp hMN)
      ((full_abstraction_op N M).mp hNM)
  · intro h
    exact ⟨(full_abstraction_op M N).mpr h.le,
      (full_abstraction_op N M).mpr h.symm.le⟩

/-- Pointwise statement: the order on morphisms is not an extra observation. -/
 theorem full_abstraction_op_pointwise {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualOpLE M N ↔ ∀ ρ : Env Γ, denote M ρ ≤ denote N ρ :=
  full_abstraction_op M N

 theorem operational_separator {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ)
    (h : ¬ denote M ≤ denote N) :
    ∃ C : PCtx Γ τ [] .nat, ∃ n : ℕ,
      Eval (C.plug M) n ∧ ¬ Eval (C.plug N) n := by
  obtain ⟨C, n, hM, hN⟩ := semantic_separator M N h
  exact ⟨C, n, (adequacy (C.plug M) n).mpr hM,
    fun he => hN ((adequacy (C.plug N) n).mp he)⟩

end OR
