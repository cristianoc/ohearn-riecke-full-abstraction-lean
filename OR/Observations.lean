import OR.Adequacy

/-!
# Termination-only observations

Numeral tests show that observing only termination at ground type gives exactly
the same contextual preorder as observing which numeral is returned.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR

 def numeralTestTerm : ℕ → Tm [] (.nat ⇒ .nat)
  | 0 => .lam (.ifz (.var .vz) .zero (Tm.omega .nat))
  | n + 1 => .lam (.ifz (.var .vz) (Tm.omega .nat)
      (.app (Tm.closed (numeralTestTerm n)) (.pred (.var .vz))))

 def numeralTest (n : ℕ) : Hom Obj.nat Obj.nat := denoteClosed (numeralTestTerm n)

 theorem numeralTest_zero (d : Ground) :
    numeralTest 0 d = Ground.ifz d (.val 0) .bot := by
  simp only [numeralTest, numeralTestTerm, denoteClosed, denote_lam, denote_ifz,
    denote_var, lookup, denote_zero, denote_omega]
  rfl

 theorem numeralTest_succ (n : ℕ) (d : Ground) :
    numeralTest (n + 1) d = Ground.ifz d .bot (numeralTest n (Ground.pred d)) := by
  simp only [numeralTest, numeralTestTerm, denoteClosed, denote_lam, denote_ifz,
    denote_var, lookup, denote_omega, denote_app, denote_closed, denote_pred]
  rfl

 theorem numeralTest_spec (n : ℕ) (d : Ground) :
    numeralTest n d = if d = .val n then .val 0 else .bot := by
  classical
  induction n generalizing d with
  | zero =>
      rw [numeralTest_zero]
      cases d with
      | bot => simp only [Ground.ifz_bot, reduceCtorEq, if_false]
      | val k => cases k <;> simp [Ground.ifz]
  | succ n ih =>
      rw [numeralTest_succ]
      cases d with
      | bot => simp only [Ground.ifz_bot, reduceCtorEq, if_false]
      | val k =>
          cases k with
          | zero => simp [Ground.ifz]
          | succ k =>
              rw [Ground.ifz_succ, Ground.pred_succ, ih]
              simp only [Flat.val.injEq, Nat.succ.injEq]

 def Terminates (M : Tm [] .nat) : Prop := ∃ n : ℕ, Eval M n

 theorem numeralTest_terminates_iff (n : ℕ) (M : Tm [] .nat) :
    Terminates (.app (numeralTestTerm n) M) ↔ Eval M n := by
  classical
  constructor
  · rintro ⟨q, hq⟩
    have hd := (adequacy (.app (numeralTestTerm n) M) q).mp hq
    change numeralTest n (denoteClosed M) = .val q at hd
    rw [numeralTest_spec] at hd
    by_cases hm : denoteClosed M = .val n
    · exact (adequacy M n).mpr hm
    · simp only [hm, if_false, reduceCtorEq] at hd
  · intro hm
    refine ⟨0, (adequacy _ 0).mpr ?_⟩
    change numeralTest n (denoteClosed M) = .val 0
    rw [numeralTest_spec, (adequacy M n).mp hm, if_pos rfl]

 def ContextualTerminationLE {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) : Prop :=
  ∀ C : PCtx Γ τ [] .nat, Terminates (C.plug M) → Terminates (C.plug N)

 theorem contextual_termination_iff_op {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualTerminationLE M N ↔ ContextualOpLE M N := by
  constructor
  · intro h C n hn
    let E : PCtx Γ τ [] .nat := .appR (numeralTestTerm n) C
    have hEM : Terminates (E.plug M) :=
      (numeralTest_terminates_iff n (C.plug M)).mpr hn
    have hEN := h E hEM
    exact (numeralTest_terminates_iff n (C.plug N)).mp hEN
  · intro h C hM
    obtain ⟨n, hn⟩ := hM
    exact ⟨n, h C n hn⟩

 theorem full_abstraction_termination {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualTerminationLE M N ↔ denote M ≤ denote N :=
  (contextual_termination_iff_op M N).trans (full_abstraction_op M N)

end OR
