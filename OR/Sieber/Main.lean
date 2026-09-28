import OR.Sieber.Statement
import OR.Sieber.CheckComplete
import OR.Sieber.CheckPrim

/-!
# Sieber's model is not universal: the proof

Assuming every element of Sieber's model is definable, observational equivalence
of finitary PCF becomes computable: both it and its negation are witnessed by
finite certificates that a primitive recursive checker accepts. This contradicts
Loader's theorem.
-/

set_option autoImplicit false

namespace OR.Sieber

open Check

/-- A predicate witnessed by a primitive recursive test is recursively enumerable. -/
theorem rePred_of_primrec {p : ℕ × ℕ → Prop} {f : (ℕ × ℕ) × ℕ → Bool} (hf : Primrec f)
    (h : ∀ a, p a ↔ ∃ n, f (a, n) = true) : REPred p := by
  have hpart : Partrec fun a : ℕ × ℕ => Nat.rfind fun n => Part.some (f (a, n)) :=
    Partrec.rfind (hf.to_comp.partrec.to₂)
  refine REPred.of_eq (Partrec.dom_re hpart) fun a => ?_
  rw [h, Nat.rfind_dom]
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

/-- Decode a certificate and test whether its verdict is `v`. -/
def certTest (v : Bool) (x : (ℕ × ℕ) × ℕ) : Bool :=
  ((Encodable.decode x.2 : Option Cert).map fun cert => verdict x.1.1 x.1.2 cert == some v).getD false

theorem certTest_prim (v : Bool) : Primrec (certTest v) :=
  Primrec.option_getD.comp (Primrec.option_map (Primrec.decode.comp Primrec.snd)
    (Prim.beq'.comp (verdict_prim.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (Primrec.const (some v))).to₂) (Primrec.const false)

/-- Decode a typing certificate and test whether it shows the pair invalid. -/
def invalidTest (x : (ℕ × ℕ) × ℕ) : Bool :=
  ((Encodable.decode x.2 : Option (List TyEntry)).map fun tt => invalidPair x.1.1 x.1.2 tt).getD false

theorem invalidTest_prim : Primrec invalidTest :=
  Primrec.option_getD.comp (Primrec.option_map (Primrec.decode.comp Primrec.snd)
    (invalidPair_prim.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂)
    (Primrec.const false)

theorem certTest_iff (v : Bool) (a : ℕ × ℕ) :
    (∃ n, certTest v (a, n) = true) ↔ ∃ cert : Cert, verdict a.1 a.2 cert = some v := by
  constructor
  · rintro ⟨n, hn⟩
    unfold certTest at hn
    cases hd : (Encodable.decode n : Option Cert) with
    | none => rw [hd] at hn; cases hn
    | some cert =>
        rw [hd] at hn
        change (verdict a.1 a.2 cert == some v) = true at hn
        exact ⟨cert, beq_iff_eq.mp hn⟩
  · rintro ⟨cert, hc⟩
    refine ⟨Encodable.encode cert, ?_⟩
    unfold certTest
    rw [Encodable.encodek]
    change (verdict a.1 a.2 cert == some v) = true
    rw [hc]; exact beq_self_eq_true _

theorem invalidTest_iff (a : ℕ × ℕ) :
    (∃ n, invalidTest (a, n) = true) ↔ ∃ tt : List TyEntry, invalidPair a.1 a.2 tt = true := by
  constructor
  · rintro ⟨n, hn⟩
    unfold invalidTest at hn
    cases hd : (Encodable.decode n : Option (List TyEntry)) with
    | none => rw [hd] at hn; cases hn
    | some tt =>
        rw [hd] at hn
        exact ⟨tt, hn⟩
  · rintro ⟨tt, ht⟩
    refine ⟨Encodable.encode tt, ?_⟩
    unfold invalidTest
    rw [Encodable.encodek]
    exact ht

section
variable (U : Universal)
include U

theorem obsEquivCode_iff (a b : ℕ) :
    ObsEquivCode a b ↔ ∃ cert : Cert, verdict a b cert = some true := by
  constructor
  · rintro ⟨τ, M, N, rfl, rfl, hobs⟩
    obtain ⟨cert, hc⟩ := complete U M N
    refine ⟨cert, ?_⟩
    rw [hc, (universal_fully_abstract U M N).mp hobs]
    simp
  · rintro ⟨cert, hc⟩
    obtain ⟨τ, M, N, rfl, rfl, hr⟩ := verdict_sound hc
    exact ⟨τ, M, N, rfl, rfl, (universal_fully_abstract U M N).mpr (hr.mp rfl)⟩

theorem not_obsEquivCode_iff (a b : ℕ) :
    ¬ ObsEquivCode a b ↔ (∃ cert : Cert, verdict a b cert = some false) ∨
      ∃ tt : List TyEntry, invalidPair a b tt = true := by
  constructor
  · intro hne
    by_cases hv : ValidPair a b
    · obtain ⟨τ, M, N, rfl, rfl⟩ := hv
      left
      obtain ⟨cert, hc⟩ := complete U M N
      refine ⟨cert, ?_⟩
      rw [hc]
      have hden : M.den ≠ N.den := fun h =>
        hne ⟨τ, M, N, rfl, rfl, (universal_fully_abstract U M N).mpr h⟩
      have hidx : idx τ M.den ≠ idx τ N.den := fun h => hden (idx_inj τ h)
      simp [hidx]
    · right
      exact invalidPair_complete hv
  · rintro (⟨cert, hc⟩ | ⟨tt, ht⟩) ⟨τ', M', N', ha, hb, hobs⟩
    · obtain ⟨τ, M, N, hM, hN, hr⟩ := verdict_sound hc
      obtain ⟨hτ, hMM⟩ := Tm.code_inj M' M (ha.trans hM.symm)
      subst hτ
      obtain ⟨-, hNN⟩ := Tm.code_inj N' N (hb.trans hN.symm)
      rw [eq_of_heq hMM, eq_of_heq hNN] at hobs
      have := (universal_fully_abstract U M N).mp hobs
      exact absurd (hr.mpr this) (by simp)
    · exact invalidPair_sound ht ⟨τ', M', N', ha, hb⟩

theorem obsEquiv_computable : ComputablePred fun p : ℕ × ℕ => ObsEquivCode p.1 p.2 := by
  rw [ComputablePred.computable_iff_re_compl_re']
  constructor
  · exact rePred_of_primrec (certTest_prim true) fun a => by
      rw [obsEquivCode_iff U, certTest_iff]
  · have hf : Primrec fun x : (ℕ × ℕ) × ℕ => certTest false (x.1, x.2.unpair.1) || invalidTest (x.1, x.2.unpair.2) :=
      Primrec.or.comp ((certTest_prim false).comp (Primrec.pair Primrec.fst
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
        (invalidTest_prim.comp (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
    refine rePred_of_primrec hf fun a => ?_
    rw [not_obsEquivCode_iff U, ← certTest_iff, ← invalidTest_iff]
    constructor
    · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
      · exact ⟨Nat.pair n 0, by simp [Nat.unpair_pair, hn]⟩
      · exact ⟨Nat.pair 0 n, by simp [Nat.unpair_pair, hn]⟩
    · rintro ⟨n, hn⟩
      simp only [Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · exact Or.inl ⟨_, hn⟩
      · exact Or.inr ⟨_, hn⟩

end

/-- **Sieber's ordinary sequentiality relations do not give a universal model of
finitary PCF**: assuming Loader's theorem, some element of Sieber's model is not
the denotation of any closed term. -/
theorem sieber_not_universal : SieberNotUniversal := by
  intro hL
  by_contra hno
  push_neg at hno
  exact hL (obsEquiv_computable hno)

end OR.Sieber
