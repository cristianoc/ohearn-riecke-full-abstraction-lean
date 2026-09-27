import Mathlib.Computability.Primrec

/-!
# Primitive recursive list combinators

Small additions to Mathlib's `Primrec` library used to show that the
certificate checker is primitive recursive.
-/

set_option autoImplicit false

namespace OR.Sieber.Prim

open Primrec

theorem all_eq_foldr {β : Type} (l : List β) (p : β → Bool) :
    l.all p = l.foldr (fun b r => p b && r) true := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.all_cons, ih]

theorem any_eq_foldr {β : Type} (l : List β) (p : β → Bool) :
    l.any p = l.foldr (fun b r => p b || r) false := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.any_cons, ih]

theorem find?_eq_foldr {β : Type} (l : List β) (p : β → Bool) :
    l.find? p = l.foldr (fun b r => if p b then some b else r) none := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      rw [List.find?_cons, List.foldr_cons, ← ih]
      cases p b <;> rfl

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- `==` is primitive recursive on any primcodable type with lawful equality. -/
theorem beq' {δ : Type} [Primcodable δ] [BEq δ] [LawfulBEq δ] :
    Primrec₂ (fun a b : δ => a == b) := by
  classical
  have h : Primrec₂ fun a b : δ => decide (a = b) := Primrec.eq
  exact Primrec₂.of_eq h fun a b => by
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]

theorem list_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have := Primrec.list_foldr (f := f) (g := fun _ => true) (h := fun a bs => p a bs.1 && bs.2) hf
    (Primrec.const true)
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact this.of_eq fun a => (all_eq_foldr _ _).symm

theorem list_any {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) := by
  have := Primrec.list_foldr (f := f) (g := fun _ => false) (h := fun a bs => p a bs.1 || bs.2) hf
    (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact this.of_eq fun a => (any_eq_foldr _ _).symm

theorem list_contains {δ : Type} [Primcodable δ] [BEq δ] [LawfulBEq δ]
    {f : α → List δ} {g : α → δ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a).contains (g a) := by
  have := list_any (p := fun a b => g a == b) hf (beq'.comp (hg.comp Primrec.fst) Primrec.snd).to₂
  exact this.of_eq fun a => List.contains_eq_any_beq.symm

theorem list_find? {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  classical
  have := Primrec.list_foldr (f := f) (g := fun _ => (none : Option β))
    (h := fun a bs => if p a bs.1 = true then some bs.1 else bs.2) hf (Primrec.const none)
    (Primrec.ite (Primrec.eq.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const true))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact this.of_eq fun a => (find?_eq_foldr _ _).symm

/-- Lookup of the value stored under key `c`, defaulting to `[]`. -/
theorem lookupD {δ : Type} [Primcodable δ] {f : α → List (ℕ × List δ)} {g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (((f a).find? (fun e => e.1 == g a)).map Prod.snd).getD [] := by
  have hfind := list_find? (p := fun a (e : ℕ × List δ) => e.1 == g a) hf
    (beq'.comp (Primrec.fst.comp Primrec.snd) (hg.comp Primrec.fst)).to₂
  exact Primrec.option_getD.comp (Primrec.option_map hfind (Primrec.snd.comp Primrec.snd).to₂)
    (Primrec.const [])

end OR.Sieber.Prim
