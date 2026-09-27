import Mathlib

/-!
# Nonempty-directed domain theory

This file deliberately uses a small local interface for nonempty-directed
completeness. All its instances and all continuous-map constructions are proved
here. In particular, it does not postulate a cartesian closed category of domains.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section

namespace OR

universe u v w z

/-- A nonempty directed subset. Empty suprema are handled by `OrderBot`, not here. -/
def Dir {α : Type u} [LE α] (s : Set α) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, ∃ c ∈ s, a ≤ c ∧ b ≤ c

namespace Dir

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

 theorem image {s : Set α} (hs : Dir s) (f : α → β) (hf : Monotone f) :
    Dir (f '' s) := by
  constructor
  · rcases hs.1 with ⟨a, ha⟩
    exact ⟨f a, ⟨a, ha, rfl⟩⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rcases hs.2 a ha b hb with ⟨c, hc, hac, hbc⟩
    exact ⟨f c, ⟨c, hc, rfl⟩, hf hac, hf hbc⟩

 theorem singleton (a : α) : Dir ({a} : Set α) := by
  refine ⟨⟨a, by simp⟩, ?_⟩
  intro x hx y hy
  have hx' : x = a := by simpa using hx
  have hy' : y = a := by simpa using hy
  subst x
  subst y
  exact ⟨a, by simp, le_rfl, le_rfl⟩

 theorem range {c : ℕ → α} (hc : Monotone c) : Dir (Set.range c) := by
  refine ⟨⟨c 0, ⟨0, rfl⟩⟩, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact ⟨c (max i j), ⟨max i j, rfl⟩,
    hc (le_max_left _ _), hc (le_max_right _ _)⟩

/-- Finite simultaneous choice of an upper bound inside a directed set. -/
 theorem finite_bound {ι : Type v} [DecidableEq ι] {s : Set α}
    (hs : Dir s) (t : Finset ι) (f : ι → α)
    (hf : ∀ i ∈ t, f i ∈ s) :
    ∃ b ∈ s, ∀ i ∈ t, f i ≤ b := by
  revert hf
  induction t using Finset.induction_on with
  | empty =>
      intro hf
      rcases hs.1 with ⟨b, hb⟩
      exact ⟨b, hb, by simp⟩
  | @insert i t hit ih =>
      intro hf
      obtain ⟨b, hb, hfb⟩ := ih (by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj))
      obtain ⟨c, hc, hic, hbc⟩ := hs.2 (f i) (hf i (by simp)) b hb
      refine ⟨c, hc, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hic
      · exact (hfb j hj).trans hbc

end Dir

/-- Directed completeness, without silently requiring suprema of arbitrary sets. -/
class DComplete (α : Type u) [PartialOrder α] : Prop where
  has_lub : ∀ s : Set α, Dir s → ∃ a, IsLUB s a

variable {α : Type u} {β : Type v} {γ : Type w}

section Supremum

variable [PartialOrder α] [DComplete α]

def dSup (s : Set α) (hs : Dir s) : α :=
  Classical.choose (DComplete.has_lub s hs)

 theorem dSup_isLUB (s : Set α) (hs : Dir s) : IsLUB s (dSup s hs) :=
  Classical.choose_spec (DComplete.has_lub s hs)

 theorem le_dSup {s : Set α} (hs : Dir s) {a : α} (ha : a ∈ s) :
    a ≤ dSup s hs := (dSup_isLUB s hs).1 ha

 theorem dSup_le {s : Set α} (hs : Dir s) {a : α}
    (ha : ∀ b ∈ s, b ≤ a) : dSup s hs ≤ a :=
  (dSup_isLUB s hs).2 ha

 theorem dSup_eq {s : Set α} (hs : Dir s) {a : α} (ha : IsLUB s a) :
    dSup s hs = a := (dSup_isLUB s hs).unique ha

 theorem dSup_congr {s t : Set α} (hs : Dir s) (ht : Dir t) (h : s = t) :
    dSup s hs = dSup t ht := by subst t; rfl

 @[simp] theorem dSup_singleton (a : α) : dSup {a} (Dir.singleton a) = a := by
  apply le_antisymm
  · apply dSup_le (Dir.singleton a)
    intro b hb
    have : b = a := by simpa using hb
    exact this.le
  · exact le_dSup (Dir.singleton a) (by simp)

 theorem dSup_mono {s t : Set α} (hs : Dir s) (ht : Dir t) (h : s ⊆ t) :
    dSup s hs ≤ dSup t ht :=
  dSup_le hs (fun _ hx => le_dSup ht (h hx))

 theorem dSup_image_le [PartialOrder β] [DComplete β]
    {s : Set α} (hs : Dir s) (f : α → β) (hf : Monotone f) {b : β}
    (h : ∀ a ∈ s, f a ≤ b) : dSup (f '' s) (hs.image f hf) ≤ b := by
  apply dSup_le (hs.image f hf)
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

 theorem dSup_image_comp [PartialOrder β] [DComplete β]
    [PartialOrder γ] [DComplete γ]
    {s : Set α} (hs : Dir s) (f : α → β) (hf : Monotone f)
    (g : β → γ) (hg : Monotone g) :
    dSup (g '' (f '' s)) ((hs.image f hf).image g hg) =
      dSup ((g ∘ f) '' s) (hs.image (g ∘ f) (hg.comp hf)) := by
  apply dSup_congr
  exact Set.image_image g f s

end Supremum

instance (priority := 100) completeLatticeDComplete
    [CompleteLattice α] : DComplete α where
  has_lub s _ := ⟨sSup s, isLUB_sSup s⟩

section Products

variable [PartialOrder α] [DComplete α]
variable [PartialOrder β] [DComplete β]

instance prodDComplete : DComplete (α × β) where
  has_lub s hs := by
    let ha := hs.image Prod.fst (fun _ _ h => h.1)
    let hb := hs.image Prod.snd (fun _ _ h => h.2)
    refine ⟨(dSup (Prod.fst '' s) ha, dSup (Prod.snd '' s) hb), ?_, ?_⟩
    · intro p hp
      exact ⟨le_dSup ha ⟨p, hp, rfl⟩, le_dSup hb ⟨p, hp, rfl⟩⟩
    · intro p hp
      constructor
      · apply dSup_le ha
        rintro _ ⟨q, hq, rfl⟩
        exact (hp hq).1
      · apply dSup_le hb
        rintro _ ⟨q, hq, rfl⟩
        exact (hp hq).2

 theorem dSup_prod_fst (s : Set (α × β)) (hs : Dir s) :
    (dSup s hs).1 = dSup (Prod.fst '' s) (hs.image _ (fun _ _ h => h.1)) := by
  apply le_antisymm
  · have h : dSup s hs ≤
        (dSup (Prod.fst '' s) (hs.image _ (fun _ _ h => h.1)), (dSup s hs).2) := by
      apply dSup_le hs
      intro p hp
      exact ⟨le_dSup (hs.image _ (fun _ _ h => h.1)) ⟨p, hp, rfl⟩,
        (le_dSup hs hp).2⟩
    exact h.1
  · apply dSup_le (hs.image Prod.fst (fun _ _ h => h.1))
    rintro _ ⟨p, hp, rfl⟩
    exact (le_dSup hs hp).1

 theorem dSup_prod_snd (s : Set (α × β)) (hs : Dir s) :
    (dSup s hs).2 = dSup (Prod.snd '' s) (hs.image _ (fun _ _ h => h.2)) := by
  apply le_antisymm
  · have h : dSup s hs ≤
        ((dSup s hs).1, dSup (Prod.snd '' s) (hs.image _ (fun _ _ h => h.2))) := by
      apply dSup_le hs
      intro p hp
      exact ⟨(le_dSup hs hp).1,
        le_dSup (hs.image _ (fun _ _ h => h.2)) ⟨p, hp, rfl⟩⟩
    exact h.2
  · apply dSup_le (hs.image Prod.snd (fun _ _ h => h.2))
    rintro _ ⟨p, hp, rfl⟩
    exact (le_dSup hs hp).2

end Products

section Pi

variable {ι : Type u} {A : ι → Type v}
variable [∀ i, PartialOrder (A i)] [∀ i, DComplete (A i)]

instance piDComplete : DComplete (∀ i, A i) where
  has_lub s hs := by
    let h : ∀ i, Dir ((fun f : ∀ j, A j => f i) '' s) :=
      fun i => hs.image (fun f : ∀ j, A j => f i) (fun _ _ h => h i)
    refine ⟨fun i => dSup _ (h i), ?_, ?_⟩
    · intro f hf i
      exact le_dSup (h i) ⟨f, hf, rfl⟩
    · intro f hf i
      apply dSup_le (h i)
      rintro _ ⟨g, hg, rfl⟩
      exact hf hg i

 theorem dSup_apply (s : Set (∀ i, A i)) (hs : Dir s) (i : ι) :
    dSup s hs i =
      dSup ((fun f : ∀ j, A j => f i) '' s)
        (hs.image (fun f : ∀ j, A j => f i) (fun _ _ h => h i)) := by
  let hi : ∀ i, Dir ((fun f : ∀ j, A j => f i) '' s) :=
    fun i => hs.image (fun f : ∀ j, A j => f i) (fun _ _ h => h i)
  have h := dSup_eq hs (show IsLUB s
      (fun i => dSup ((fun f : ∀ j, A j => f i) '' s) (hi i)) from by
    constructor
    · intro f hf i
      exact le_dSup (hi i) ⟨f, hf, rfl⟩
    · intro f hf i
      apply dSup_le (hi i)
      rintro _ ⟨g, hg, rfl⟩
      exact hf hg i)
  exact congrFun h i

end Pi

/-- The upper-bound formulation makes proofs of continuity entirely order-theoretic. -/
structure CMap (α : Type u) (β : Type v)
    [PartialOrder α] [DComplete α] [PartialOrder β] [DComplete β] where
  toFun : α → β
  mono : Monotone toFun
  map_le : ∀ (s : Set α) (hs : Dir s) (b : β),
    (∀ a ∈ s, toFun a ≤ b) → toFun (dSup s hs) ≤ b

namespace CMap

variable [PartialOrder α] [DComplete α]
variable [PartialOrder β] [DComplete β]
variable [PartialOrder γ] [DComplete γ]

instance : CoeFun (CMap α β) (fun _ => α → β) := ⟨CMap.toFun⟩

 @[ext] theorem ext {f g : CMap α β} (h : ∀ a, f a = g a) : f = g := by
  cases f with
  | mk f fm fc =>
    cases g with
    | mk g gm gc =>
      have : f = g := funext h
      subst g
      rfl

instance : PartialOrder (CMap α β) where
  le f g := ∀ a, f a ≤ g a
  le_refl _ _ := le_rfl
  le_trans _ _ _ h k a := (h a).trans (k a)
  le_antisymm _ _ h k := ext (fun a => le_antisymm (h a) (k a))

 @[simp] theorem le_def (f g : CMap α β) : f ≤ g ↔ ∀ a, f a ≤ g a := Iff.rfl

 theorem map_dSup (f : CMap α β) (s : Set α) (hs : Dir s) :
    f (dSup s hs) = dSup (f '' s) (hs.image f f.mono) := by
  apply le_antisymm
  · exact f.map_le s hs _ (fun a ha => le_dSup (hs.image f f.mono) ⟨a, ha, rfl⟩)
  · apply dSup_le (hs.image f f.mono)
    rintro _ ⟨a, ha, rfl⟩
    exact f.mono (le_dSup hs ha)

 def id : CMap α α where
  toFun := fun x => x
  mono := fun _ _ h => h
  map_le s hs _ h := dSup_le hs h

 def const (b : β) : CMap α β where
  toFun := fun _ => b
  mono := fun _ _ _ => le_rfl
  map_le s hs _ h := by rcases hs.1 with ⟨a, ha⟩; exact h a ha

 def comp (g : CMap β γ) (f : CMap α β) : CMap α γ where
  toFun := fun a => g (f a)
  mono := g.mono.comp f.mono
  map_le s hs b h := by
    rw [f.map_dSup]
    apply g.map_le
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha

 def fst : CMap (α × β) α where
  toFun := Prod.fst
  mono := fun _ _ h => h.1
  map_le s hs a h := by
    rw [dSup_prod_fst]
    apply dSup_le (hs.image Prod.fst (fun _ _ h => h.1))
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp

 def snd : CMap (α × β) β where
  toFun := Prod.snd
  mono := fun _ _ h => h.2
  map_le s hs b h := by
    rw [dSup_prod_snd]
    apply dSup_le (hs.image Prod.snd (fun _ _ h => h.2))
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp

 def pair (f : CMap α β) (g : CMap α γ) : CMap α (β × γ) where
  toFun := fun a => (f a, g a)
  mono := fun _ _ h => ⟨f.mono h, g.mono h⟩
  map_le s hs b h :=
    ⟨f.map_le s hs b.1 (fun a ha => (h a ha).1),
      g.map_le s hs b.2 (fun a ha => (h a ha).2)⟩

 @[simp] theorem id_apply (a : α) : (id : CMap α α) a = a := rfl
 @[simp] theorem const_apply (b : β) (a : α) : (const b : CMap α β) a = b := rfl
 @[simp] theorem comp_apply (g : CMap β γ) (f : CMap α β) (a : α) :
    comp g f a = g (f a) := rfl
 @[simp] theorem fst_apply (p : α × β) : (fst : CMap (α × β) α) p = p.1 := rfl
 @[simp] theorem snd_apply (p : α × β) : (snd : CMap (α × β) β) p = p.2 := rfl
 @[simp] theorem pair_apply (f : CMap α β) (g : CMap α γ) (a : α) :
    pair f g a = (f a, g a) := rfl

 def pointSup (s : Set (CMap α β)) (hs : Dir s) : CMap α β where
  toFun a := dSup ((fun f : CMap α β => f a) '' s)
    (hs.image (fun f : CMap α β => f a) (fun _ _ h => h a))
  mono := by
    intro a b hab
    apply dSup_le (hs.image (fun f : CMap α β => f a) (fun _ _ h => h a))
    rintro _ ⟨f, hf, rfl⟩
    exact (f.mono hab).trans
      (le_dSup (hs.image (fun f : CMap α β => f b) (fun _ _ h => h b)) ⟨f, hf, rfl⟩)
  map_le t ht b h := by
    apply dSup_le
      (hs.image (fun f : CMap α β => f (dSup t ht)) (fun _ _ h => h _))
    rintro _ ⟨f, hf, rfl⟩
    apply f.map_le t ht b
    intro a ha
    exact (le_dSup (hs.image (fun f : CMap α β => f a) (fun _ _ h => h a))
      ⟨f, hf, rfl⟩).trans (h a ha)

instance : DComplete (CMap α β) where
  has_lub s hs := by
    refine ⟨pointSup s hs, ?_, ?_⟩
    · intro f hf a
      exact le_dSup (hs.image (fun f : CMap α β => f a) (fun _ _ h => h a))
        ⟨f, hf, rfl⟩
    · intro f hf a
      apply dSup_le (hs.image (fun f : CMap α β => f a) (fun _ _ h => h a))
      rintro _ ⟨g, hg, rfl⟩
      exact hf hg a

 theorem dSup_apply (s : Set (CMap α β)) (hs : Dir s) (a : α) :
    (dSup s hs) a = dSup ((fun f : CMap α β => f a) '' s)
      (hs.image (fun f : CMap α β => f a) (fun _ _ h => h a)) := by
  have heq : dSup s hs = pointSup s hs := by
    apply dSup_eq hs
    constructor
    · intro f hf x
      exact le_dSup (hs.image (fun f : CMap α β => f x) (fun _ _ h => h x))
        ⟨f, hf, rfl⟩
    · intro f hf x
      apply dSup_le (hs.image (fun f : CMap α β => f x) (fun _ _ h => h x))
      rintro _ ⟨g, hg, rfl⟩
      exact hf hg x
  exact congrArg (fun f : CMap α β => f a) heq

instance [OrderBot β] : OrderBot (CMap α β) where
  bot := const ⊥
  bot_le _ _ := bot_le

 @[simp] theorem bot_apply [OrderBot β] (a : α) : (⊥ : CMap α β) a = ⊥ := rfl

/-- Joint continuity; the directed diagonal, rather than separate continuity, is used. -/
 def eval : CMap (CMap α β × α) β where
  toFun p := p.1 p.2
  mono := by
    intro p q h
    exact (h.1 p.2).trans (q.1.mono h.2)
  map_le s hs b h := by
    rw [dSup_prod_fst, dSup_prod_snd, CMap.dSup_apply]
    apply dSup_le
    rintro _ ⟨f, ⟨p, hp, rfl⟩, rfl⟩
    apply p.1.map_le
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨r, hr, hpr, hqr⟩ := hs.2 p hp q hq
    exact ((hpr.1 q.2).trans (r.1.mono hqr.2)).trans (h r hr)

 def curry (f : CMap (γ × α) β) : CMap γ (CMap α β) where
  toFun c := f.comp ((const c).pair id)
  mono := by
    intro c d h a
    exact f.mono ⟨h, le_rfl⟩
  map_le s hs b h := by
    intro a
    let e : CMap γ (γ × α) := id.pair (const a)
    have he : (dSup s hs, a) = dSup (e '' s) (hs.image e e.mono) :=
      e.map_dSup s hs
    change f (dSup s hs, a) ≤ b a
    rw [he]
    apply f.map_le
    rintro _ ⟨c, hc, rfl⟩
    exact h c hc a

 def uncurry (f : CMap γ (CMap α β)) : CMap (γ × α) β :=
  eval.comp ((f.comp fst).pair snd)

 @[simp] theorem eval_apply (p : CMap α β × α) : eval p = p.1 p.2 := rfl
 @[simp] theorem curry_apply (f : CMap (γ × α) β) (c : γ) (a : α) :
    curry f c a = f (c, a) := rfl
 @[simp] theorem uncurry_apply (f : CMap γ (CMap α β)) (c : γ) (a : α) :
    uncurry f (c, a) = f c a := rfl
 @[simp] theorem uncurry_curry (f : CMap (γ × α) β) : uncurry (curry f) = f := by
  ext p
  rfl
 @[simp] theorem curry_uncurry (f : CMap γ (CMap α β)) : curry (uncurry f) = f := by
  ext c a
  rfl

/-- Coordinate projection on a possibly dependent product. -/
 def proj {ι : Type w} {A : ι → Type z}
    [∀ i, PartialOrder (A i)] [∀ i, DComplete (A i)] (i : ι) :
    CMap (∀ j, A j) (A i) where
  toFun f := f i
  mono := fun _ _ h => h i
  map_le s hs b h := by
    rw [OR.dSup_apply]
    apply dSup_le (hs.image (fun f : ∀ j, A j => f i) (fun _ _ h => h i))
    rintro _ ⟨f, hf, rfl⟩
    exact h f hf

 def pi {ι : Type w} {A : ι → Type z}
    [∀ i, PartialOrder (A i)] [∀ i, DComplete (A i)]
    (f : ∀ i, CMap α (A i)) : CMap α (∀ i, A i) where
  toFun a i := f i a
  mono := fun _ _ h i => (f i).mono h
  map_le s hs b h i := (f i).map_le s hs (b i) (fun a ha => h a ha i)

 def applyAt (a : α) : CMap (CMap α β) β :=
  eval.comp (id.pair (const a))

 @[simp] theorem proj_apply {ι : Type w} {A : ι → Type z}
    [∀ i, PartialOrder (A i)] [∀ i, DComplete (A i)]
    (i : ι) (f : ∀ i, A i) : proj i f = f i := rfl

 @[simp] theorem pi_apply {ι : Type w} {A : ι → Type z}
    [∀ i, PartialOrder (A i)] [∀ i, DComplete (A i)]
    (f : ∀ i, CMap α (A i)) (a : α) (i : ι) : pi f a i = f i a := rfl

 @[simp] theorem applyAt_apply (a : α) (f : CMap α β) : applyAt a f = f a := rfl

end CMap

/-- Closure under nonempty directed suprema; no downward closure is imposed. -/
class SupClosed {α : Type u} [PartialOrder α] [DComplete α]
    (P : α → Prop) : Prop where
  closed : ∀ s : Set α, ∀ hs : Dir s, (∀ a ∈ s, P a) → P (dSup s hs)

section Subtypes

variable [PartialOrder α] [DComplete α] {P : α → Prop} [SupClosed P]

instance subtypeDComplete : DComplete {a : α // P a} where
  has_lub s hs := by
    let ht := hs.image Subtype.val (fun _ _ h => h)
    have hP : P (dSup (Subtype.val '' s) ht) :=
      SupClosed.closed _ ht (by rintro _ ⟨a, ha, rfl⟩; exact a.property)
    refine ⟨⟨dSup (Subtype.val '' s) ht, hP⟩, ?_, ?_⟩
    · intro a ha
      exact le_dSup ht ⟨a, ha, rfl⟩
    · intro a ha
      apply dSup_le ht
      rintro _ ⟨b, hb, rfl⟩
      exact ha hb

 theorem dSup_subtype_val (s : Set {a : α // P a}) (hs : Dir s) :
    (dSup s hs).val =
      dSup (Subtype.val '' s) (hs.image _ (fun _ _ h => h)) := by
  let ht := hs.image Subtype.val (fun _ _ h => h)
  have hP : P (dSup (Subtype.val '' s) ht) :=
    SupClosed.closed _ ht (by rintro _ ⟨a, ha, rfl⟩; exact a.property)
  have he : dSup s hs = ⟨dSup (Subtype.val '' s) ht, hP⟩ := by
    apply dSup_eq hs
    constructor
    · intro a ha
      exact le_dSup ht ⟨a, ha, rfl⟩
    · intro a ha
      apply dSup_le ht
      rintro _ ⟨b, hb, rfl⟩
      exact ha hb
  exact congrArg Subtype.val he

 def CMap.subtypeVal : CMap {a : α // P a} α where
  toFun := Subtype.val
  mono := fun _ _ h => h
  map_le s hs b h := by
    rw [dSup_subtype_val]
    apply dSup_le (hs.image Subtype.val (fun _ _ h => h))
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha

 def CMap.codRestrict [PartialOrder β] [DComplete β]
    (f : CMap β α) (hf : ∀ b, P (f b)) : CMap β {a : α // P a} where
  toFun b := ⟨f b, hf b⟩
  mono := f.mono
  map_le s hs b h := f.map_le s hs b.val h

 @[simp] theorem CMap.subtypeVal_apply (a : {a : α // P a}) :
    (CMap.subtypeVal : CMap {a : α // P a} α) a = a.val := rfl

 @[simp] theorem CMap.codRestrict_apply [PartialOrder β] [DComplete β]
    (f : CMap β α) (hf : ∀ b, P (f b)) (b : β) :
    (CMap.codRestrict f hf b).val = f b := rfl

end Subtypes

/-- Increasing natural-number-indexed chains, used only for approximation and recursion. -/
structure Chain (α : Type u) [Preorder α] where
  «at» : ℕ → α
  mono : Monotone «at»

namespace Chain

variable [PartialOrder α] [DComplete α]
variable [PartialOrder β] [DComplete β]

instance : CoeFun (Chain α) (fun _ => ℕ → α) := ⟨Chain.at⟩

@[ext] theorem ext {c d : Chain α} (h : ∀ n, c n = d n) : c = d := by
  cases c with
  | mk c hc =>
    cases d with
    | mk d hd =>
      have he : c = d := funext h
      subst d
      rfl

def dir (c : Chain α) : Dir (Set.range c.at) := Dir.range c.mono

def sup (c : Chain α) : α := dSup (Set.range c.at) c.dir

theorem le_sup (c : Chain α) (n : ℕ) : c n ≤ c.sup :=
  le_dSup c.dir ⟨n, rfl⟩

theorem sup_le (c : Chain α) {a : α} (h : ∀ n, c n ≤ a) : c.sup ≤ a := by
  apply dSup_le c.dir
  rintro _ ⟨n, rfl⟩
  exact h n

def map (c : Chain α) (f : CMap α β) : Chain β :=
  ⟨fun n => f (c n), f.mono.comp c.mono⟩

@[simp] theorem map_at (c : Chain α) (f : CMap α β) (n : ℕ) :
    c.map f n = f (c n) := rfl

theorem map_sup (c : Chain α) (f : CMap α β) : f c.sup = (c.map f).sup := by
  rw [sup, f.map_dSup]
  apply dSup_congr
  ext b
  constructor
  · rintro ⟨a, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨c n, ⟨n, rfl⟩, rfl⟩

theorem sup_mono (c d : Chain α) (h : ∀ n, c n ≤ d n) : c.sup ≤ d.sup :=
  c.sup_le (fun n => (h n).trans (d.le_sup n))

theorem sup_const (a : α) : (Chain.mk (fun _ => a) (fun _ _ _ => le_rfl)).sup = a := by
  let c : Chain α := ⟨fun _ => a, fun _ _ _ => le_rfl⟩
  exact le_antisymm (c.sup_le (fun _ => le_rfl)) (c.le_sup 0)

theorem sup_fun_apply {ι : Type v} {A : ι → Type w}
    [∀ i, PartialOrder (A i)] [∀ i, DComplete (A i)]
    (c : Chain (∀ i, A i)) (i : ι) :
    c.sup i = (Chain.mk (fun n => c n i) (fun _ _ h => c.mono h i)).sup := by
  rw [sup, OR.dSup_apply]
  apply dSup_congr
  ext x
  constructor
  · rintro ⟨f, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨c n, ⟨n, rfl⟩, rfl⟩

/-- A failure of order is already visible at one common approximation index. -/
theorem failure_at_finite_stage (c : Chain α) (f g : CMap α β)
    (h : ¬ f c.sup ≤ g c.sup) : ∃ n, ¬ f (c n) ≤ g (c n) := by
  by_contra hn
  have hn' : ∀ n, f (c n) ≤ g (c n) := by simpa using hn
  apply h
  exact f.map_le _ c.dir _ (by
    rintro _ ⟨n, rfl⟩
    exact (hn' n).trans (g.mono (c.le_sup n)))

end Chain

section FixedPoints

variable [PartialOrder α] [DComplete α] [OrderBot α]

def iterate (f : CMap α α) : ℕ → α
  | 0 => ⊥
  | n + 1 => f (iterate f n)

@[simp] theorem iterate_zero (f : CMap α α) : iterate f 0 = ⊥ := rfl
@[simp] theorem iterate_succ (f : CMap α α) (n : ℕ) :
    iterate f (n + 1) = f (iterate f n) := rfl

theorem iterate_mono (f : CMap α α) : Monotone (iterate f) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact f.mono ih

def iterChain (f : CMap α α) : Chain α := ⟨iterate f, iterate_mono f⟩

def lfp (f : CMap α α) : α := (iterChain f).sup

theorem lfp_unfold (f : CMap α α) : f (lfp f) = lfp f := by
  apply le_antisymm
  · apply f.map_le _ (iterChain f).dir
    rintro _ ⟨n, rfl⟩
    exact (iterChain f).le_sup (n + 1)
  · apply (iterChain f).sup_le
    intro n
    cases n with
    | zero => exact bot_le
    | succ n => exact f.mono ((iterChain f).le_sup n)

theorem lfp_le (f : CMap α α) {a : α} (ha : f a ≤ a) : lfp f ≤ a := by
  apply (iterChain f).sup_le
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact (f.mono ih).trans ha

@[simp] theorem lfp_id : lfp (CMap.id : CMap α α) = ⊥ := by
  exact le_antisymm (lfp_le (CMap.id : CMap α α) (a := (⊥ : α)) le_rfl) bot_le

theorem lfp_mono {f g : CMap α α} (h : f ≤ g) : lfp f ≤ lfp g := by
  apply Chain.sup_mono
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (h _).trans (g.mono ih)

end FixedPoints

/-- A bundled small pointed dcpo. Relation universes will be larger than its carrier. -/
structure Domain where
  Carrier : Type
  po : PartialOrder Carrier
  ob : @OrderBot Carrier po.toLE
  dc : @DComplete Carrier po

attribute [instance] Domain.po Domain.ob Domain.dc
instance : CoeSort Domain Type := ⟨Domain.Carrier⟩

end OR
