import OR.Order

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section

namespace OR

universe u v

/-- A wrapper avoids accidentally inheriting the non-flat order on `Option α`. -/
inductive Flat (α : Type u) where
  | bot : Flat α
  | val : α → Flat α
  deriving DecidableEq, Repr

namespace Flat

variable {α : Type u} {β : Type v}

instance : PartialOrder (Flat α) where
  le x y := x = .bot ∨ x = y
  le_refl _ := Or.inr rfl
  le_trans _ _ _ h k := by
    rcases h with h | rfl
    · exact Or.inl h
    · exact k
  le_antisymm x y h k := by
    rcases h with rfl | h
    · rcases k with rfl | k
      · rfl
      · exact k.symm
    · exact h

instance : OrderBot (Flat α) where
  bot := .bot
  bot_le _ := Or.inl rfl

@[simp] theorem le_def (x y : Flat α) : x ≤ y ↔ x = .bot ∨ x = y := Iff.rfl
@[simp] theorem bottom_eq : (⊥ : Flat α) = .bot := rfl
@[simp] theorem val_ne_bot (a : α) : val a ≠ (⊥ : Flat α) := by intro h; cases h
@[simp] theorem val_le_iff (a : α) (x : Flat α) : val a ≤ x ↔ x = val a := by
  simp only [le_def, reduceCtorEq, false_or]
  exact eq_comm
@[simp] theorem val_le_val (a b : α) : val a ≤ val b ↔ a = b := by
  simp only [val_le_iff, val.injEq]
  exact eq_comm
@[simp] theorem le_bot_iff (x : Flat α) : x ≤ .bot ↔ x = .bot := by
  simp only [le_def, or_self]

 theorem eq_val_of_mem {s : Set (Flat α)} (hs : Dir s)
    {a : α} (ha : val a ∈ s) {x : Flat α} (hx : x ∈ s) : x ≤ val a := by
  obtain ⟨z, hz, hxz, haz⟩ := hs.2 x hx (val a) ha
  have he : z = val a := (val_le_iff a z).mp haz
  simpa only [he] using hxz

 theorem all_bot_of_no_val {s : Set (Flat α)}
    (h : ¬ ∃ a, val a ∈ s) {x : Flat α} (hx : x ∈ s) : x = .bot := by
  cases x with
  | bot => rfl
  | val a => exact False.elim (h ⟨a, hx⟩)

instance : DComplete (Flat α) where
  has_lub s hs := by
    classical
    by_cases h : ∃ a, val a ∈ s
    · rcases h with ⟨a, ha⟩
      refine ⟨val a, ?_, ?_⟩
      · intro x hx
        exact eq_val_of_mem hs ha hx
      · intro x hx
        exact hx ha
    · refine ⟨.bot, ?_, ?_⟩
      · intro x hx
        rw [all_bot_of_no_val h hx]
      · intro x _
        exact bot_le

 theorem dSup_of_val_mem {s : Set (Flat α)} (hs : Dir s)
    {a : α} (ha : val a ∈ s) : dSup s hs = val a := by
  apply le_antisymm
  · exact dSup_le hs (fun _ hx => eq_val_of_mem hs ha hx)
  · exact le_dSup hs ha

 theorem dSup_mem {s : Set (Flat α)} (hs : Dir s) : dSup s hs ∈ s := by
  classical
  by_cases h : ∃ a, val a ∈ s
  · rcases h with ⟨a, ha⟩
    simpa only [dSup_of_val_mem hs ha] using ha
  · obtain ⟨x, hx⟩ := hs.1
    have he : x = .bot := all_bot_of_no_val h hx
    have he' : dSup s hs = .bot := by
      apply le_antisymm
      · exact dSup_le hs (fun y hy => (all_bot_of_no_val h hy).le)
      · exact bot_le
    simpa only [he, he'] using hx

 theorem val_mem_of_dSup_eq {s : Set (Flat α)} (hs : Dir s)
    {a : α} (h : dSup s hs = val a) : val a ∈ s := by
  simpa only [h] using dSup_mem hs

 theorem val_mem_of_le_dSup {s : Set (Flat α)} (hs : Dir s)
    {a : α} (h : val a ≤ dSup s hs) : val a ∈ s :=
  val_mem_of_dSup_eq hs ((val_le_iff _ _).mp h)

 theorem chain_compact (c : Chain (Flat α)) {a : α}
    (h : c.sup = val a) : ∃ n, c n = val a := by
  have hm := val_mem_of_dSup_eq c.dir h
  exact hm

 theorem strict_monotone (f : Flat α → Flat β) (hf : f .bot = .bot) :
    Monotone f := by
  intro x y h
  rcases h with rfl | rfl
  · rw [hf]
    exact bot_le
  · exact le_rfl

 theorem observed_order (x y : Flat α) :
    x ≤ y ↔ ∀ a, x = val a → y = val a := by
  constructor
  · intro h a ha
    subst x
    exact (val_le_iff _ _).mp h
  · intro h
    cases x with
    | bot => exact bot_le
    | val a => exact (h a rfl).symm.le

end Flat

/-- Every directed supremum is attained; this is not finiteness of the carrier. -/
class Stabilizing (α : Type u) [PartialOrder α] [DComplete α] : Prop where
  sup_mem : ∀ s : Set α, ∀ hs : Dir s, dSup s hs ∈ s

instance {α : Type u} : Stabilizing (Flat α) := ⟨fun _ hs => Flat.dSup_mem hs⟩

instance stabilizingPUnit : Stabilizing PUnit where
  sup_mem s hs := by
    rcases hs.1 with ⟨a, ha⟩
    simpa only [Subsingleton.elim (dSup s hs) a] using ha

instance stabilizingProd {α : Type u} {β : Type v}
    [PartialOrder α] [DComplete α] [Stabilizing α]
    [PartialOrder β] [DComplete β] [Stabilizing β] : Stabilizing (α × β) where
  sup_mem s hs := by
    have ha := Stabilizing.sup_mem (Prod.fst '' s)
      (hs.image _ (fun _ _ h => h.1))
    have hb := Stabilizing.sup_mem (Prod.snd '' s)
      (hs.image _ (fun _ _ h => h.2))
    rcases ha with ⟨a, ha, hea⟩
    rcases hb with ⟨b, hb, heb⟩
    obtain ⟨c, hc, hac, hbc⟩ := hs.2 a ha b hb
    have he : dSup s hs = c := by
      apply le_antisymm
      · constructor
        · rw [dSup_prod_fst, ← hea]
          exact hac.1
        · rw [dSup_prod_snd, ← heb]
          exact hbc.2
      · exact le_dSup hs hc
    simpa only [he] using hc

/-- Directed stabilization at a finite arity, even when each ground carrier is infinite. -/
instance stabilizingPi {ι : Type u} {A : ι → Type v} [Finite ι]
    [∀ i, PartialOrder (A i)] [∀ i, DComplete (A i)] [∀ i, Stabilizing (A i)] :
    Stabilizing (∀ i, A i) where
  sup_mem s hs := by
    classical
    letI : Fintype ι := Fintype.ofFinite ι
    have hx : ∀ i, ∃ f ∈ s, f i = dSup s hs i := by
      intro i
      have h := Stabilizing.sup_mem ((fun f : ∀ j, A j => f i) '' s)
        (hs.image (fun f : ∀ j, A j => f i) (fun _ _ h => h i))
      rcases h with ⟨f, hf, he⟩
      exact ⟨f, hf, he.trans (OR.dSup_apply s hs i).symm⟩
    choose f hf he using hx
    obtain ⟨b, hb, hfb⟩ := hs.finite_bound Finset.univ f (by
      intro i _
      exact hf i)
    have hb' : dSup s hs = b := by
      apply le_antisymm
      · intro i
        rw [← he i]
        exact hfb i (Finset.mem_univ i) i
      · exact le_dSup hs hb
    simpa only [hb'] using hb

namespace CMap

variable {α : Type u} {β : Type v}
variable [PartialOrder α] [DComplete α] [Stabilizing α]
variable [PartialOrder β] [DComplete β]

 def ofStabilizing (f : α → β) (hf : Monotone f) : CMap α β where
  toFun := f
  mono := hf
  map_le s hs _ h := h _ (Stabilizing.sup_mem s hs)

@[simp] theorem ofStabilizing_apply (f : α → β) (hf : Monotone f) (a : α) :
    ofStabilizing f hf a = f a := rfl

end CMap

abbrev Ground := Flat ℕ

namespace Ground

 def succ : Ground → Ground
  | .bot => .bot
  | .val n => .val (n + 1)

/-- O'Hearn--Riecke's predecessor: predecessor of zero diverges. -/
 def pred : Ground → Ground
  | .bot => .bot
  | .val 0 => .bot
  | .val (n + 1) => .val n

 def ifz : Ground → Ground → Ground → Ground
  | .bot, _, _ => .bot
  | .val 0, a, _ => a
  | .val (_ + 1), _, b => b

@[simp] theorem succ_bot : succ .bot = .bot := rfl
@[simp] theorem succ_val (n : ℕ) : succ (.val n) = .val (n + 1) := rfl
@[simp] theorem pred_bot : pred .bot = .bot := rfl
@[simp] theorem pred_zero : pred (.val 0) = .bot := rfl
@[simp] theorem pred_succ (n : ℕ) : pred (.val (n + 1)) = .val n := rfl
@[simp] theorem ifz_bot (a b : Ground) : ifz .bot a b = .bot := rfl
@[simp] theorem ifz_zero (a b : Ground) : ifz (.val 0) a b = a := rfl
@[simp] theorem ifz_succ (n : ℕ) (a b : Ground) : ifz (.val (n + 1)) a b = b := rfl

 theorem succ_mono : Monotone succ := Flat.strict_monotone succ rfl
 theorem pred_mono : Monotone pred := Flat.strict_monotone pred rfl

 theorem ifz_mono : Monotone (fun p : Ground × (Ground × Ground) => ifz p.1 p.2.1 p.2.2) := by
  rintro ⟨c, a, b⟩ ⟨d, u, v⟩ ⟨hcd, hau, hbv⟩
  change c ≤ d at hcd
  change a ≤ u at hau
  change b ≤ v at hbv
  change ifz c a b ≤ ifz d u v
  rcases hcd with rfl | hcd
  · exact bot_le
  · subst d
    cases c with
    | bot => exact bot_le
    | val n =>
      cases n with
      | zero => exact hau
      | succ n => exact hbv

 def succMap : CMap Ground Ground := CMap.ofStabilizing succ succ_mono
 def predMap : CMap Ground Ground := CMap.ofStabilizing pred pred_mono
 def ifzMap : CMap (Ground × (Ground × Ground)) Ground :=
  CMap.ofStabilizing (fun p => ifz p.1 p.2.1 p.2.2) ifz_mono

/-- Finite case analysis. Out-of-range natural numbers and bottom return bottom. -/
 def casesUpTo : ℕ → Ground → (ℕ → Ground) → Ground
  | 0, c, h => ifz c (h 0) .bot
  | k + 1, c, h => ifz c (h 0) (casesUpTo k (pred c) (fun j => h (j + 1)))

@[simp] theorem casesUpTo_bot (k : ℕ) (h : ℕ → Ground) :
    casesUpTo k .bot h = .bot := by cases k <;> rfl

 theorem casesUpTo_val (k j : ℕ) (h : ℕ → Ground) :
    casesUpTo k (.val j) h = if j ≤ k then h j else .bot := by
  induction k generalizing j h with
  | zero =>
      cases j with
      | zero => simp [casesUpTo]
      | succ j => simp [casesUpTo]
  | succ k ih =>
      cases j with
      | zero => simp [casesUpTo]
      | succ j => simpa [casesUpTo, Nat.succ_le_succ_iff] using ih j (fun j => h (j + 1))

end Ground

end OR
