import OR.Flat

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR

universe u

/-- Closure under precisely the four PCF ground operations. -/
structure PrimitiveClosed {ι : Type u} (R : (ι → Ground) → Prop) : Prop where
  zero : R (fun _ => .val 0)
  succ : ∀ g, R g → R (fun i => Ground.succ (g i))
  pred : ∀ g, R g → R (fun i => Ground.pred (g i))
  ifz : ∀ c a b, R c → R a → R b → R (fun i => Ground.ifz (c i) (a i) (b i))

namespace PrimitiveClosed

variable {ι : Type u} {R : (ι → Ground) → Prop}

 theorem bottom (h : PrimitiveClosed R) : R (fun _ => .bot) := by
  simpa only [Ground.pred_zero] using h.pred _ h.zero

 theorem numeral (h : PrimitiveClosed R) (n : ℕ) : R (fun _ => .val n) := by
  induction n with
  | zero => exact h.zero
  | succ n ih => exact h.succ _ ih

 theorem constant (h : PrimitiveClosed R) (d : Ground) : R (fun _ => d) := by
  cases d with
  | bot => exact h.bottom
  | val n => exact h.numeral n

 theorem casesUpTo (hR : PrimitiveClosed R) (k : ℕ) (c : ι → Ground)
    (h : ℕ → ι → Ground) (hc : R c) (hh : ∀ j, R (h j)) :
    R (fun i => Ground.casesUpTo k (c i) (fun j => h j i)) := by
  induction k generalizing c h with
  | zero => exact hR.ifz c (h 0) (fun _ => .bot) hc (hh 0) hR.bottom
  | succ k ih =>
      exact hR.ifz c (h 0)
        (fun i => Ground.casesUpTo k (Ground.pred (c i)) (fun j => h (j + 1) i))
        hc (hh 0) (ih _ _ (hR.pred _ hc) (fun j => hh (j + 1)))

end PrimitiveClosed

/-- Sieber's elementary sequentiality relation, with the subset side condition separate. -/
def Elementary {ι : Type u} (A B : Finset ι) (g : ι → Ground) : Prop :=
  (∃ i ∈ A, g i = .bot) ∨ ∀ i ∈ B, ∀ j ∈ B, g i = g j

namespace Elementary

variable {ι : Type u} {A B : Finset ι}

 theorem constant (A B : Finset ι) (d : Ground) : Elementary A B (fun _ => d) :=
  Or.inr (fun _ _ _ _ => rfl)

 theorem congr (hAB : A ⊆ B) {g h : ι → Ground}
    (he : ∀ i ∈ B, g i = h i) : Elementary A B g ↔ Elementary A B h := by
  constructor
  · rintro (⟨i, hi, hgi⟩ | hg)
    · exact Or.inl ⟨i, hi, (he i (hAB hi)).symm.trans hgi⟩
    · exact Or.inr (fun i hi j hj => (he i hi).symm.trans ((hg i hi j hj).trans (he j hj)))
  · rintro (⟨i, hi, hhi⟩ | hh)
    · exact Or.inl ⟨i, hi, (he i (hAB hi)).trans hhi⟩
    · exact Or.inr (fun i hi j hj => (he i hi).trans ((hh i hi j hj).trans (he j hj).symm))

 theorem strict_map {g : ι → Ground} (hg : Elementary A B g)
    (f : Ground → Ground) (hf : f .bot = .bot) :
    Elementary A B (fun i => f (g i)) := by
  rcases hg with ⟨i, hi, hgi⟩ | hg
  · exact Or.inl ⟨i, hi, (congrArg f hgi).trans hf⟩
  · exact Or.inr (fun i hi j hj => congrArg f (hg i hi j hj))

 theorem conditional (hAB : A ⊆ B) {c a b : ι → Ground}
    (hc : Elementary A B c) (ha : Elementary A B a) (hb : Elementary A B b) :
    Elementary A B (fun i => Ground.ifz (c i) (a i) (b i)) := by
  classical
  rcases hc with ⟨i, hi, hci⟩ | hc
  · refine Or.inl ⟨i, hi, ?_⟩
    change Ground.ifz (c i) (a i) (b i) = .bot
    rw [hci, Ground.ifz_bot]
  · by_cases hB : B.Nonempty
    · rcases hB with ⟨i, hi⟩
      have hci : ∀ j ∈ B, c j = c i := fun j hj => hc j hj i hi
      cases he : c i with
      | bot =>
          apply (congr hAB (g := fun _ => .bot) (h := fun j => Ground.ifz (c j) (a j) (b j)) ?_).mp
            (constant A B .bot)
          intro j hj
          change (.bot : Ground) = Ground.ifz (c j) (a j) (b j)
          rw [hci j hj, he]
          rfl
      | val n =>
          cases n with
          | zero =>
              apply (congr hAB (g := a) (h := fun j => Ground.ifz (c j) (a j) (b j)) ?_).mp ha
              intro j hj
              change a j = Ground.ifz (c j) (a j) (b j)
              rw [hci j hj, he]
              rfl
          | succ n =>
              apply (congr hAB (g := b) (h := fun j => Ground.ifz (c j) (a j) (b j)) ?_).mp hb
              intro j hj
              change b j = Ground.ifz (c j) (a j) (b j)
              rw [hci j hj, he]
              rfl
    · right
      intro i hi
      exact False.elim (hB ⟨i, hi⟩)

 theorem primitiveClosed (hAB : A ⊆ B) : PrimitiveClosed (Elementary A B) where
  zero := constant A B (.val 0)
  succ _ hg := strict_map hg Ground.succ rfl
  pred _ hg := strict_map hg Ground.pred rfl
  ifz _ _ _ hc ha hb := conditional hAB hc ha hb

end Elementary

/-- The intersection of all elementary relations containing `R`. -/
def sequentialHull {ι : Type u} (R : (ι → Ground) → Prop) (g : ι → Ground) : Prop :=
  ∀ A B : Finset ι, A ⊆ B →
    (∀ h, R h → Elementary A B h) → Elementary A B g

/-- Equality with the canonical elementary intersection. -/
def Sequential {ι : Type u} (R : (ι → Ground) → Prop) : Prop := R = sequentialHull R

 theorem into_sequentialHull {ι : Type u} {R : (ι → Ground) → Prop}
    {g : ι → Ground} (hg : R g) : sequentialHull R g :=
  fun _ _ _ h => h g hg

 theorem hull_primitiveClosed {ι : Type u} (R : (ι → Ground) → Prop) :
    PrimitiveClosed (sequentialHull R) where
  zero _ _ hAB _ := (Elementary.primitiveClosed hAB).zero
  succ g hg A B hAB hR := (Elementary.primitiveClosed hAB).succ g (hg A B hAB hR)
  pred g hg A B hAB hR := (Elementary.primitiveClosed hAB).pred g (hg A B hAB hR)
  ifz c a b hc ha hb A B hAB hR :=
    (Elementary.primitiveClosed hAB).ifz c a b
      (hc A B hAB hR) (ha A B hAB hR) (hb A B hAB hR)

/-- The substantive finite interpolation proof; recursion is on strict subsets. -/
 theorem finite_interpolation {ι : Type u} [DecidableEq ι]
    {R : (ι → Ground) → Prop} (hR : PrimitiveClosed R)
    {r : ι → Ground} (hr : sequentialHull R r) (B : Finset ι) :
    ∃ h, R h ∧ ∀ i ∈ B, h i = r i := by
  classical
  refine Finset.strongInductionOn B ?_
  intro B ih
  by_cases hc : ∃ d : Ground, ∀ i ∈ B, r i = d
  · rcases hc with ⟨d, hd⟩
    exact ⟨fun _ => d, hR.constant d, fun i hi => (hd i hi).symm⟩
  · let A := B.filter (fun i => r i ≠ .bot)
    have hAB : A ⊆ B := Finset.filter_subset _ _
    have hrv : ¬ Elementary A B r := by
      rintro (⟨i, hi, hri⟩ | hconst)
      · exact (Finset.mem_filter.mp hi).2 hri
      · apply hc
        by_cases hB : B.Nonempty
        · rcases hB with ⟨i, hi⟩
          exact ⟨r i, fun j hj => hconst j hj i hi⟩
        · exact ⟨.bot, fun i hi => False.elim (hB ⟨i, hi⟩)⟩
    have hgex : ∃ g, R g ∧ ¬ Elementary A B g := by
      by_contra hg
      have hv : ∀ g, R g → Elementary A B g := by
        intro g hgr
        by_contra hv
        exact hg ⟨g, hgr, hv⟩
      exact hrv (hr A B hAB hv)
    rcases hgex with ⟨g, hg, hgv⟩
    have hgA : ∀ i ∈ A, g i ≠ .bot := by
      intro i hi he
      exact hgv (Or.inl ⟨i, hi, he⟩)
    have hgB : ¬ ∀ i ∈ B, ∀ j ∈ B, g i = g j :=
      fun h => hgv (Or.inr h)
    let fiber : ℕ → Finset ι := fun j => B.filter (fun i => g i = .val j)
    have hsmall : ∀ j, fiber j ⊂ B := by
      intro j
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      apply hgB
      intro i hi k hk
      have hi' : i ∈ fiber j := he.symm ▸ hi
      have hk' : k ∈ fiber j := he.symm ▸ hk
      exact (Finset.mem_filter.mp hi').2.trans (Finset.mem_filter.mp hk').2.symm
    have hh : ∀ j, ∃ h, R h ∧ ∀ i ∈ fiber j, h i = r i :=
      fun j => ih (fiber j) (hsmall j)
    choose h hhR hhr using hh
    let value : ι → ℕ := fun i => match g i with | .bot => 0 | .val j => j
    let K := B.sup value
    have hK : ∀ i ∈ B, ∀ j, g i = .val j → j ≤ K := by
      intro i hi j hij
      have hle : value i ≤ B.sup value := Finset.le_sup hi
      simpa only [value, hij] using hle
    refine ⟨fun i => Ground.casesUpTo K (g i) (fun j => h j i),
      hR.casesUpTo K g h hg hhR, ?_⟩
    intro i hi
    change Ground.casesUpTo K (g i) (fun j => h j i) = r i
    cases hgi : g i with
    | bot =>
        have hri : r i = .bot := by
          by_contra hri
          exact hgA i (Finset.mem_filter.mpr ⟨hi, hri⟩) hgi
        simp only [Ground.casesUpTo_bot, hri]
    | val j =>
        rw [Ground.casesUpTo_val, if_pos (hK i hi j hgi)]
        exact hhr j i (Finset.mem_filter.mpr ⟨hi, hgi⟩)

 theorem sequential_iff_primitive_closed {ι : Type u} [Finite ι]
    (R : (ι → Ground) → Prop) : Sequential R ↔ PrimitiveClosed R := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro h
    change R = sequentialHull R at h
    rw [h]
    exact hull_primitiveClosed R
  · intro hR
    change R = sequentialHull R
    funext r
    apply propext
    constructor
    · exact into_sequentialHull
    · intro hr
      obtain ⟨g, hg, hgr⟩ := finite_interpolation hR hr Finset.univ
      have he : g = r := funext (fun i => hgr i (Finset.mem_univ i))
      simpa only [he] using hg

end OR
