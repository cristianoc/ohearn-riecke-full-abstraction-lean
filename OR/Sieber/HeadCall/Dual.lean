import OR.Sieber.HeadCall

/-!
# Compatibility obstructions are seen by Sieber's tests

Theorem 7 of `HEADCALL.md` (§6), in Sieber's model.

For `a : Fin k → τ₁` and a relation `P` on `Fin k` whose pairs have common upper bounds,
the test `R_K` of arity `k + 1` consists of the pair `({1..k}, {0..k})` and, for each
`P i j`, the pair `({i+1, j+1}, {i+1, j+1})`; position `i + 1` is `Fin.succ i`.

* `compat_iff_pointwise`, `joinBB`: two elements of `B ⇒ B` that agree wherever both are
  defined have a join in the model; every monotone map `B → B` preserves every test.
* `rk_compat`: an `R_K`-related tuple at `B ⇒ B` is compatible on `P`.
* `rk_related`: if no choice `φ` with `aᵢ(φᵢ) ≠ ⊥` is compatible on `P`, the tuple
  `(⊥, a₁, …, a_k)` is `R_K`-related at `τ₁`.
* `rk_not_holds`, `rk_not_preserved`, `rk_no_element`: a map `h` with `h ⊥ = ⊥` and every
  `h (aᵢ)` defined sends that tuple outside `R_K`, so it preserves `R_K` on no relation-
  preserving extension; in particular no element of the model at `τ₀` has these values.
-/

set_option autoImplicit false

namespace OR.Sieber

/-! ## Elements of `B ⇒ B` -/

/-- A monotone map `B → B` preserves every test. -/
theorem Test.holds_comp_of_mono {c : Val → Val} (hc : ∀ x y, Val.le x y → Val.le (c x) (c y))
    {w : ℕ} (d : Test w) {g : Fin w → Val} (hg : d.holds g) : d.holds (fun i => c (g i)) := by
  intro p hp hAB
  have hE := hg p hp hAB
  cases hc0 : c .bot with
  | bot =>
      rcases hE with ⟨i, hi, h⟩ | h
      · exact Or.inl ⟨i, hi, by simp only [h, hc0]⟩
      · exact Or.inr fun i hi j hj => by simp only [h i hi j hj]
  | tt =>
      have hconst : ∀ x, c x = .tt := fun x => by
        rcases hc .bot x (Or.inl rfl) with h | h
        · rw [hc0] at h; cases h
        · rw [← h, hc0]
      exact Or.inr fun i _ j _ => by simp only [hconst]
  | ff =>
      have hconst : ∀ x, c x = .ff := fun x => by
        rcases hc .bot x (Or.inl rfl) with h | h
        · rw [hc0] at h; cases h
        · rw [← h, hc0]
      exact Or.inr fun i _ j _ => by simp only [hconst]

/-- The join on `B`, defined by the first argument where it is defined. -/
def joinVal (a b : Val) : Val :=
  match a with
  | .bot => b
  | v => v

theorem joinVal_mono : ∀ f0 fy g0 gy : Val, Val.le f0 fy → Val.le g0 gy →
    (fy = .bot ∨ gy = .bot ∨ fy = gy) → Val.le (joinVal f0 g0) (joinVal fy gy) := by
  unfold Val.le; decide

/-- The pointwise join of two elements of `B ⇒ B`, defined by `f` where `f` is defined. -/
def joinFun (f g : SieberBool (.B ⇒ .B)) (x : Val) : Val := joinVal (f.1 x) (g.1 x)

/-- Two elements of `B ⇒ B` agree wherever both are defined. -/
def Agree (f g : SieberBool (.B ⇒ .B)) : Prop :=
  ∀ x, f.1 x = .bot ∨ g.1 x = .bot ∨ f.1 x = g.1 x

theorem joinFun_mono {f g : SieberBool (.B ⇒ .B)} (hfg : Agree f g) :
    ∀ x y, Val.le x y → Val.le (joinFun f g x) (joinFun f g y) := by
  intro x y hxy
  rcases hxy with rfl | rfl
  · exact joinVal_mono _ _ _ _ (f.2.1 _ _ (Or.inl rfl)) (g.2.1 _ _ (Or.inl rfl)) (hfg y)
  · exact Or.inr rfl

/-- The join of two agreeing elements of `B ⇒ B`, as an element of the model. -/
def joinBB (f g : SieberBool (.B ⇒ .B)) (hfg : Agree f g) : SieberBool (.B ⇒ .B) :=
  ⟨joinFun f g, joinFun_mono hfg, fun _ d _ hg => Test.holds_comp_of_mono (joinFun_mono hfg) d hg⟩

theorem le_joinBB_left (f g : SieberBool (.B ⇒ .B)) (hfg : Agree f g) :
    (Model (.B ⇒ .B)).le f (joinBB f g hfg) := by
  intro x
  show Val.le (f.1 x) (joinFun f g x)
  unfold joinFun joinVal
  cases f.1 x <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem le_joinBB_right (f g : SieberBool (.B ⇒ .B)) (hfg : Agree f g) :
    (Model (.B ⇒ .B)).le g (joinBB f g hfg) := by
  intro x
  show Val.le (g.1 x) (joinFun f g x)
  unfold joinFun joinVal
  rcases hfg x with h | h | h
  · rw [h]; exact Or.inr rfl
  · rw [h]; exact Or.inl rfl
  · rw [h]; cases g.1 x <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- Compatibility in `B ⇒ B` is agreement wherever both are defined. -/
theorem compat_iff_agree (f g : SieberBool (.B ⇒ .B)) : Compat f g ↔ Agree f g := by
  constructor
  · rintro ⟨c, hfc, hgc⟩ x
    rcases (hfc x : Val.le _ _) with h | h
    · exact Or.inl h
    rcases (hgc x : Val.le _ _) with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))
  · intro hfg
    exact ⟨joinBB f g hfg, le_joinBB_left f g hfg, le_joinBB_right f g hfg⟩

/-! ## The test `R_K` -/

variable {k : ℕ}

/-- The test `R_K`: `({1..k}, {0..k})` and `({i+1, j+1}, {i+1, j+1})` for each `P i j`. -/
def rkTest (P : Fin k → Fin k → Prop) [DecidableRel P] : Test (k + 1) :=
  insert (Finset.univ.image Fin.succ, Finset.univ)
    ((Finset.univ.filter (fun ij : Fin k × Fin k => P ij.1 ij.2)).image
      (fun ij => ({ij.1.succ, ij.2.succ}, {ij.1.succ, ij.2.succ})))

theorem rkTest_mem_top (P : Fin k → Fin k → Prop) [DecidableRel P] :
    ((Finset.univ.image Fin.succ, Finset.univ) : Finset (Fin (k + 1)) × Finset (Fin (k + 1)))
      ∈ rkTest P :=
  Finset.mem_insert_self _ _

theorem rkTest_mem_pair (P : Fin k → Fin k → Prop) [DecidableRel P] {i j : Fin k}
    (hij : P i j) :
    (({i.succ, j.succ}, {i.succ, j.succ}) :
      Finset (Fin (k + 1)) × Finset (Fin (k + 1))) ∈ rkTest P :=
  Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)

/-- Membership in `R_K`: the top pair and the `P`-pairs. -/
theorem rkTest_holds_iff (P : Fin k → Fin k → Prop) [DecidableRel P] (g : Fin (k + 1) → Val) :
    (rkTest P).holds g ↔
      Elem (Finset.univ.image Fin.succ) Finset.univ g ∧
      ∀ i j, P i j → Elem {i.succ, j.succ} {i.succ, j.succ} g := by
  constructor
  · intro h
    exact ⟨h _ (rkTest_mem_top P) (Finset.subset_univ _),
      fun i j hij => h _ (rkTest_mem_pair P hij) (subset_refl _)⟩
  · rintro ⟨htop, hpair⟩ p hp _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact htop
    · obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hp
      exact hpair ij.1 ij.2 (Finset.mem_filter.mp hij).2

/-- The ground tuple with `u` at `0`, `i + 1`, `j + 1` and `⊥` elsewhere. -/
def probe (i j : Fin k) (u : Val) (p : Fin (k + 1)) : Val :=
  if p = 0 ∨ p = i.succ ∨ p = j.succ then u else .bot

theorem probe_holds (P : Fin k → Fin k → Prop) [DecidableRel P] (i j : Fin k) (u : Val) :
    (rkTest P).holds (probe i j u) := by
  rw [rkTest_holds_iff]
  constructor
  · by_cases hm : ∃ m : Fin k, m ≠ i ∧ m ≠ j
    · obtain ⟨m, hmi, hmj⟩ := hm
      refine Or.inl ⟨m.succ, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      simp only [probe, Fin.succ_ne_zero, false_or, Fin.succ_inj, hmi, hmj, or_self,
        if_false]
    · push_neg at hm
      have hall : ∀ p, probe i j u p = u := by
        intro p
        refine Fin.cases ?_ (fun m => ?_) p
        · simp only [probe, true_or, if_true]
        · have : m = i ∨ m = j := by
            by_cases hmi : m = i
            · exact Or.inl hmi
            · exact Or.inr (hm m hmi)
          simp only [probe, Fin.succ_ne_zero, false_or, Fin.succ_inj]
          rw [if_pos this]
      exact Or.inr fun p _ q _ => by rw [hall, hall]
  · intro i' j' _
    by_cases hi' : i' = i ∨ i' = j
    · by_cases hj' : j' = i ∨ j' = j
      · refine Or.inr fun p hp q hq => ?_
        have hval : ∀ r ∈ ({i'.succ, j'.succ} : Finset (Fin (k + 1))), probe i j u r = u := by
          intro r hr
          rcases Finset.mem_insert.mp hr with rfl | hr
          · simp only [probe, Fin.succ_ne_zero, false_or, Fin.succ_inj, if_pos hi']
          · rw [Finset.mem_singleton.mp hr]
            simp only [probe, Fin.succ_ne_zero, false_or, Fin.succ_inj, if_pos hj']
        rw [hval p hp, hval q hq]
      · refine Or.inl ⟨j'.succ, by simp, ?_⟩
        simp only [probe, Fin.succ_ne_zero, false_or, Fin.succ_inj, if_neg hj']
    · refine Or.inl ⟨i'.succ, by simp, ?_⟩
      simp only [probe, Fin.succ_ne_zero, false_or, Fin.succ_inj, if_neg hi']

/-- **Step 1.** An `R_K`-related tuple at `B ⇒ B` is compatible on `P` at positions `1..k`. -/
theorem rk_compat (P : Fin k → Fin k → Prop) [DecidableRel P]
    (Φ : Fin (k + 1) → SieberBool (.B ⇒ .B)) (hΦ : (Model (.B ⇒ .B)).rel (k + 1) (rkTest P) Φ)
    {i j : Fin k} (hij : P i j) : Compat (Φ i.succ) (Φ j.succ) := by
  rw [compat_iff_agree]
  intro u
  have h := ((rkTest_holds_iff P _).mp (hΦ (probe i j u) (probe_holds P i j u))).2 i j hij
  have hi : probe i j u i.succ = u := by simp [probe]
  have hj : probe i j u j.succ = u := by simp [probe]
  rcases h with ⟨p, hp, hpb⟩ | h
  · rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Or.inl (by rw [← hi]; exact hpb)
    · rw [Finset.mem_singleton.mp hp] at hpb
      exact Or.inr (Or.inl (by rw [← hj]; exact hpb))
  · have := h i.succ (by simp) j.succ (by simp)
    simp only at this
    rw [hi, hj] at this
    exact Or.inr (Or.inr this)

theorem botτ₁_apply (φ : SieberBool (.B ⇒ .B)) : botτ₁.1 φ = .bot := rfl

/-- **Theorem 7, first part.** The tuple `(⊥, a₁, …, a_k)` is `R_K`-related at `τ₁`. -/
theorem rk_related (a : Fin k → SieberBool τ₁) (P : Fin k → Fin k → Prop) [DecidableRel P]
    (hP : ∀ i j, P i j → ∃ u, (Model τ₁).le (a i) u ∧ (Model τ₁).le (a j) u)
    (hno : ¬ ∃ φ : Fin k → SieberBool (.B ⇒ .B),
      (∀ i, (a i).1 (φ i) ≠ .bot) ∧ ∀ i j, P i j → Compat (φ i) (φ j)) :
    (Model τ₁).rel (k + 1) (rkTest P) (Fin.cons botτ₁ a) := by
  intro Φ hΦ
  show (rkTest P).holds _
  rw [rkTest_holds_iff]
  have hcomp : ∀ i j, P i j → Compat (Φ i.succ) (Φ j.succ) := fun i j hij => rk_compat P Φ hΦ hij
  constructor
  · -- some `aᵢ(φᵢ)` is undefined
    have : ∃ i, (a i).1 (Φ i.succ) = .bot := by
      by_contra hall
      exact hno ⟨fun i => Φ i.succ, fun i hi => hall ⟨i, hi⟩, hcomp⟩
    obtain ⟨i, hi⟩ := this
    exact Or.inl ⟨i.succ, Finset.mem_image_of_mem _ (Finset.mem_univ _), by simpa using hi⟩
  · intro i j hij
    obtain ⟨u, hiu, hju⟩ := hP i j hij
    obtain ⟨ψ, hiψ, hjψ⟩ := hcomp i j hij
    -- `aᵢ(φᵢ) ≤ u(φᵢ) ≤ u(ψ)` and `aⱼ(φⱼ) ≤ u(φⱼ) ≤ u(ψ)`
    have hi : Val.le ((a i).1 (Φ i.succ)) (u.1 ψ) :=
      Model.le_trans .B _ _ _ (hiu (Φ i.succ)) (u.2.1 _ _ hiψ)
    have hj : Val.le ((a j).1 (Φ j.succ)) (u.1 ψ) :=
      Model.le_trans .B _ _ _ (hju (Φ j.succ)) (u.2.1 _ _ hjψ)
    rcases hi with hi | hi
    · exact Or.inl ⟨i.succ, by simp, by simpa using hi⟩
    rcases hj with hj | hj
    · exact Or.inl ⟨j.succ, by simp, by simpa using hj⟩
    refine Or.inr fun p hp q hq => ?_
    have hval : ∀ r ∈ ({i.succ, j.succ} : Finset (Fin (k + 1))),
        ((Fin.cons botτ₁ a : Fin (k + 1) → SieberBool τ₁) r).1 (Φ r) = u.1 ψ := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · simpa using hi
      · rw [Finset.mem_singleton.mp hr]; simpa using hj
    exact (hval p hp).trans (hval q hq).symm

/-- **Theorem 7, second part.** For `h ⊥ = ⊥` and every `h (aᵢ)` defined, the image of
`(⊥, a₁, …, a_k)` under `h` lies outside `R_K`. -/
theorem rk_not_holds (hk : 0 < k) (a : Fin k → SieberBool τ₁) (P : Fin k → Fin k → Prop)
    [DecidableRel P] (h : SieberBool τ₁ → Val) (hbot : h botτ₁ = .bot)
    (ha : ∀ i, h (a i) ≠ .bot) :
    ¬ (rkTest P).holds (fun p => h ((Fin.cons botτ₁ a : Fin (k + 1) → SieberBool τ₁) p)) := by
  intro H
  rcases ((rkTest_holds_iff P _).mp H).1 with ⟨p, hp, hpb⟩ | hc
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ha i (by simpa using hpb)
  · have := hc (Fin.succ ⟨0, hk⟩) (Finset.mem_univ _) 0 (Finset.mem_univ _)
    simp only [Fin.cons_succ, Fin.cons_zero, hbot] at this
    exact ha _ this

/-- A map `h : τ₁ → B` with `h ⊥ = ⊥` and every `h (aᵢ)` defined does not preserve `R_K`. -/
theorem rk_not_preserved (hk : 0 < k) (a : Fin k → SieberBool τ₁) (P : Fin k → Fin k → Prop)
    [DecidableRel P]
    (hP : ∀ i j, P i j → ∃ u, (Model τ₁).le (a i) u ∧ (Model τ₁).le (a j) u)
    (hno : ¬ ∃ φ : Fin k → SieberBool (.B ⇒ .B),
      (∀ i, (a i).1 (φ i) ≠ .bot) ∧ ∀ i j, P i j → Compat (φ i) (φ j))
    (h : SieberBool τ₁ → Val) (hbot : h botτ₁ = .bot) (ha : ∀ i, h (a i) ≠ .bot) :
    ¬ ∀ g : Fin (k + 1) → SieberBool τ₁, (Model τ₁).rel (k + 1) (rkTest P) g →
      (rkTest P).holds (fun p => h (g p)) :=
  fun hpres => rk_not_holds hk a P h hbot ha (hpres _ (rk_related a P hP hno))

/-- No element of Sieber's model at `τ₀` is `⊥` at `⊥` and defined at every `aᵢ`. -/
theorem rk_no_element (hk : 0 < k) (a : Fin k → SieberBool τ₁) (P : Fin k → Fin k → Prop)
    [DecidableRel P]
    (hP : ∀ i j, P i j → ∃ u, (Model τ₁).le (a i) u ∧ (Model τ₁).le (a j) u)
    (hno : ¬ ∃ φ : Fin k → SieberBool (.B ⇒ .B),
      (∀ i, (a i).1 (φ i) ≠ .bot) ∧ ∀ i j, P i j → Compat (φ i) (φ j)) :
    ¬ ∃ H : SieberBool τ₀, H.1 botτ₁ = .bot ∧ ∀ i, H.1 (a i) ≠ .bot := by
  rintro ⟨H, hbot, ha⟩
  exact rk_not_preserved hk a P hP hno H.1 hbot ha (fun g hg => H.2.2 (k + 1) (rkTest P) g hg)

end OR.Sieber
