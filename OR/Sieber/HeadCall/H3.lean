import OR.Sieber.HeadCall

/-!
# The table `h₃` is not definable

§5.2 of `HEADCALL.md`. The points `129, 272, 321` of `D₂` and the common upper bounds
`281 ≥ 129, 272` and `333 ≥ 129, 321` (indices of `gpu/REPORT.md`) are denotations of
closed terms. Writing `a` for the argument of type `B ⇒ B`:

* `m₀ = 129 = ⟦λa. if a tt then (if a ff then ⊥ else ff) else (if a ff then tt else ff)⟧`
* `m₁ = 272 = ⟦λa. if a tt then ff else ⊥⟧`
* `m₂ = 321 = ⟦λa. if a ff then tt else a ⊥⟧`
* `u₀₁ = 281 = ⟦λa. if a tt then ff else (if a ff then tt else ff)⟧`
* `u₀₂ = 333 = ⟦λa. if a ff then tt else (if a tt then ff else ff)⟧`

`h₃` is `ff` on the union of the up-cones of `m₀, m₁, m₂` and `⊥` elsewhere. Theorem 6
(`firstCall_compat`) with `P = {(0,1), (0,2)}` shows that no closed term agrees with `h₃`
on any set `S` containing `⊥, m₀, m₁, m₂`.
-/

set_option autoImplicit false

namespace OR.Sieber.H3

open OR.Sieber

instance : DecidableRel Val.le := fun a b => by unfold Val.le; infer_instance

/-- The call `a v` of the bound variable `a : B ⇒ B`. -/
abbrev call (v : Tm [.B ⇒ .B] .B) : Tm [.B ⇒ .B] .B := .app (.var .vz) v

/-- Point 129. -/
def m0 : SieberBool τ₁ :=
  (Tm.lam (.ite (call .tt) (.ite (call .ff) .bot .ff) (.ite (call .ff) .tt .ff)) : Tm [] τ₁).den
/-- Point 272. -/
def m1 : SieberBool τ₁ := (Tm.lam (.ite (call .tt) .ff .bot) : Tm [] τ₁).den
/-- Point 321. -/
def m2 : SieberBool τ₁ := (Tm.lam (.ite (call .ff) .tt (call .bot)) : Tm [] τ₁).den
/-- Point 281, an upper bound of 129 and 272. -/
def u01 : SieberBool τ₁ :=
  (Tm.lam (.ite (call .tt) .ff (.ite (call .ff) .tt .ff)) : Tm [] τ₁).den
/-- Point 333, an upper bound of 129 and 321. -/
def u02 : SieberBool τ₁ :=
  (Tm.lam (.ite (call .ff) .tt (.ite (call .tt) .ff .ff)) : Tm [] τ₁).den

variable (a : SieberBool (.B ⇒ .B))

theorem m0_apply : m0.1 a =
    Val.ite (a.1 .tt) (Val.ite (a.1 .ff) .bot .ff) (Val.ite (a.1 .ff) .tt .ff) := rfl
theorem m1_apply : m1.1 a = Val.ite (a.1 .tt) .ff .bot := rfl
theorem m2_apply : m2.1 a = Val.ite (a.1 .ff) .tt (a.1 .bot) := rfl
theorem u01_apply : u01.1 a = Val.ite (a.1 .tt) .ff (Val.ite (a.1 .ff) .tt .ff) := rfl
theorem u02_apply : u02.1 a = Val.ite (a.1 .ff) .tt (Val.ite (a.1 .tt) .ff .ff) := rfl
theorem botτ₁_apply : botτ₁.1 a = .bot := rfl

/-- An element of `B ⇒ B` is monotone: `a ⊥ ≤ a tt` and `a ⊥ ≤ a ff`. -/
theorem mono_vals : Val.le (a.1 .bot) (a.1 .tt) ∧ Val.le (a.1 .bot) (a.1 .ff) :=
  ⟨a.2.1 .bot .tt (Or.inl rfl), a.2.1 .bot .ff (Or.inl rfl)⟩

/-! ## The order facts -/

theorem m0_le_u01 : (Model τ₁).le m0 u01 := fun a => by
  show Val.le (m0.1 a) (u01.1 a)
  rw [m0_apply, u01_apply]
  generalize a.1 .tt = x; generalize a.1 .ff = y
  revert x y; change ∀ x y : Val, _; decide

theorem m1_le_u01 : (Model τ₁).le m1 u01 := fun a => by
  show Val.le (m1.1 a) (u01.1 a)
  rw [m1_apply, u01_apply]
  generalize a.1 .tt = x; generalize a.1 .ff = y
  revert x y; change ∀ x y : Val, _; decide

theorem m0_le_u02 : (Model τ₁).le m0 u02 := fun a => by
  show Val.le (m0.1 a) (u02.1 a)
  rw [m0_apply, u02_apply]
  generalize a.1 .tt = x; generalize a.1 .ff = y
  revert x y; change ∀ x y : Val, _; decide

theorem m2_le_u02 : (Model τ₁).le m2 u02 := fun a => by
  show Val.le (m2.1 a) (u02.1 a)
  obtain ⟨hx, hy⟩ := mono_vals a
  rw [m2_apply, u02_apply]
  revert hx hy
  generalize a.1 .bot = p; generalize a.1 .tt = x; generalize a.1 .ff = y
  revert p x y; change ∀ p x y : Val, _; decide

/-! ## The table -/

/-- The three points, indexed by `Fin 3`. -/
def m : Fin 3 → SieberBool τ₁ := ![m0, m1, m2]

/-- `F` lies in the up-cone of `m₀`, `m₁` or `m₂`. -/
def InCones (F : SieberBool τ₁) : Prop := ∃ i, (Model τ₁).le (m i) F

open Classical in
/-- `h₃`: `ff` on `↑m₀ ∪ ↑m₁ ∪ ↑m₂`, `⊥` elsewhere. -/
noncomputable def h3 (F : SieberBool τ₁) : Val := if InCones F then .ff else .bot

/-- `⟦λx. x⟧ = ⊥tf`. -/
def idB : SieberBool (.B ⇒ .B) := (Tm.lam (.var .vz) : Tm [] (.B ⇒ .B)).den
/-- `⟦λx. tt⟧ = ttt`. -/
def ttB : SieberBool (.B ⇒ .B) := (Tm.lam .tt : Tm [] (.B ⇒ .B)).den

theorem h3_bot : h3 botτ₁ = .bot := by
  have hn : ¬ InCones botτ₁ := by
    rintro ⟨i, hi⟩
    fin_cases i
    · have h : Val.le .ff .bot := hi idB
      revert h; decide
    · have h : Val.le .ff .bot := hi idB
      revert h; decide
    · have h : Val.le .tt .bot := hi ttB
      revert h; decide
  simp only [h3, hn, if_false]

theorem h3_m (i : Fin 3) : h3 (m i) ≠ .bot := by
  have hc : InCones (m i) := ⟨i, Model.le_refl τ₁ _⟩
  simp only [h3, hc, if_true]
  decide

/-! ## No compatible choice of first-call arguments -/

/-- Compatible elements of `B ⇒ B` agree wherever both are defined. -/
theorem compat_agree {a b : SieberBool (.B ⇒ .B)} (h : Compat a b) (v : Val) :
    a.1 v = .bot ∨ b.1 v = .bot ∨ a.1 v = b.1 v := by
  obtain ⟨c, hac, hbc⟩ := h
  rcases hac v with h1 | h1
  · exact Or.inl h1
  rcases hbc v with h2 | h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (h1.trans h2.symm))

/-- The pairs with a common upper bound: `(0,1)` along `281` and `(0,2)` along `333`. -/
def P (i j : Fin 3) : Prop := (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2)

theorem P_bound (i j : Fin 3) (h : P i j) :
    ∃ u, (Model τ₁).le (m i) u ∧ (Model τ₁).le (m j) u := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨u01, m0_le_u01, m1_le_u01⟩
  · exact ⟨u02, m0_le_u02, m2_le_u02⟩

/-- The finite core of `no_choice`, on the values `a₀ tt, a₀ ff, a₁ tt, a₂ ⊥, a₂ tt, a₂ ff`. -/
theorem no_choice_vals : ∀ x0 y0 x1 p2 x2 y2 : Val,
    Val.ite x0 (Val.ite y0 .bot .ff) (Val.ite y0 .tt .ff) ≠ .bot →
    Val.ite x1 .ff .bot ≠ .bot →
    Val.ite y2 .tt p2 ≠ .bot →
    (x0 = .bot ∨ x1 = .bot ∨ x0 = x1) →
    (x0 = .bot ∨ x2 = .bot ∨ x0 = x2) →
    (y0 = .bot ∨ y2 = .bot ∨ y0 = y2) →
    Val.le p2 x2 → Val.le p2 y2 → False := by
  decide

theorem no_choice : ¬ ∃ a : Fin 3 → SieberBool (.B ⇒ .B),
    (∀ i, (m i).1 (a i) ≠ .bot) ∧ ∀ i j, P i j → Compat (a i) (a j) := by
  rintro ⟨a, ha, hc⟩
  have h0 : m0.1 (a 0) ≠ .bot := ha 0
  have h1 : m1.1 (a 1) ≠ .bot := ha 1
  have h2 : m2.1 (a 2) ≠ .bot := ha 2
  rw [m0_apply] at h0
  rw [m1_apply] at h1
  rw [m2_apply] at h2
  have c01 := compat_agree (hc 0 1 (Or.inl ⟨rfl, rfl⟩)) .tt
  have c02t := compat_agree (hc 0 2 (Or.inr ⟨rfl, rfl⟩)) .tt
  have c02f := compat_agree (hc 0 2 (Or.inr ⟨rfl, rfl⟩)) .ff
  have mono2 := mono_vals (a 2)
  exact no_choice_vals _ _ _ _ _ _ h0 h1 h2 c01 c02t c02f mono2.1 mono2.2

/-! ## Non-definability -/

/-- **`h₃` is not definable** on any set of arguments containing `⊥, m₀, m₁, m₂`. -/
theorem not_definableOn {S : Set (SieberBool τ₁)} (hbotS : botτ₁ ∈ S) (hmS : ∀ i, m i ∈ S) :
    ¬ DefinableOn S h3 :=
  firstCall_compat hbotS h3_bot m hmS h3_m P P_bound no_choice

/-- On `D₂`, the definable elements of `τ₁`. -/
theorem not_definableOn_definable : ¬ DefinableOn {F | Definable F} h3 :=
  not_definableOn ⟨_, rfl⟩ (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)

theorem not_definableOn_univ : ¬ DefinableOn Set.univ h3 :=
  not_definableOn (Set.mem_univ _) (fun _ => Set.mem_univ _)

/-- No closed term of type `τ₀` denotes `h₃`. -/
theorem not_definable : ¬ ∃ t : Tm [] τ₀, ∀ F, t.den.1 F = h3 F :=
  fun ⟨t, ht⟩ => not_definableOn_univ ⟨t, fun F _ => ht F⟩

end OR.Sieber.H3
