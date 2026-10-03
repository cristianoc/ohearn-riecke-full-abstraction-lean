import OR.Sieber.Arity.Merge
import OR.Sieber.Soundness

/-!
# The arity bound R6

`ARITY.md` §3, Theorem R6, for `τ = σ₁ → ⋯ → σₙ → B` with `n ≥ 1`.

A candidate at `τ` is a function `f : D_{σ₁} → D_ρ` with `ρ = σ₂ → ⋯ → σₙ → B`. It *fails*
a test `d` of arity `w` when the constant tuple `(f, …, f)` is outside the lifted relation
`R_τ` (the clause defining `D_τ` in `Model`), stated by `Fails`.

* `Ty.arrows`, `Args`, `Args.rel`, `Args.apply`: argument lists, their tuples, the
  componentwise lifted relation, and full application.
* `Model.rel_arrows`: `(F_i)_i ∈ R_{σ₁ → ⋯ → σₙ → B}` iff every related tuple of argument
  columns gives a ground output in `R`.
* `columns`: a tuple `G : Fin w → α` factors as `y ∘ π` with `π : Fin w → Fin k` surjective,
  `y` injective, `k ≤ w`.
* `R6`: if R7 holds at every `σ_j` for every test and surjection, a candidate failing a test
  of arity `w` fails `π^*R` for a surjection `π : Fin w → Fin k` with `k ≤ w` and
  `k ≤ ∏_j |D_{σ_j}|`.
* `R6_bound`: the resulting arity bound `N(τ) ≤ ∏_j |D_{σ_j}|`.
-/

set_option autoImplicit false

namespace OR.Sieber

/-- `σ₁ → ⋯ → σₙ → b`. -/
def Ty.arrows : List Ty → Ty → Ty
  | [], b => b
  | σ :: l, b => .arr σ (Ty.arrows l b)

/-- Tuples of arguments `(a₁, …, aₙ) ∈ D_{σ₁} × ⋯ × D_{σₙ}`. -/
def Args : List Ty → Type
  | [] => PUnit
  | σ :: l => (Model σ).car × Args l

/-- The lifted relation on argument columns, componentwise. -/
def Args.rel : (l : List Ty) → (w : ℕ) → Test w → (Fin w → Args l) → Prop
  | [], _, _, _ => True
  | σ :: l, w, d, G => (Model σ).rel w d (fun i => (G i).1) ∧ Args.rel l w d (fun i => (G i).2)

/-- Full application of an element of `D_{σ₁ → ⋯ → σₙ → B}`. -/
def Args.apply : (l : List Ty) → (Model (Ty.arrows l .B)).car → Args l → Val
  | [], v, _ => v
  | _ :: l, f, a => Args.apply l (f.1 a.1) a.2

theorem Model.rel_arrows : ∀ (l : List Ty) {w : ℕ} (d : Test w)
    (F : Fin w → (Model (Ty.arrows l .B)).car),
    (Model (Ty.arrows l .B)).rel w d F ↔
      ∀ G : Fin w → Args l, Args.rel l w d G → d.holds (fun i => Args.apply l (F i) (G i))
  | [], _, d, F => by
      constructor
      · intro h _ _; exact h
      · intro h; exact h (fun _ => PUnit.unit) trivial
  | σ :: l, _, d, F => by
      show (∀ g, (Model σ).rel _ d g → (Model (Ty.arrows l .B)).rel _ d _) ↔ _
      constructor
      · intro h G hG
        exact (Model.rel_arrows l d _).mp (h _ hG.1) (fun i => (G i).2) hG.2
      · intro h g hg
        refine (Model.rel_arrows l d _).mpr fun G hG => ?_
        exact h (fun i => (g i, G i)) ⟨hg, hG⟩

/-- R7 at each argument type lifts to argument columns. -/
theorem Args.rel_pullback : ∀ (l : List Ty) {w k : ℕ} (d : Test w) (π : Fin w → Fin k),
    (∀ σ ∈ l, R7 σ d π) →
    ∀ y : Fin k → Args l, Args.rel l w d (y ∘ π) → Args.rel l k (d.pullback π) y
  | [], _, _, _, _, _, _, _ => trivial
  | σ :: l, _, _, d, π, h, y, hy =>
      ⟨h σ (by simp) (fun j => (y j).1) hy.1,
        Args.rel_pullback l d π (fun τ hτ => h τ (by simp [hτ]))
          (fun j => (y j).2) hy.2⟩

theorem Args.finite : ∀ l : List Ty, Finite (Args l)
  | [] => by show Finite PUnit; infer_instance
  | σ :: l => by
      haveI := finite_car σ
      haveI := Args.finite l
      show Finite ((Model σ).car × Args l); infer_instance

theorem Args.card : ∀ l : List Ty,
    Nat.card (Args l) = (l.map fun σ => Nat.card (Model σ).car).prod
  | [] => by show Nat.card PUnit = _; simp
  | σ :: l => by
      rw [List.map_cons, List.prod_cons, ← Args.card l]
      show Nat.card ((Model σ).car × Args l) = _
      exact Nat.card_prod _ _

/-- The candidate `f` fails the test `d`: `(f, …, f) ∉ R_{σ → ρ}`. -/
def Fails (σ ρ : Ty) (f : (Model σ).car → (Model ρ).car) {w : ℕ} (d : Test w) : Prop :=
  ¬ ∀ g : Fin w → (Model σ).car, (Model σ).rel w d g → (Model ρ).rel w d (fun i => f (g i))

/-- A tuple factors through the set of its distinct entries. -/
theorem columns {α : Type*} {w : ℕ} (G : Fin w → α) :
    ∃ (k : ℕ) (π : Fin w → Fin k) (y : Fin k → α),
      Function.Surjective π ∧ Function.Injective y ∧ y ∘ π = G ∧ k ≤ w := by
  classical
  let s := Finset.univ.image G
  let e := s.equivFin
  refine ⟨s.card, fun i => e ⟨G i, Finset.mem_image_of_mem G (Finset.mem_univ i)⟩,
    fun l => (e.symm l).1, ?_, ?_, ?_, ?_⟩
  · intro l
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (e.symm l).2
    refine ⟨i, ?_⟩
    rw [← e.apply_symm_apply l]
    exact congrArg e (Subtype.ext hi)
  · intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  · funext i
    simp
  · simpa using Finset.card_image_le (s := Finset.univ) (f := G)

/-- **Theorem R6.** Let `τ = σ₁ → ⋯ → σₙ → B` and suppose R7 holds at every `σ_j` for every
test and every surjection. If a candidate `f` fails a test `d` of arity `w`, it fails
`π^* d` for a surjection `π : Fin w → Fin k` with `k ≤ w` and `k ≤ ∏_j |D_{σ_j}|`. -/
theorem R6 (σ : Ty) (rest : List Ty)
    (hR7 : ∀ τ ∈ σ :: rest, ∀ (w k : ℕ) (d : Test w) (π : Fin w → Fin k),
      Function.Surjective π → R7 τ d π)
    (f : (Model σ).car → (Model (Ty.arrows rest .B)).car) {w : ℕ} (d : Test w)
    (hf : Fails σ (Ty.arrows rest .B) f d) :
    ∃ (k : ℕ) (π : Fin w → Fin k), Function.Surjective π ∧ k ≤ w ∧
      k ≤ ((σ :: rest).map fun τ => Nat.card (Model τ).car).prod ∧
      Fails σ (Ty.arrows rest .B) f (d.pullback π) := by
  -- A failing tuple of argument columns.
  obtain ⟨G, hG, hout⟩ : ∃ G : Fin w → Args (σ :: rest), Args.rel (σ :: rest) w d G ∧
      ¬ d.holds (fun i => Args.apply rest (f (G i).1) (G i).2) := by
    by_contra hc
    push_neg at hc
    refine hf fun g hg => (Model.rel_arrows rest d _).mpr fun G' hG' => ?_
    exact hc (fun i => (g i, G' i)) ⟨hg, hG'⟩
  obtain ⟨k, π, y, hπ, hy, hyπ, hkw⟩ := columns G
  refine ⟨k, π, hπ, hkw, ?_, ?_⟩
  · haveI := Args.finite (σ :: rest)
    rw [← Args.card]
    have := Finite.card_le_of_injective y hy
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  · intro hsucc
    have hyrel : Args.rel (σ :: rest) k (d.pullback π) y :=
      Args.rel_pullback (σ :: rest) d π (fun τ hτ => hR7 τ hτ w k d π hπ) y (hyπ ▸ hG)
    have hk := (Model.rel_arrows rest (d.pullback π) _).mp (hsucc _ hyrel.1)
      (fun j => (y j).2) hyrel.2
    apply hout
    have := congrFun (Test.holds_pullback π d) (fun j => Args.apply rest (f (y j).1) (y j).2)
    rw [← this] at hk
    simpa [pullback, Function.comp_def, ← hyπ] using hk

/-- The arity bound of R6: under its hypothesis, a candidate that fails some test fails one
of arity at most `∏_j |D_{σ_j}|`. -/
theorem R6_bound (σ : Ty) (rest : List Ty)
    (hR7 : ∀ τ ∈ σ :: rest, ∀ (w k : ℕ) (d : Test w) (π : Fin w → Fin k),
      Function.Surjective π → R7 τ d π)
    (f : (Model σ).car → (Model (Ty.arrows rest .B)).car) {w : ℕ} (d : Test w)
    (hf : Fails σ (Ty.arrows rest .B) f d) :
    ∃ (k : ℕ) (d' : Test k), k ≤ ((σ :: rest).map fun τ => Nat.card (Model τ).car).prod ∧
      Fails σ (Ty.arrows rest .B) f d' := by
  obtain ⟨k, π, -, -, hk, hfk⟩ := R6 σ rest hR7 f d hf
  exact ⟨k, d.pullback π, hk, hfk⟩

end OR.Sieber
