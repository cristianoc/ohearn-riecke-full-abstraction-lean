import OR.Sieber.Arity.Bound

/-!
# The arity bound from R7′

`R7.md` §5, Conjecture R7′, stated without `C_w`, and the arity bound R6 under it.

* `R7w σ` (R7′ at `σ`): for every test `d` of arity `w`, every surjection
  `π : Fin w → Fin k`, every `x : Fin k → D_σ` with `x ∘ π ∈ R_σ` and every ground
  `v : Fin k → Val` outside `π^*R`, some test `d'` of arity `k` has `x ∈ R'_σ` and `v ∉ R'`.
* `R7w_of_R7`: R7 at `σ` for every test and surjection implies `R7w σ`, with `d' = π^* d`.
* `R7wArgs l`: the same statement for tuples of argument columns `Fin k → Args l`, with one
  test `d'` relating every column. It is the hypothesis the multi-argument bound uses.
  `R7wArgs_of_R7` derives it from R7 at every type of `l`; `R7wArgs_single` derives
  `R7wArgs [σ]` from `R7w σ`.
* `R6w`: under `R7wArgs (σ :: rest)`, a candidate failing a test of arity `w` fails a test
  of arity `k ≤ w` with `k ≤ ∏_j |D_{σ_j}|`.
* `R6w_one`: the one-argument case `τ = σ → B` under `R7w σ`.
-/

set_option autoImplicit false

namespace OR.Sieber

/-- R7′ at type `σ`. -/
def R7w (σ : Ty) : Prop :=
  ∀ (w k : ℕ) (d : Test w) (π : Fin w → Fin k), Function.Surjective π →
    ∀ x : Fin k → (Model σ).car, (Model σ).rel w d (x ∘ π) →
    ∀ v : Fin k → Val, ¬ (d.pullback π).holds v →
    ∃ d' : Test k, (Model σ).rel k d' x ∧ ¬ d'.holds v

/-- R7 implies R7′, with `d' = π^* d`. -/
theorem R7w_of_R7 (σ : Ty)
    (h : ∀ (w k : ℕ) (d : Test w) (π : Fin w → Fin k), Function.Surjective π → R7 σ d π) :
    R7w σ :=
  fun _ _ d π hπ x hx _ hv => ⟨d.pullback π, h _ _ d π hπ x hx, hv⟩

/-- R7′ for tuples of argument columns: one test of arity `k` relates all columns. -/
def R7wArgs (l : List Ty) : Prop :=
  ∀ (w k : ℕ) (d : Test w) (π : Fin w → Fin k), Function.Surjective π →
    ∀ y : Fin k → Args l, Args.rel l w d (y ∘ π) →
    ∀ v : Fin k → Val, ¬ (d.pullback π).holds v →
    ∃ d' : Test k, Args.rel l k d' y ∧ ¬ d'.holds v

/-- R7 at every argument type implies `R7wArgs`, with `d' = π^* d`. -/
theorem R7wArgs_of_R7 (l : List Ty)
    (h : ∀ τ ∈ l, ∀ (w k : ℕ) (d : Test w) (π : Fin w → Fin k),
      Function.Surjective π → R7 τ d π) :
    R7wArgs l :=
  fun w k d π hπ y hy _ hv =>
    ⟨d.pullback π, Args.rel_pullback l d π (fun τ hτ => h τ hτ w k d π hπ) y hy, hv⟩

/-- With one argument type, `R7wArgs [σ]` follows from `R7w σ`. -/
theorem R7wArgs_single (σ : Ty) (h : R7w σ) : R7wArgs [σ] := by
  intro w k d π hπ y hy v hv
  obtain ⟨d', hd', hvd'⟩ := h w k d π hπ (fun j => (y j).1) hy.1 v hv
  exact ⟨d', ⟨hd', trivial⟩, hvd'⟩

/-- **R6 from R7′.** Let `τ = σ₁ → ⋯ → σₙ → B` and suppose `R7wArgs [σ₁, …, σₙ]`. If a
candidate `f` fails a test of arity `w`, it fails a test of arity `k` with `k ≤ w` and
`k ≤ ∏_j |D_{σ_j}|`. -/
theorem R6w (σ : Ty) (rest : List Ty) (hR7w : R7wArgs (σ :: rest))
    (f : (Model σ).car → (Model (Ty.arrows rest .B)).car) {w : ℕ} (d : Test w)
    (hf : Fails σ (Ty.arrows rest .B) f d) :
    ∃ (k : ℕ) (d' : Test k), k ≤ w ∧
      k ≤ ((σ :: rest).map fun τ => Nat.card (Model τ).car).prod ∧
      Fails σ (Ty.arrows rest .B) f d' := by
  -- A failing tuple of argument columns.
  obtain ⟨G, hG, hout⟩ : ∃ G : Fin w → Args (σ :: rest), Args.rel (σ :: rest) w d G ∧
      ¬ d.holds (fun i => Args.apply rest (f (G i).1) (G i).2) := by
    by_contra hc
    push_neg at hc
    refine hf fun g hg => (Model.rel_arrows rest d _).mpr fun G' hG' => ?_
    exact hc (fun i => (g i, G' i)) ⟨hg, hG'⟩
  obtain ⟨k, π, y, hπ, hy, hyπ, hkw⟩ := columns G
  -- The output pattern on the distinct columns, excluded by `π^* d`.
  set v : Fin k → Val := fun j => Args.apply rest (f (y j).1) (y j).2 with hv
  have hvout : ¬ (d.pullback π).holds v := by
    rw [← Test.holds_pullback]
    intro h
    apply hout
    simpa [pullback, Function.comp_def, hv, ← hyπ] using h
  obtain ⟨d', hd', hvd'⟩ := hR7w w k d π hπ y (hyπ ▸ hG) v hvout
  refine ⟨k, d', hkw, ?_, ?_⟩
  · haveI := Args.finite (σ :: rest)
    rw [← Args.card]
    have := Finite.card_le_of_injective y hy
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  · intro hsucc
    exact hvd' ((Model.rel_arrows rest d' _).mp (hsucc _ hd'.1) (fun j => (y j).2) hd'.2)

/-- **R6 from R7′, one argument.** For `τ = σ → B` under `R7w σ`, a candidate failing a test
of arity `w` fails a test of arity `k ≤ w` with `k ≤ |D_σ|`. -/
theorem R6w_one (σ : Ty) (hR7w : R7w σ) (f : (Model σ).car → (Model .B).car) {w : ℕ}
    (d : Test w) (hf : Fails σ .B f d) :
    ∃ (k : ℕ) (d' : Test k), k ≤ w ∧ k ≤ Nat.card (Model σ).car ∧ Fails σ .B f d' := by
  obtain ⟨k, d', hkw, hk, hfk⟩ := R6w σ [] (R7wArgs_single σ hR7w) f d hf
  refine ⟨k, d', hkw, ?_, hfk⟩
  simpa using hk

end OR.Sieber
