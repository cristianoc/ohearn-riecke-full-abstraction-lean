import OR.Sieber.Arity.Reindex

/-!
# Single merges suffice for R7

`R7.md` §1, Lemma M2, at an arbitrary type `σ` of Sieber's model.

For a test `d` of arity `w` and a map `π : Fin w → Fin k`, `R7 σ d π` states
`π^*(R_σ) ⊆ (π^*R)_σ`: every `x : Fin k → D_σ` with `x ∘ π ∈ R_σ` lies in `(π^*R)_σ`,
where `R` is the relation denoted by `d` and `π^*R` the one denoted by `d.pullback π`.

* `Model.rel_congr`: the lifted relation of a test depends only on the ground relation it
  denotes.
* `Model.rel_reindex_equiv`, `R7_of_bijective`: R7 holds for every bijection.
* `merge`, `merge_surjective`, `comp_merge`: a map `π : Fin (m+1) → Fin k` with
  `π i = π j`, `i ≠ j`, factors as `π = s ∘ merge i j` with `merge i j : Fin (m+1) → Fin m`
  surjective; `s` is surjective when `π` is.
* `R7_of_single_merges` (M2): if R7 holds at `σ` for every test and every surjection
  `Fin (n+1) → Fin n` (a map identifying exactly two coordinates), it holds at `σ` for every
  test and every surjection.
-/

set_option autoImplicit false

namespace OR.Sieber

/-- R7 for `(d, π)` at type `σ`: `π^*(R_σ) ⊆ (π^*R)_σ`. -/
def R7 (σ : Ty) {w k : ℕ} (d : Test w) (π : Fin w → Fin k) : Prop :=
  ∀ x : Fin k → (Model σ).car, (Model σ).rel w d (x ∘ π) → (Model σ).rel k (d.pullback π) x

/-- The lifted relation of a test depends only on the ground relation it denotes. -/
theorem Model.rel_congr : ∀ (τ : Ty) {w : ℕ} {d d' : Test w}, d.holds = d'.holds →
    ∀ g : Fin w → (Model τ).car, (Model τ).rel w d g ↔ (Model τ).rel w d' g
  | .B, _, _, _, h, g => by
      exact iff_of_eq (congrFun h g)
  | .arr σ τ, _, _, _, h, F => by
      show (∀ g, (Model σ).rel _ _ g → (Model τ).rel _ _ _) ↔
        (∀ g, (Model σ).rel _ _ g → (Model τ).rel _ _ _)
      exact forall_congr' fun g =>
        imp_congr (Model.rel_congr σ h g) (Model.rel_congr τ h _)

/-- Lifted relations commute with reindexing along a bijection. -/
theorem Model.rel_reindex_equiv : ∀ (τ : Ty) {w k : ℕ} (d : Test w) (e : Fin w ≃ Fin k)
    (x : Fin k → (Model τ).car),
    (Model τ).rel w d (x ∘ e) ↔ (Model τ).rel k (d.pullback e) x
  | .B, _, _, d, e, x => by
      show d.holds (x ∘ e) ↔ (d.pullback e).holds x
      rw [← Test.holds_pullback]
      rfl
  | .arr σ τ, _, _, d, e, x => by
      constructor
      · intro hx y hy
        have hy' : (Model σ).rel _ d (y ∘ e) := (Model.rel_reindex_equiv σ d e y).mpr hy
        exact (Model.rel_reindex_equiv τ d e (fun j => (x j).1 (y j))).mp (hx _ hy')
      · intro hx g hg
        have hg' : (Model σ).rel _ d ((g ∘ e.symm) ∘ e) := by
          simpa [Function.comp_def] using hg
        have := hx _ ((Model.rel_reindex_equiv σ d e (g ∘ e.symm)).mp hg')
        have := (Model.rel_reindex_equiv τ d e (fun j => (x j).1 ((g ∘ e.symm) j))).mpr this
        simpa [Function.comp_def] using this

/-- R7 holds for every bijection. -/
theorem R7_of_bijective (σ : Ty) {w k : ℕ} (d : Test w) (π : Fin w → Fin k)
    (hπ : Function.Bijective π) : R7 σ d π := by
  intro x hx
  exact (Model.rel_reindex_equiv σ d (Equiv.ofBijective π hπ) x).mp hx

/-- The map `Fin (m+1) → Fin m` identifying `j` with `i` and otherwise inverting
`j.succAbove`. -/
noncomputable def merge {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j) : Fin (m + 1) → Fin m :=
  fun x => if h : x = j then (Fin.exists_succAbove_eq hij).choose
    else (Fin.exists_succAbove_eq h).choose

theorem succAbove_merge {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j) (x : Fin (m + 1)) :
    j.succAbove (merge i j hij x) = if x = j then i else x := by
  unfold merge
  split_ifs with h
  · exact (Fin.exists_succAbove_eq hij).choose_spec
  · exact (Fin.exists_succAbove_eq h).choose_spec

theorem merge_surjective {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j) :
    Function.Surjective (merge i j hij) := by
  intro z
  refine ⟨j.succAbove z, ?_⟩
  apply Fin.succAbove_right_injective (p := j)
  rw [succAbove_merge, if_neg (Fin.succAbove_ne j z)]

/-- `merge i j` identifies `i` and `j`. -/
theorem merge_eq {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j) :
    merge i j hij j = merge i j hij i := by
  apply Fin.succAbove_right_injective (p := j)
  rw [succAbove_merge, succAbove_merge, if_pos rfl, if_neg hij]

/-- A map with `π i = π j` factors through `merge i j`. -/
theorem comp_merge {m k : ℕ} (π : Fin (m + 1) → Fin k) (i j : Fin (m + 1)) (hij : i ≠ j)
    (hπ : π i = π j) : (π ∘ j.succAbove) ∘ merge i j hij = π := by
  funext x
  simp only [Function.comp_apply, succAbove_merge]
  split_ifs with h
  · rw [hπ, h]
  · rfl

/-- **Lemma M2.** If R7 holds at `σ` for every test and every surjection `Fin (n+1) → Fin n`,
then it holds at `σ` for every test and every surjection. -/
theorem R7_of_single_merges (σ : Ty)
    (h : ∀ (n : ℕ) (d : Test (n + 1)) (ρ : Fin (n + 1) → Fin n),
      Function.Surjective ρ → R7 σ d ρ) :
    ∀ (w k : ℕ) (d : Test w) (π : Fin w → Fin k), Function.Surjective π → R7 σ d π := by
  intro w
  induction w with
  | zero =>
      intro k d π hπ
      apply R7_of_bijective
      refine ⟨fun a => a.elim0, hπ⟩
  | succ m ih =>
      intro k d π hπ
      by_cases hinj : Function.Injective π
      · exact R7_of_bijective σ d π ⟨hinj, hπ⟩
      obtain ⟨i, j, hπij, hij⟩ : ∃ i j, π i = π j ∧ i ≠ j := by
        by_contra hc
        push_neg at hc
        exact hinj fun a b hab => hc a b hab
      set s := π ∘ j.succAbove with hs
      have hfac : s ∘ merge i j hij = π := comp_merge π i j hij hπij
      have hsurj : Function.Surjective s := by
        intro z
        obtain ⟨x, rfl⟩ := hπ z
        exact ⟨merge i j hij x, congrFun hfac x⟩
      intro x hx
      have h1 : (Model σ).rel m (d.pullback (merge i j hij)) (x ∘ s) := by
        apply h m d (merge i j hij) (merge_surjective i j hij)
        rw [Function.comp_assoc, hfac]
        exact hx
      have h2 := ih k (d.pullback (merge i j hij)) s hsurj x h1
      refine (Model.rel_congr σ ?_ x).mp h2
      rw [Test.holds_pullback_comp, hfac]

end OR.Sieber
