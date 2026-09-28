import OR.Compactness
import OR.Sieber.Transfer

/-!
# The ordinary natural Sieber model is an ω-algebraic, order-extensional model

These are the hypotheses of the Milner--Plotkin compact-definability theorem, checked
for `D^N`.  The argument is the one used for the Kripke model in `Projections` and
`Compactness`: the projections `ψⁿ` are idempotent, increasing in `n`, have finite
images, and approximate every element.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR.NS

theorem psi_index_mono : ∀ (τ : Ty) (d : D τ), Monotone (fun n => psi τ n d)
  | .nat, d, n, m, hnm => by
      change psi .nat n d ≤ psi .nat m d
      rw [psi_nat, psi_nat]
      cases d with
      | bot => exact le_rfl
      | val k =>
          by_cases hkn : k ≤ n
          · simp [Ground.cut, hkn, hkn.trans hnm]
          · simp only [Ground.cut, if_neg hkn]
            exact (bot_le : (⊥ : Ground) ≤ _)
  | .arr σ τ, f, n, m, hnm => fun x => by
      change psi (σ ⇒ τ) n f x ≤ psi (σ ⇒ τ) m f x
      rw [psi_arr, psi_arr]
      exact ((psi τ n).mono (f.mono (psi_index_mono σ x hnm))).trans (psi_index_mono τ _ hnm)

theorem psi_comp : ∀ (τ : Ty) (m n : ℕ) (d : D τ), psi τ m (psi τ n d) = psi τ (min m n) d
  | .nat, m, n, d => by
      cases d with
      | bot => simp [psi_nat, Ground.cut]
      | val k =>
          by_cases hn : k ≤ n <;> by_cases hm : k ≤ m <;>
            simp [psi_nat, Ground.cut, hn, hm, le_min_iff]
  | .arr σ τ, m, n, f => by
      apply Hom.ext
      intro x
      change psi (σ ⇒ τ) m (psi (σ ⇒ τ) n f) x = psi (σ ⇒ τ) (min m n) f x
      rw [psi_arr, psi_arr, psi_arr, psi_comp τ, psi_comp σ, min_comm n m]

@[simp] theorem psi_idem (τ : Ty) (n : ℕ) (d : D τ) : psi τ n (psi τ n d) = psi τ n d := by
  simpa only [min_self] using psi_comp τ n n d

def psiChain (τ : Ty) (d : D τ) : Chain (D τ) := ⟨fun n => psi τ n d, psi_index_mono τ d⟩

theorem psi_approximates : ∀ (τ : Ty) (d : D τ), (psiChain τ d).sup = d
  | .nat, d => by
      apply le_antisymm
      · exact (psiChain .nat d).sup_le (fun n => psi_le .nat n d)
      · cases d with
        | bot => exact bot_le
        | val k =>
            have h := (psiChain .nat (.val k)).le_sup k
            simpa [psiChain, psi_nat, Ground.cut] using h
  | .arr σ τ, f => by
      apply Hom.ext
      intro x
      rw [Hom.chain_sup_apply]
      let c : Chain (D τ) :=
        ⟨fun n => psi (σ ⇒ τ) n f x, fun _ _ h => psi_index_mono (σ ⇒ τ) f h x⟩
      change c.sup = f x
      apply le_antisymm
      · exact c.sup_le (fun n => psi_le (σ ⇒ τ) n f x)
      · have hx : x = (psiChain σ x).sup := (psi_approximates σ x).symm
        rw [hx]
        apply f.val.map_le _ (psiChain σ x).dir
        rintro _ ⟨n, rfl⟩
        calc
          f (psi σ n x) = (psiChain τ (f (psi σ n x))).sup := (psi_approximates τ _).symm
          _ ≤ c.sup := by
            apply Chain.sup_le
            intro m
            let k := max m n
            calc
              psi τ m (f (psi σ n x)) ≤ psi τ k (f (psi σ n x)) :=
                psi_index_mono τ _ (le_max_left _ _)
              _ ≤ psi τ k (f (psi σ k x)) :=
                (psi τ k).mono (f.mono (psi_index_mono σ x (le_max_right _ _)))
              _ = c k := (psi_arr σ τ k f x).symm
              _ ≤ c.sup := c.le_sup k

/-- The elements of level `n`. -/
abbrev NLevel (τ : Ty) (n : ℕ) := {d : D τ // psi τ n d = d}

theorem level_input {σ τ : Ty} {n : ℕ} {f : D (σ ⇒ τ)} (hf : psi (σ ⇒ τ) n f = f) (x : D σ) :
    f (psi σ n x) = f x := by
  have hpoint : ∀ y, psi τ n (f (psi σ n y)) = f y := fun y => by
    have h := congrArg (fun g : D (σ ⇒ τ) => g y) hf
    simpa only [psi_arr] using h
  calc
    f (psi σ n x) = psi τ n (f (psi σ n (psi σ n x))) := (hpoint _).symm
    _ = psi τ n (f (psi σ n x)) := by rw [psi_idem]
    _ = f x := hpoint x

theorem level_output {σ τ : Ty} {n : ℕ} {f : D (σ ⇒ τ)} (hf : psi (σ ⇒ τ) n f = f) (x : D σ) :
    psi τ n (f x) = f x := by
  have he : psi τ n (f (psi σ n x)) = f x := by
    simpa only [psi_arr] using congrArg (fun g : D (σ ⇒ τ) => g x) hf
  rw [← he, psi_idem]

def natLevelCode {n : ℕ} (a : NLevel .nat n) : Fin (n + 2) :=
  ⟨Ground.code a.val, by
    have hp := a.property
    cases h : a.val with
    | bot => simp [Ground.code]
    | val k =>
        have hk : k ≤ n := by
          rw [psi_nat, h] at hp
          by_contra hk
          simp [Ground.cut, hk] at hp
        simp only [Ground.code]
        omega⟩

theorem natLevelCode_injective (n : ℕ) : Function.Injective (@natLevelCode n) := by
  intro a b h
  apply Subtype.ext
  apply Ground.code_injective
  exact congrArg Fin.val h

def levelRestriction {σ τ : Ty} {n : ℕ} (f : NLevel (σ ⇒ τ) n) : NLevel σ n → NLevel τ n :=
  fun a => ⟨f.val a.val, level_output f.property a.val⟩

theorem levelRestriction_injective (σ τ : Ty) (n : ℕ) :
    Function.Injective (@levelRestriction σ τ n) := by
  intro f g h
  apply Subtype.ext
  apply Hom.ext
  intro x
  let a : NLevel σ n := ⟨psi σ n x, psi_idem σ n x⟩
  have he := congrArg (fun k : NLevel σ n → NLevel τ n => (k a).val) h
  change f.val (psi σ n x) = g.val (psi σ n x) at he
  rw [level_input f.property x, level_input g.property x] at he
  exact he

theorem finite_level : ∀ (τ : Ty) (n : ℕ), Finite (NLevel τ n)
  | .nat, n => Finite.of_injective natLevelCode (natLevelCode_injective n)
  | .arr σ τ, n =>
      letI : Finite (NLevel σ n) := finite_level σ n
      letI : Finite (NLevel τ n) := finite_level τ n
      Finite.of_injective levelRestriction (levelRestriction_injective σ τ n)

theorem psi_image_finite (τ : Ty) (n : ℕ) (s : Set (D τ)) : ((fun a => psi τ n a) '' s).Finite := by
  haveI := finite_level τ n
  apply (Set.finite_range (fun a : NLevel τ n => a.val)).subset
  rintro _ ⟨a, _, rfl⟩
  exact ⟨⟨psi τ n a, psi_idem τ n a⟩, rfl⟩

theorem level_compact (τ : Ty) (n : ℕ) (d : D τ) (hd : psi τ n d = d) : Compact d := by
  intro s hs hds
  let p : Hom (typeObj τ) (typeObj τ) := psi τ n
  have hpdir : Dir ((fun a => p a) '' s) := hs.image p p.mono
  obtain ⟨a, ha, hea⟩ := hpdir.finite_sup_mem (psi_image_finite τ n s)
  refine ⟨a, ha, ?_⟩
  calc
    d = p d := hd.symm
    _ ≤ p (dSup s hs) := p.mono hds
    _ = dSup ((fun a => p a) '' s) hpdir := p.val.map_dSup s hs
    _ = p a := hea.symm
    _ ≤ a := psi_le τ n a

theorem compact_iff_level (τ : Ty) (d : D τ) : Compact d ↔ ∃ n : ℕ, psi τ n d = d := by
  constructor
  · intro hd
    obtain ⟨a, ⟨n, rfl⟩, hn⟩ :=
      hd (Set.range (psiChain τ d).at) (psiChain τ d).dir (psi_approximates τ d).symm.le
    exact ⟨n, le_antisymm (psi_le τ n d) hn⟩
  · rintro ⟨n, hn⟩
    exact level_compact τ n d hn

/-! ## The premises of Milner--Plotkin -/

/-- Functions are ordered pointwise. -/
def OrderExtensional : Prop :=
  ∀ (σ τ : Ty) (f g : D (σ ⇒ τ)), f ≤ g ↔ ∀ x, f x ≤ g x

/-- Every element is the supremum of a chain of compact elements, and each type has
countably many compact elements. -/
def OmegaAlgebraic : Prop :=
  (∀ (τ : Ty) (d : D τ), ∃ c : Chain (D τ), c.sup = d ∧ ∀ n, Compact (c n)) ∧
    ∀ τ : Ty, {d : D τ | Compact d}.Countable

/-- `fix` denotes the least fixed point. -/
def LeastFixedPoints : Prop :=
  ∀ (τ : Ty) (M : Tm [] (τ ⇒ τ)),
    denoteClosed M (denoteClosed (.fix M)) = denoteClosed (.fix M) ∧
      ∀ y, denoteClosed M y ≤ y → denoteClosed (.fix M) ≤ y

theorem orderExtensional : OrderExtensional := fun _ _ _ _ => Iff.rfl

theorem omegaAlgebraic : OmegaAlgebraic := by
  refine ⟨fun τ d => ⟨psiChain τ d, psi_approximates τ d,
    fun n => level_compact τ n _ (psi_idem τ n d)⟩, fun τ => ?_⟩
  have hsub : {d : D τ | Compact d} ⊆ ⋃ n : ℕ, Set.range (fun a : NLevel τ n => a.val) := by
    intro d hd
    obtain ⟨n, hn⟩ := (compact_iff_level τ d).mp hd
    exact Set.mem_iUnion.mpr ⟨n, ⟨d, hn⟩, rfl⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun n => ?_)
  haveI := finite_level τ n
  exact (Set.finite_range _).countable

theorem leastFixedPoints : LeastFixedPoints := by
  intro τ M
  simp only [denoteClosed, denote_fix, Hom.fixMap_apply]
  exact ⟨lfp_unfold _, fun y hy => lfp_le _ hy⟩

end OR.NS
