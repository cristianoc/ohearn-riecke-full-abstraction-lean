import OR.Definability

/-!
# Compact elements and algebraicity

These results are consequences of the constructed projections, not assumptions
used to construct the model. They also give a separate check on finite-level
finiteness and directed continuity.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR

universe u

namespace Dir

 theorem finite_sup_mem {α : Type u} [PartialOrder α] [DComplete α]
    {s : Set α} (hs : Dir s) (hfinite : s.Finite) : dSup s hs ∈ s := by
  classical
  obtain ⟨b, hb, hu⟩ := hs.finite_bound hfinite.toFinset (fun a => a) (by
    intro a ha
    exact hfinite.mem_toFinset.mp ha)
  have he : dSup s hs = b := by
    apply le_antisymm
    · apply dSup_le hs
      intro a ha
      exact hu a (hfinite.mem_toFinset.mpr ha)
    · exact le_dSup hs hb
  simpa only [he] using hb

end Dir

/-- Compactness for nonempty directed sets. -/
def Compact {α : Type u} [PartialOrder α] [DComplete α] (d : α) : Prop :=
  ∀ (s : Set α) (hs : Dir s), d ≤ dSup s hs → ∃ a ∈ s, d ≤ a

 theorem projection_image_finite (τ : Ty) (n : ℕ) (s : Set (D τ)) :
    ((fun a => projection τ n a) '' s).Finite := by
  have hr : (Set.range (fun a : Level τ n => a.val)).Finite := Set.finite_range _
  apply hr.subset
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨⟨projection τ n a, projection_idem τ n a⟩, rfl⟩

 theorem finite_level_compact (τ : Ty) (n : ℕ) (d : D τ)
    (hd : projection τ n d = d) : Compact d := by
  intro s hs hds
  let p : Hom (typeObj τ) (typeObj τ) := projection τ n
  have hpdir : Dir ((fun a => p a) '' s) := hs.image p p.mono
  have hmem : dSup ((fun a => p a) '' s) hpdir ∈ ((fun a => p a) '' s) :=
    hpdir.finite_sup_mem (projection_image_finite τ n s)
  obtain ⟨a, ha, hea⟩ := hmem
  refine ⟨a, ha, ?_⟩
  calc
    d = p d := hd.symm
    _ ≤ p (dSup s hs) := p.mono hds
    _ = dSup ((fun a => p a) '' s) hpdir := p.val.map_dSup s hs
    _ = p a := hea.symm
    _ ≤ a := projection_le τ n a

 theorem projection_compact (τ : Ty) (n : ℕ) (d : D τ) :
    Compact (projection τ n d) :=
  finite_level_compact τ n _ (projection_idem τ n d)

/-- No other compact elements are hidden outside the finite levels. -/
 theorem compact_iff_finite_level (τ : Ty) (d : D τ) :
    Compact d ↔ ∃ n : ℕ, projection τ n d = d := by
  constructor
  · intro hd
    have hsup : d ≤ (projectionChain τ d).sup := (projection_approximates τ d).symm.le
    obtain ⟨a, ⟨n, rfl⟩, hn⟩ := hd (Set.range (projectionChain τ d).at)
      (projectionChain τ d).dir hsup
    exact ⟨n, le_antisymm (projection_le τ n d) hn⟩
  · rintro ⟨n, hn⟩
    exact finite_level_compact τ n d hn

 theorem compact_definability (τ : Ty) (d : D τ) (hd : Compact d) :
    ∃ M : Tm [] τ, denoteClosed M = d := by
  obtain ⟨n, hn⟩ := (compact_iff_finite_level τ d).mp hd
  exact finite_definability τ n d hn

/-- Every element is the supremum of an increasing chain of compact definable elements. -/
 theorem algebraic_definable (τ : Ty) (d : D τ) :
    ∃ c : Chain (D τ), c.sup = d ∧
      ∀ n, Compact (c n) ∧ ∃ M : Tm [] τ, denoteClosed M = c n := by
  refine ⟨projectionChain τ d, projection_approximates τ d, ?_⟩
  intro n
  exact ⟨projection_compact τ n d, approximant_definable τ n d⟩

end OR
