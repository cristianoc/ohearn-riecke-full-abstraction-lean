import OR.Sequential

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section

namespace OR

/--
All small concrete categories of finite arities, equipped with a primitive-closed
Kripke ground relation. `Test : Type 1`; its worlds and each arity are in `Type 0`.
This type is defined before PCF syntax, types, or relational semantic objects.
-/
structure Test where
  World : Type
  El : World → Type
  finite : ∀ w, Finite (El w)
  Hom : {v w : World} → (El v → El w) → Prop
  identity : ∀ w, Hom (fun x : El w => x)
  composition : ∀ {u v w : World} {f : El u → El v} {g : El v → El w},
    Hom f → Hom g → Hom (g ∘ f)
  /-- Paper Definition 3: the ground family is already a complete Kripke relation. -/
  ground : ∀ w, (El w → Ground) → Prop
  ground_bottom : ∀ w, ground w (fun _ => ⊥)
  ground_sup : ∀ w (s : Set (El w → Ground)) (hs : Dir s),
    (∀ g ∈ s, ground w g) → ground w (dSup s hs)
  reindex : ∀ {v w : World} {φ : El v → El w}, Hom φ →
    ∀ g, ground w g → ground v (g ∘ φ)
  /-- Paper Definitions 4--5: every finite-arity component is sequential. -/
  sequential : ∀ w, Sequential (ground w)

attribute [instance] Test.finite

/-- An admissible Kripke relation, not a downward-closed relation. -/
structure KRel (T : Test) (D : Domain) where
  holds : ∀ w : T.World, (T.El w → D) → Prop
  bottom : ∀ w, holds w (fun _ => ⊥)
  sup : ∀ w (s : Set (T.El w → D)) (hs : Dir s),
    (∀ g ∈ s, holds w g) → holds w (dSup s hs)
  reindex : ∀ {v w : T.World} {φ : T.El v → T.El w}, T.Hom φ →
    ∀ g, holds w g → holds v (g ∘ φ)

namespace KRel

/-- Admissibility transported along an arbitrary continuous tuple-valued map. -/
 theorem mapSup {T : Test} {D : Domain} (R : KRel T D)
    {α : Type} [PartialOrder α] [DComplete α]
    (w : T.World) (f : CMap α (T.El w → D))
    (s : Set α) (hs : Dir s) (h : ∀ a ∈ s, R.holds w (f a)) :
    R.holds w (f (dSup s hs)) := by
  rw [f.map_dSup]
  apply R.sup
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

end KRel

 def groundDomain : Domain where
  Carrier := Ground
  po := inferInstance
  ob := inferInstance
  dc := inferInstance

/-- Proposition 6, recovered from the paper-level sequentiality field. -/
 theorem Test.primitive (T : Test) (w : T.World) : PrimitiveClosed (T.ground w) :=
  (sequential_iff_primitive_closed (T.ground w)).mp (T.sequential w)

 def Test.groundRel (T : Test) : KRel T groundDomain where
  holds := T.ground
  bottom := T.ground_bottom
  sup := T.ground_sup
  reindex hφ g hg := T.reindex hφ g hg

end OR
