import OR.Worlds

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR

/-- A concrete relational domain. Every carrier element satisfies constant-tuple tests. -/
structure Obj where
  domain : Domain
  rel : ∀ T : Test, KRel T domain
  concrete : ∀ T (w : T.World) (a : domain), (rel T).holds w (fun _ => a)

instance : CoeSort Obj Type := ⟨fun A => A.domain.Carrier⟩
instance objPartialOrder (A : Obj) : PartialOrder A := A.domain.po
instance objOrderBot (A : Obj) : OrderBot A := A.domain.ob
instance objDComplete (A : Obj) : DComplete A := A.domain.dc

abbrev Obj.R (A : Obj) (T : Test) (w : T.World) (g : T.El w → A) : Prop :=
  (A.rel T).holds w g

/-- The universal quantifier over *all* ground tests occurs in the arrow carrier. -/
def Uniform (A B : Obj) (f : CMap A B) : Prop :=
  ∀ T (w : T.World) (g : T.El w → A), A.R T w g → B.R T w (fun i => f (g i))

instance uniformSupClosed (A B : Obj) : SupClosed (Uniform A B) where
  closed s hs h T w g hg := by
    let e : CMap (CMap A B) (T.El w → B) :=
      CMap.pi (fun i => CMap.applyAt (g i))
    exact (B.rel T).mapSup w e s hs (fun f hf => h f hf T w g hg)

/-- Uniform continuous functions, not arbitrary continuous functions. -/
abbrev Hom (A B : Obj) := {f : CMap A B // Uniform A B f}

namespace Hom

variable {A B C D : Obj}

instance : CoeFun (Hom A B) (fun _ => A → B) := ⟨fun f => f.val.toFun⟩

@[ext] theorem ext {f g : Hom A B} (h : ∀ a, f a = g a) : f = g :=
  Subtype.ext (CMap.ext h)

@[simp] theorem le_def (f g : Hom A B) : f ≤ g ↔ ∀ a, f a ≤ g a := Iff.rfl

theorem mono (f : Hom A B) : Monotone (fun a => f a) := f.val.mono

theorem uniform (f : Hom A B) (T : Test) (w : T.World) (g : T.El w → A)
    (hg : A.R T w g) : B.R T w (fun i => f (g i)) := f.property T w g hg

 def id : Hom A A := ⟨CMap.id, fun _ _ _ hg => hg⟩

 def const (b : B) : Hom A B := ⟨CMap.const b, fun T w _ _ => B.concrete T w b⟩

 def comp (g : Hom B C) (f : Hom A B) : Hom A C :=
  ⟨g.val.comp f.val, fun T w a ha => g.uniform T w _ (f.uniform T w a ha)⟩

instance : OrderBot (Hom A B) where
  bot := const ⊥
  bot_le _ _ := bot_le

@[simp] theorem id_apply (a : A) : (id : Hom A A) a = a := rfl
@[simp] theorem const_apply (b : B) (a : A) : (const b : Hom A B) a = b := rfl
@[simp] theorem comp_apply (g : Hom B C) (f : Hom A B) (a : A) :
    comp g f a = g (f a) := rfl
@[simp] theorem bot_apply (a : A) : (⊥ : Hom A B) a = ⊥ := rfl

@[simp] theorem comp_id (f : Hom A B) : f.comp id = f := by ext a; rfl
@[simp] theorem id_comp (f : Hom A B) : id.comp f = f := by ext a; rfl
 theorem comp_assoc (h : Hom C D) (g : Hom B C) (f : Hom A B) :
    h.comp (g.comp f) = (h.comp g).comp f := by ext a; rfl

 def applyAt (a : A) : CMap (Hom A B) B :=
  (CMap.applyAt a).comp (CMap.subtypeVal : CMap (Hom A B) (CMap A B))

@[simp] theorem applyAt_apply (a : A) (f : Hom A B) : applyAt a f = f a := rfl

 theorem dSup_apply (s : Set (Hom A B)) (hs : Dir s) (a : A) :
    dSup s hs a = dSup ((fun f : Hom A B => f a) '' s)
      (hs.image _ (fun _ _ h => h a)) :=
  (applyAt a).map_dSup s hs

 theorem chain_sup_apply (c : Chain (Hom A B)) (a : A) :
    c.sup a = (Chain.mk (fun n => c n a) (fun _ _ h => c.mono h a)).sup :=
  c.map_sup (applyAt a)

 def evalContinuous : CMap (Hom A B × A) B :=
  CMap.eval.comp
    (((CMap.subtypeVal : CMap (Hom A B) (CMap A B)).comp CMap.fst).pair CMap.snd)

end Hom

namespace Obj

 def one : Obj where
  domain := { Carrier := PUnit, po := inferInstance, ob := inferInstance, dc := inferInstance }
  rel T := {
    holds := fun _ _ => True
    bottom := fun _ => True.intro
    sup := fun _ _ _ _ => True.intro
    reindex := fun _ _ _ => True.intro }
  concrete := fun _ _ _ => True.intro

instance oneSubsingleton : Subsingleton one := by
  change Subsingleton PUnit
  infer_instance

 def prod (A B : Obj) : Obj where
  domain := { Carrier := A × B, po := inferInstance, ob := inferInstance, dc := inferInstance }
  rel T := {
    holds := fun w g => A.R T w (fun i => (g i).1) ∧ B.R T w (fun i => (g i).2)
    bottom := fun w => ⟨(A.rel T).bottom w, (B.rel T).bottom w⟩
    sup := by
      intro w s hs h
      constructor
      · let e : CMap (T.El w → A × B) (T.El w → A) :=
          CMap.pi (fun i => CMap.fst.comp (CMap.proj i))
        exact (A.rel T).mapSup w e s hs (fun g hg => (h g hg).1)
      · let e : CMap (T.El w → A × B) (T.El w → B) :=
          CMap.pi (fun i => CMap.snd.comp (CMap.proj i))
        exact (B.rel T).mapSup w e s hs (fun g hg => (h g hg).2)
    reindex := by
      intro v w φ hφ g hg
      exact ⟨(A.rel T).reindex hφ _ hg.1, (B.rel T).reindex hφ _ hg.2⟩ }
  concrete T w a := ⟨A.concrete T w a.1, B.concrete T w a.2⟩

@[simp] theorem prod_related (A B : Obj) (T : Test) (w : T.World)
    (g : T.El w → prod A B) :
    (prod A B).R T w g ↔
      A.R T w (fun i => (g i).1) ∧ B.R T w (fun i => (g i).2) := Iff.rfl

/--
The relation tests every reindexing in the selected test. The carrier is `Hom A B`,
whose elements already preserve every test. The two quantifiers are independent.
-/
 def arr (A B : Obj) : Obj where
  domain := { Carrier := Hom A B, po := inferInstance, ob := inferInstance, dc := inferInstance }
  rel T := {
    holds := fun w g =>
      ∀ (v : T.World) (φ : T.El v → T.El w), T.Hom φ →
        ∀ a : T.El v → A, A.R T v a → B.R T v (fun i => g (φ i) (a i))
    bottom := by
      intro w v φ hφ a ha
      exact (B.rel T).bottom v
    sup := by
      intro w s hs h v φ hφ a ha
      let e : CMap (T.El w → Hom A B) (T.El v → B) :=
        CMap.pi (fun i => (Hom.applyAt (a i)).comp (CMap.proj (φ i)))
      exact (B.rel T).mapSup v e s hs (fun g hg => h g hg v φ hφ a ha)
    reindex := by
      intro u w θ hθ g hg v φ hφ a ha
      exact hg v (θ ∘ φ) (T.composition hφ hθ) a ha }
  concrete T w f v φ hφ a ha := f.uniform T v a ha

/-- Expose application without unfolding the relational object indices of `Hom`. -/
instance arrCoeFun (A B : Obj) : CoeFun (arr A B) (fun _ => A → B) :=
  ⟨fun f => (show Hom A B from f).val.toFun⟩

@[simp] theorem arr_related (A B : Obj) (T : Test) (w : T.World)
    (g : T.El w → arr A B) :
    (arr A B).R T w g ↔
      ∀ (v : T.World) (φ : T.El v → T.El w), T.Hom φ →
        ∀ a : T.El v → A, A.R T v a → B.R T v (fun i => g (φ i) (a i)) := Iff.rfl

 def nat : Obj where
  domain := groundDomain
  rel := Test.groundRel
  concrete T w a := (T.primitive w).constant a

@[simp] theorem nat_related (T : Test) (w : T.World) (g : T.El w → nat) :
    nat.R T w g ↔ T.ground w g := Iff.rfl

end Obj

namespace Hom

variable {A B C D : Obj}

 def fst : Hom (Obj.prod A B) A :=
  ⟨CMap.fst, fun _ _ _ h => h.1⟩

 def snd : Hom (Obj.prod A B) B :=
  ⟨CMap.snd, fun _ _ _ h => h.2⟩

 def pair (f : Hom A B) (g : Hom A C) : Hom A (Obj.prod B C) :=
  ⟨f.val.pair g.val, fun T w a ha => ⟨f.uniform T w a ha, g.uniform T w a ha⟩⟩

 def terminal : Hom A Obj.one := const PUnit.unit

@[simp] theorem fst_apply (p : Obj.prod A B) : (fst : Hom (Obj.prod A B) A) p = p.1 := rfl
@[simp] theorem snd_apply (p : Obj.prod A B) : (snd : Hom (Obj.prod A B) B) p = p.2 := rfl
@[simp] theorem pair_apply (f : Hom A B) (g : Hom A C) (a : A) :
    pair f g a = (f a, g a) := rfl
@[simp] theorem fst_pair (f : Hom A B) (g : Hom A C) : fst.comp (pair f g) = f := by ext a; rfl
@[simp] theorem snd_pair (f : Hom A B) (g : Hom A C) : snd.comp (pair f g) = g := by ext a; rfl
@[simp] theorem pair_eta (f : Hom A (Obj.prod B C)) : pair (fst.comp f) (snd.comp f) = f := by
  apply Hom.ext
  intro a
  rfl
 theorem terminal_unique (f g : Hom A Obj.one) : f = g := by
  apply Hom.ext
  intro a
  exact Subsingleton.elim _ _

 def eval : Hom (Obj.prod (Obj.arr A B) A) B :=
  ⟨evalContinuous, by
    intro T w g hg
    exact hg.1 w (fun i => i) (T.identity w) (fun i => (g i).2) hg.2⟩

 theorem curry_section_uniform (f : Hom (Obj.prod C A) B) (c : C) :
    Uniform A B (CMap.curry f.val c) := by
  intro T w a ha
  exact f.uniform T w (fun i => (c, a i)) ⟨C.concrete T w c, ha⟩

 def curry (f : Hom (Obj.prod C A) B) : Hom C (Obj.arr A B) :=
  ⟨CMap.codRestrict (CMap.curry f.val) (curry_section_uniform f), by
    intro T w g hg v φ hφ a ha
    exact f.uniform T v (fun i => (g (φ i), a i))
      ⟨(C.rel T).reindex hφ g hg, ha⟩⟩

 def uncurry (f : Hom C (Obj.arr A B)) : Hom (Obj.prod C A) B :=
  eval.comp ((f.comp fst).pair snd)

@[simp] theorem eval_apply (f : Hom A B) (a : A) : eval (f, a) = f a := rfl
@[simp] theorem curry_apply (f : Hom (Obj.prod C A) B) (c : C) (a : A) :
    curry f c a = f (c, a) := rfl
@[simp] theorem uncurry_apply (f : Hom C (Obj.arr A B)) (c : C) (a : A) :
    uncurry f (c, a) = f c a := rfl
@[simp] theorem uncurry_curry (f : Hom (Obj.prod C A) B) : uncurry (curry f) = f := by
  ext p
  rfl
@[simp] theorem curry_uncurry (f : Hom C (Obj.arr A B)) : curry (uncurry f) = f := by
  ext c a
  rfl

 theorem curry_mono {f g : Hom (Obj.prod C A) B} (h : f ≤ g) : curry f ≤ curry g :=
  fun c a => h (c, a)

 theorem uncurry_mono {f g : Hom C (Obj.arr A B)} (h : f ≤ g) : uncurry f ≤ uncurry g :=
  fun p => h p.1 p.2

/-- Exponentiation on arrows, constructed through evaluation and currying. -/
 def expMap (h : Hom A B) (g : Hom C D) : Hom (Obj.arr B C) (Obj.arr A D) :=
  curry (g.comp (eval.comp (fst.pair (h.comp snd))))

@[simp] theorem expMap_apply (h : Hom A B) (g : Hom C D) (k : Hom B C) (a : A) :
    expMap h g k a = g (k (h a)) := rfl

 theorem global_element (a : A) : ∃ f : Hom Obj.one A, f PUnit.unit = a :=
  ⟨const a, rfl⟩

 theorem le_iff_global (f g : Hom A B) :
    f ≤ g ↔ ∀ e : Hom Obj.one A, f.comp e ≤ g.comp e := by
  constructor
  · intro h e u
    exact h (e u)
  · intro h a
    exact h (const a) PUnit.unit

/-- Uniform iteration maps; their supremum supplies a uniform fixed-point operator. -/
 def iterMap (A : Obj) : ℕ → Hom (Obj.arr A A) A
  | 0 => const ⊥
  | n + 1 => eval.comp (id.pair (iterMap A n))

 theorem iterMap_mono (A : Obj) : Monotone (iterMap A) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => intro f; exact bot_le
  | succ n ih => intro f; exact f.mono (ih f)

 def fixMap (A : Obj) : Hom (Obj.arr A A) A :=
  (Chain.mk (iterMap A) (iterMap_mono A)).sup

 theorem iterMap_apply (A : Obj) (n : ℕ) (f : Hom A A) :
    iterMap A n f = iterate f.val n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterMap, comp_apply, pair_apply, id_apply, eval_apply, iterate_succ] using congrArg f ih

 theorem fixMap_apply (A : Obj) (f : Hom A A) : fixMap A f = lfp f.val := by
  rw [fixMap, chain_sup_apply]
  unfold lfp
  apply congrArg Chain.sup
  apply Chain.ext
  intro n
  exact iterMap_apply A n f

 theorem fixMap_unfold (A : Obj) (f : Hom A A) : f (fixMap A f) = fixMap A f := by
  rw [fixMap_apply]
  exact lfp_unfold f.val

 theorem fixMap_le (A : Obj) (f : Hom A A) {a : A} (ha : f a ≤ a) : fixMap A f ≤ a := by
  rw [fixMap_apply]
  exact lfp_le f.val ha

@[simp] theorem fixMap_id (A : Obj) : fixMap A (id : Hom A A) = ⊥ := by
  rw [fixMap_apply]
  exact lfp_id

 def successor : Hom Obj.nat Obj.nat :=
  ⟨Ground.succMap, fun T w g hg => (T.primitive w).succ g hg⟩

 def predecessor : Hom Obj.nat Obj.nat :=
  ⟨Ground.predMap, fun T w g hg => (T.primitive w).pred g hg⟩

 def conditional : Hom (Obj.prod Obj.nat (Obj.prod Obj.nat Obj.nat)) Obj.nat :=
  ⟨Ground.ifzMap, fun T w g hg =>
    (T.primitive w).ifz _ _ _ hg.1 hg.2.1 hg.2.2⟩

@[simp] theorem successor_apply (d : Ground) : successor d = Ground.succ d := rfl
@[simp] theorem predecessor_apply (d : Ground) : predecessor d = Ground.pred d := rfl
@[simp] theorem conditional_apply (c a b : Ground) : conditional (c, a, b) = Ground.ifz c a b := rfl

end Hom

end OR
