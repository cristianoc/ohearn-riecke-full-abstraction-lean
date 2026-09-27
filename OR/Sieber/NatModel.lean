import OR.Interpretation
import OR.Sieber.Model

/-!
# The ordinary (single-world) Sieber model of PCF over `ℕ⊥`

This is the model in O'Hearn and Riecke's open question: types denote
directed-complete posets, and an arrow type denotes the continuous maps that
preserve every ordinary sequentiality relation. It differs from the Kripke
model `OR.D` only in the relations: here a relation is indexed by a single
test `(w, d)` (an arity and a finite intersection of Sieber's relations
`S^w_{A,B}`), and there is no reindexing.

The construction mirrors `OR.SR` and `OR.Interpretation`, specialised to
single-world tests.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR.NS

/-- An ordinary test: an arity `w` and a finite set of pairs `(A, B)`, standing for
the intersection of the relations `S^w_{A,B}` with `A ⊆ B`. The same descriptions
are used for the Boolean model. -/
abbrev NTest := Σ w : ℕ, OR.Sieber.Test w

/-- The ground relation of a test on `ℕ⊥`. -/
def gholds (t : NTest) (g : Fin t.1 → Ground) : Prop :=
  ∀ p ∈ t.2, p.1 ⊆ p.2 → Elementary p.1 p.2 g

theorem gholds_prim (t : NTest) : PrimitiveClosed (gholds t) where
  zero := fun _ _ _ => Elementary.constant _ _ _
  succ _ hg := fun p hp hAB => (hg p hp hAB).strict_map Ground.succ rfl
  pred _ hg := fun p hp hAB => (hg p hp hAB).strict_map Ground.pred rfl
  ifz _ _ _ hc ha hb := fun p hp hAB =>
    Elementary.conditional hAB (hc p hp hAB) (ha p hp hAB) (hb p hp hAB)

theorem gholds_sup (t : NTest) (s : Set (Fin t.1 → Ground)) (hs : Dir s)
    (h : ∀ g ∈ s, gholds t g) : gholds t (dSup s hs) :=
  h _ (Stabilizing.sup_mem (α := Fin t.1 → Ground) s hs)

/-- An admissible family of relations, one per ordinary test. -/
structure NRel (D : Domain) where
  holds : ∀ t : NTest, (Fin t.1 → D) → Prop
  bottom : ∀ t, holds t (fun _ => ⊥)
  sup : ∀ t (s : Set (Fin t.1 → D)) (hs : Dir s), (∀ g ∈ s, holds t g) → holds t (dSup s hs)

theorem NRel.mapSup {D : Domain} (R : NRel D) {α : Type} [PartialOrder α] [DComplete α]
    (t : NTest) (f : CMap α (Fin t.1 → D)) (s : Set α) (hs : Dir s)
    (h : ∀ a ∈ s, R.holds t (f a)) : R.holds t (f (dSup s hs)) := by
  rw [f.map_dSup]
  apply R.sup
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

structure Obj where
  domain : Domain
  rel : NRel domain
  concrete : ∀ t (a : domain), rel.holds t (fun _ => a)

instance : CoeSort Obj Type := ⟨fun A => A.domain.Carrier⟩
instance objPartialOrder (A : Obj) : PartialOrder A := A.domain.po
instance objOrderBot (A : Obj) : OrderBot A := A.domain.ob
instance objDComplete (A : Obj) : DComplete A := A.domain.dc

abbrev Obj.R (A : Obj) (t : NTest) (g : Fin t.1 → A) : Prop := A.rel.holds t g

/-- Preservation of every ordinary test. -/
def Uniform (A B : Obj) (f : CMap A B) : Prop :=
  ∀ t (g : Fin t.1 → A), A.R t g → B.R t (fun i => f (g i))

instance uniformSupClosed (A B : Obj) : SupClosed (Uniform A B) where
  closed s hs h t g hg := by
    let e : CMap (CMap A B) (Fin t.1 → B) := CMap.pi (fun i => CMap.applyAt (g i))
    exact B.rel.mapSup t e s hs (fun f hf => h f hf t g hg)

abbrev Hom (A B : Obj) := {f : CMap A B // Uniform A B f}

namespace Hom

variable {A B C : Obj}

instance : CoeFun (Hom A B) (fun _ => A → B) := ⟨fun f => f.val.toFun⟩

@[ext] theorem ext {f g : Hom A B} (h : ∀ a, f a = g a) : f = g := Subtype.ext (CMap.ext h)

@[simp] theorem le_def (f g : Hom A B) : f ≤ g ↔ ∀ a, f a ≤ g a := Iff.rfl

theorem mono (f : Hom A B) : Monotone (fun a => f a) := f.val.mono

theorem uniform (f : Hom A B) (t : NTest) (g : Fin t.1 → A) (hg : A.R t g) :
    B.R t (fun i => f (g i)) := f.property t g hg

def id : Hom A A := ⟨CMap.id, fun _ _ hg => hg⟩

def const (b : B) : Hom A B := ⟨CMap.const b, fun t _ _ => B.concrete t b⟩

def comp (g : Hom B C) (f : Hom A B) : Hom A C :=
  ⟨g.val.comp f.val, fun t a ha => g.uniform t _ (f.uniform t a ha)⟩

instance : OrderBot (Hom A B) where
  bot := const ⊥
  bot_le _ _ := bot_le

@[simp] theorem id_apply (a : A) : (id : Hom A A) a = a := rfl
@[simp] theorem const_apply (b : B) (a : A) : (const b : Hom A B) a = b := rfl
@[simp] theorem comp_apply (g : Hom B C) (f : Hom A B) (a : A) : comp g f a = g (f a) := rfl

def applyAt (a : A) : CMap (Hom A B) B :=
  (CMap.applyAt a).comp (CMap.subtypeVal : CMap (Hom A B) (CMap A B))

@[simp] theorem applyAt_apply (a : A) (f : Hom A B) : applyAt a f = f a := rfl

theorem dSup_apply (s : Set (Hom A B)) (hs : Dir s) (a : A) :
    dSup s hs a = dSup ((fun f : Hom A B => f a) '' s) (hs.image _ (fun _ _ h => h a)) :=
  (applyAt a).map_dSup s hs

theorem chain_sup_apply (c : Chain (Hom A B)) (a : A) :
    c.sup a = (Chain.mk (fun n => c n a) (fun _ _ h => c.mono h a)).sup :=
  c.map_sup (applyAt a)

def evalContinuous : CMap (Hom A B × A) B :=
  CMap.eval.comp (((CMap.subtypeVal : CMap (Hom A B) (CMap A B)).comp CMap.fst).pair CMap.snd)

end Hom

namespace Obj

def one : Obj where
  domain := { Carrier := PUnit, po := inferInstance, ob := inferInstance, dc := inferInstance }
  rel := { holds := fun _ _ => True, bottom := fun _ => trivial, sup := fun _ _ _ _ => trivial }
  concrete := fun _ _ => trivial

def prod (A B : Obj) : Obj where
  domain := { Carrier := A × B, po := inferInstance, ob := inferInstance, dc := inferInstance }
  rel := {
    holds := fun t g => A.R t (fun i => (g i).1) ∧ B.R t (fun i => (g i).2)
    bottom := fun t => ⟨A.rel.bottom t, B.rel.bottom t⟩
    sup := by
      intro t s hs h
      constructor
      · let e : CMap (Fin t.1 → A × B) (Fin t.1 → A) := CMap.pi (fun i => CMap.fst.comp (CMap.proj i))
        exact A.rel.mapSup t e s hs (fun g hg => (h g hg).1)
      · let e : CMap (Fin t.1 → A × B) (Fin t.1 → B) := CMap.pi (fun i => CMap.snd.comp (CMap.proj i))
        exact B.rel.mapSup t e s hs (fun g hg => (h g hg).2) }
  concrete t a := ⟨A.concrete t a.1, B.concrete t a.2⟩

/-- The ordinary logical lift to function spaces. -/
def arr (A B : Obj) : Obj where
  domain := { Carrier := Hom A B, po := inferInstance, ob := inferInstance, dc := inferInstance }
  rel := {
    holds := fun t F => ∀ g : Fin t.1 → A, A.R t g → B.R t (fun i => F i (g i))
    bottom := fun t g _ => B.rel.bottom t
    sup := by
      intro t s hs h g hg
      let e : CMap (Fin t.1 → Hom A B) (Fin t.1 → B) :=
        CMap.pi (fun i => (Hom.applyAt (g i)).comp (CMap.proj i))
      exact B.rel.mapSup t e s hs (fun F hF => h F hF g hg) }
  concrete t f g hg := f.uniform t g hg

instance arrCoeFun (A B : Obj) : CoeFun (arr A B) (fun _ => A → B) :=
  ⟨fun f => (show Hom A B from f).val.toFun⟩

def groundDomain : Domain := OR.groundDomain

def nat : Obj where
  domain := groundDomain
  rel := { holds := gholds, bottom := fun t => (gholds_prim t).bottom, sup := gholds_sup }
  concrete t a := (gholds_prim t).constant a

end Obj

namespace Hom

variable {A B C : Obj}

def fst : Hom (Obj.prod A B) A := ⟨CMap.fst, fun _ _ h => h.1⟩
def snd : Hom (Obj.prod A B) B := ⟨CMap.snd, fun _ _ h => h.2⟩
def pair (f : Hom A B) (g : Hom A C) : Hom A (Obj.prod B C) :=
  ⟨f.val.pair g.val, fun t a ha => ⟨f.uniform t a ha, g.uniform t a ha⟩⟩

def eval : Hom (Obj.prod (Obj.arr A B) A) B :=
  ⟨evalContinuous, fun _ g hg => hg.1 (fun i => (g i).2) hg.2⟩

theorem curry_section_uniform (f : Hom (Obj.prod C A) B) (c : C) :
    Uniform A B (CMap.curry f.val c) :=
  fun t a ha => f.uniform t (fun i => (c, a i)) ⟨C.concrete t c, ha⟩

def curry (f : Hom (Obj.prod C A) B) : Hom C (Obj.arr A B) :=
  ⟨CMap.codRestrict (CMap.curry f.val) (curry_section_uniform f),
    fun t g hg a ha => f.uniform t (fun i => (g i, a i)) ⟨hg, ha⟩⟩

@[simp] theorem fst_apply (p : Obj.prod A B) : (fst : Hom (Obj.prod A B) A) p = p.1 := rfl
@[simp] theorem snd_apply (p : Obj.prod A B) : (snd : Hom (Obj.prod A B) B) p = p.2 := rfl
@[simp] theorem pair_apply (f : Hom A B) (g : Hom A C) (a : A) : pair f g a = (f a, g a) := rfl
@[simp] theorem eval_apply (f : Hom A B) (a : A) : eval (f, a) = f a := rfl
@[simp] theorem curry_apply (f : Hom (Obj.prod C A) B) (c : C) (a : A) : curry f c a = f (c, a) := rfl

def iterMap (A : Obj) : ℕ → Hom (Obj.arr A A) A
  | 0 => const ⊥
  | n + 1 => eval.comp (id.pair (iterMap A n))

theorem iterMap_mono (A : Obj) : Monotone (iterMap A) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => intro f; exact bot_le
  | succ n ih => intro f; exact f.mono (ih f)

def fixMap (A : Obj) : Hom (Obj.arr A A) A := (Chain.mk (iterMap A) (iterMap_mono A)).sup

theorem iterMap_apply (A : Obj) (n : ℕ) (f : Hom A A) : iterMap A n f = iterate f.val n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [iterMap, comp_apply, pair_apply, id_apply, eval_apply, iterate_succ] using congrArg f ih

theorem fixMap_apply (A : Obj) (f : Hom A A) : fixMap A f = lfp f.val := by
  rw [fixMap, chain_sup_apply]
  unfold lfp
  apply congrArg Chain.sup
  apply Chain.ext
  intro n
  exact iterMap_apply A n f

@[simp] theorem fixMap_id (A : Obj) : fixMap A (id : Hom A A) = ⊥ := by
  rw [fixMap_apply]; exact lfp_id

def successor : Hom Obj.nat Obj.nat := ⟨Ground.succMap, fun t g hg => (gholds_prim t).succ g hg⟩
def predecessor : Hom Obj.nat Obj.nat := ⟨Ground.predMap, fun t g hg => (gholds_prim t).pred g hg⟩
def conditional : Hom (Obj.prod Obj.nat (Obj.prod Obj.nat Obj.nat)) Obj.nat :=
  ⟨Ground.ifzMap, fun t _ hg => (gholds_prim t).ifz _ _ _ hg.1 hg.2.1 hg.2.2⟩

end Hom

/-! ## Interpretation of PCF -/

def typeObj : Ty → Obj
  | .nat => Obj.nat
  | .arr σ τ => Obj.arr (typeObj σ) (typeObj τ)

abbrev D (τ : Ty) : Type := (typeObj τ).domain.Carrier

instance dArrCoeFun (σ τ : Ty) : CoeFun (D (σ ⇒ τ)) (fun _ => D σ → D τ) :=
  ⟨fun f => (show Hom (typeObj σ) (typeObj τ) from f).val.toFun⟩

def envObj : Ctx → Obj
  | [] => Obj.one
  | σ :: Γ => Obj.prod (envObj Γ) (typeObj σ)

abbrev Env (Γ : Ctx) : Type := (envObj Γ).domain.Carrier

instance emptyEnvSubsingleton : Subsingleton (Env []) := by
  change Subsingleton PUnit
  infer_instance

def lookup {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Env Γ → D τ :=
  match x with
  | .vz => Prod.snd
  | .vs x => fun ρ => lookup x ρ.1

def lookupHom {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Hom (envObj Γ) (typeObj τ) :=
  match x with
  | .vz => Hom.snd
  | .vs x => (lookupHom x).comp Hom.fst

@[simp] theorem lookupHom_apply {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) :
    lookupHom x ρ = lookup x ρ := by
  induction x with
  | vz => rfl
  | vs x ih => exact ih ρ.1

def envOf : {Γ : Ctx} → (∀ {τ : Ty}, Var Γ τ → D τ) → Env Γ
  | [], _ => PUnit.unit
  | _ :: _, f => (envOf (fun x => f (.vs x)), f .vz)

@[simp] theorem lookup_envOf {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (f : ∀ {τ : Ty}, Var Γ τ → D τ) :
    lookup x (envOf f) = f x := by
  induction x with
  | vz => rfl
  | vs x ih => exact ih (fun x => f (.vs x))

theorem env_ext {Γ : Ctx} {ρ η : Env Γ} (h : ∀ {τ : Ty}, ∀ x : Var Γ τ, lookup x ρ = lookup x η) :
    ρ = η := by
  induction Γ with
  | nil => exact Subsingleton.elim _ _
  | cons σ Γ ih =>
      apply Prod.ext
      · apply ih; intro τ x; exact h (.vs x)
      · exact h .vz

def pull {Γ Δ : Ctx} (r : Ren Γ Δ) (η : Env Δ) : Env Γ := envOf (fun x => lookup (r x) η)

@[simp] theorem lookup_pull {Γ Δ : Ctx} {τ : Ty} (r : Ren Γ Δ) (x : Var Γ τ) (η : Env Δ) :
    lookup x (pull r η) = lookup (r x) η := lookup_envOf x _

@[simp] theorem pull_lift {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (ρ : Env Δ) (a : D σ) :
    pull (Ren.lift r) (ρ, a) = (pull r ρ, a) := by
  apply env_ext
  intro τ x
  rw [lookup_pull]
  cases x <;> simp only [Ren.lift, lookup, lookup_pull]

def denote {Γ : Ctx} {τ : Ty} (M : Tm Γ τ) : Hom (envObj Γ) (typeObj τ) :=
  match M with
  | .var x => lookupHom x
  | .lam M => Hom.curry (denote M)
  | .app M N => Hom.eval.comp ((denote M).pair (denote N))
  | .fix M => (Hom.fixMap _).comp (denote M)
  | .zero => Hom.const (.val 0)
  | .succ M => Hom.successor.comp (denote M)
  | .pred M => Hom.predecessor.comp (denote M)
  | .ifz C M N => Hom.conditional.comp ((denote C).pair ((denote M).pair (denote N)))

abbrev denoteClosed {τ : Ty} (M : Tm [] τ) : D τ := denote M PUnit.unit

@[simp] theorem denote_var {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) :
    denote (.var x) ρ = lookup x ρ := lookupHom_apply x ρ
@[simp] theorem denote_lam {Γ : Ctx} {σ τ : Ty} (M : Tm (σ :: Γ) τ) (ρ : Env Γ) (a : D σ) :
    denote (.lam M) ρ a = denote M (ρ, a) := rfl
@[simp] theorem denote_app {Γ : Ctx} {σ τ : Ty} (M : Tm Γ (σ ⇒ τ)) (N : Tm Γ σ) (ρ : Env Γ) :
    denote (.app M N) ρ = denote M ρ (denote N ρ) := rfl
@[simp] theorem denote_fix {Γ : Ctx} {τ : Ty} (M : Tm Γ (τ ⇒ τ)) (ρ : Env Γ) :
    denote (.fix M) ρ = Hom.fixMap (typeObj τ) (denote M ρ) := rfl
@[simp] theorem denote_zero {Γ : Ctx} (ρ : Env Γ) : denote (Tm.zero : Tm Γ .nat) ρ = .val 0 := rfl
@[simp] theorem denote_succ {Γ : Ctx} (M : Tm Γ .nat) (ρ : Env Γ) :
    denote (.succ M) ρ = Ground.succ (denote M ρ) := rfl
@[simp] theorem denote_pred {Γ : Ctx} (M : Tm Γ .nat) (ρ : Env Γ) :
    denote (.pred M) ρ = Ground.pred (denote M ρ) := rfl
@[simp] theorem denote_ifz {Γ : Ctx} (C M N : Tm Γ .nat) (ρ : Env Γ) :
    denote (.ifz C M N) ρ = Ground.ifz (denote C ρ) (denote M ρ) (denote N ρ) := rfl

theorem denote_rename {Γ Δ : Ctx} {τ : Ty} (M : Tm Γ τ) (r : Ren Γ Δ) (η : Env Δ) :
    denote (Tm.rename r M) η = denote M (pull r η) := by
  induction M generalizing Δ with
  | var x => simp only [Tm.rename, denote_var, lookup_pull]
  | lam M ih =>
      apply Hom.ext
      intro a
      change denote (Tm.rename (Ren.lift r) M) (η, a) = denote M (pull r η, a)
      rw [ih, pull_lift]
  | app M N ihM ihN => simp only [Tm.rename, denote_app, ihM, ihN]
  | fix M ih => simp only [Tm.rename, denote_fix, ih]
  | zero => rfl
  | succ M ih => simp only [Tm.rename, denote_succ, ih]
  | pred M ih => simp only [Tm.rename, denote_pred, ih]
  | ifz C M N ihC ihM ihN => simp only [Tm.rename, denote_ifz, ihC, ihM, ihN]

@[simp] theorem denote_closed {Γ : Ctx} {τ : Ty} (M : Tm [] τ) (ρ : Env Γ) :
    denote (Tm.closed M) ρ = denoteClosed M := by
  rw [Tm.closed, denote_rename]
  exact congrArg (denote M) (Subsingleton.elim _ _)

@[simp] theorem denote_omega {Γ : Ctx} (τ : Ty) (ρ : Env Γ) : denote (Tm.omega τ) ρ = ⊥ := by
  have hid : denote (Tm.lam (Tm.var (Var.vz : Var (τ :: Γ) τ))) ρ =
      (Hom.id : Hom (typeObj τ) (typeObj τ)) := by
    apply Hom.ext; intro a; rfl
  rw [Tm.omega, denote_fix, hid, Hom.fixMap_id]

end OR.NS
