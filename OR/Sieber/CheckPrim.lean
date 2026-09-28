import OR.Sieber.Check
import OR.Sieber.TypeCheck
import OR.Sieber.PrimrecLib

/-!
# The checker is primitive recursive

Every function of the certificate checker, and of the typing checker, is
primitive recursive in Mathlib's sense. The proofs are compositions of
Mathlib's `Primrec` combinators and those of `PrimrecLib`.
-/

set_option autoImplicit false

namespace OR.Sieber.Check

open Primrec OR.Sieber.Prim

theorem dom_prim : Primrec dom :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

theorem cod_prim : Primrec cod :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

theorem arrow_prim : Primrec₂ arrow :=
  (Primrec.succ.comp Primrec₂.natPair).of_eq fun _ => rfl

theorem tabs_prim : Primrec₂ tabs :=
  (lookupD (f := fun p : List TyTab × ℕ => p.1) (g := fun p => p.2) Primrec.fst Primrec.snd).of_eq
    fun _ => rfl

theorem size_prim : Primrec₂ size := by
  classical
  refine (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 3)
    (Primrec.list_length.comp tabs_prim)).of_eq fun p => ?_
  rfl

theorem app_prim : Primrec fun x : List TyTab × ℕ × ℕ × ℕ => app x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (Primrec.list_getD 0).comp
    ((Primrec.list_getD []).comp (tabs_prim.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

/-- `tuples` by `Nat.rec`. -/
theorem tuples_eq (n w : ℕ) :
    tuples n w = Nat.rec [[]] (fun _ acc => acc.flatMap fun t => (List.range n).map (· :: t)) w := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [tuples, ih]

theorem tuples_prim : Primrec₂ tuples := by
  have := Primrec.nat_rec (f := fun _ : ℕ => ([[]] : List (List ℕ)))
    (g := fun n (p : ℕ × List (List ℕ)) => p.2.flatMap fun t => (List.range n).map (· :: t))
    (Primrec.const _)
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂
  exact this.of_eq fun n w => (tuples_eq n w).symm


abbrev TestL := List (List ℕ × List ℕ)

theorem holds_prim : Primrec₂ holds := by
  -- y : (TestL × List ℕ) × (List ℕ × List ℕ)
  have hA : Primrec fun y : (TestL × List ℕ) × (List ℕ × List ℕ) => y.2.1.all fun i => y.2.2.contains i :=
    list_all (Primrec.fst.comp Primrec.snd)
      (list_contains (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  have hB : Primrec fun y : (TestL × List ℕ) × (List ℕ × List ℕ) => y.2.1.any fun i => y.1.2.getD i 0 == 0 :=
    list_any (Primrec.fst.comp Primrec.snd)
      (beq'.comp ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.const 0)).to₂
  have hC : Primrec fun y : (TestL × List ℕ) × (List ℕ × List ℕ) =>
      y.2.2.all fun i => y.2.2.all fun j => y.1.2.getD i 0 == y.1.2.getD j 0 :=
    list_all (Primrec.snd.comp Primrec.snd)
      (list_all (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (beq'.comp
          ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp Primrec.fst))
          ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            Primrec.snd)).to₂).to₂
  exact (list_all (f := fun x : TestL × List ℕ => x.1) Primrec.fst
    (Primrec.or.comp (Primrec.or.comp (Primrec.not.comp hA) hB) hC).to₂).of_eq fun _ => rfl

theorem liftSet_prim : Primrec₂ liftSet :=
  (lookupD (f := fun p : List Lift × ℕ => p.1) (g := fun p => p.2) Primrec.fst Primrec.snd).of_eq
    fun _ => rfl

theorem hasLift_prim : Primrec₂ hasLift :=
  (list_any (f := fun p : List Lift × ℕ => p.1) Primrec.fst
    (beq'.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂).of_eq fun _ => rfl

theorem appTuple_prim :
    Primrec fun x : List TyTab × ℕ × ℕ × List ℕ × List ℕ => appTuple x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  refine (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))
    (app_prim.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.pair
          ((Primrec.list_getD 0).comp
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) Primrec.snd)
          ((Primrec.list_getD 0).comp
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) Primrec.snd))))).to₂)
    |>.of_eq fun _ => rfl

/-- Arguments of `cond`: `(tys, w, d, lifts, c, u)`. -/
abbrev CondArgs := List TyTab × ℕ × TestL × List Lift × ℕ × List ℕ

theorem cond_prim : Primrec fun x : CondArgs => cond x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 := by
  classical
  have hc : Primrec fun x : CondArgs => x.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hu : Primrec fun x : CondArgs => x.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hl : Primrec fun x : CondArgs => x.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec fun x : CondArgs => x.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hw : Primrec fun x : CondArgs => x.2.1 := Primrec.fst.comp Primrec.snd
  have htys : Primrec fun x : CondArgs => x.1 := Primrec.fst
  have hall : Primrec fun x : CondArgs =>
      (liftSet x.2.2.2.1 (dom x.2.2.2.2.1)).all fun h =>
        (liftSet x.2.2.2.1 (cod x.2.2.2.2.1)).contains (appTuple x.1 x.2.1 x.2.2.2.2.1 x.2.2.2.2.2 h) :=
    list_all (liftSet_prim.comp hl (dom_prim.comp hc))
      (list_contains (liftSet_prim.comp (hl.comp Primrec.fst) (cod_prim.comp (hc.comp Primrec.fst)))
        (appTuple_prim.comp (Primrec.pair (htys.comp Primrec.fst) (Primrec.pair (hw.comp Primrec.fst)
          (Primrec.pair (hc.comp Primrec.fst) (Primrec.pair (hu.comp Primrec.fst) Primrec.snd)))))).to₂
  exact (Primrec.ite (Primrec.eq.comp hc (Primrec.const 0)) (holds_prim.comp hd hu) hall).of_eq
    fun _ => rfl


theorem negValid_prim : Primrec₂ negValid := by
  -- x : List TyTab × Neg, with Neg = (c, t, w, d, g, lifts)
  have htys : Primrec fun x : List TyTab × Neg => x.1 := Primrec.fst
  have hc : Primrec fun x : List TyTab × Neg => x.2.1 := Primrec.fst.comp Primrec.snd
  have ht : Primrec fun x : List TyTab × Neg => x.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hw : Primrec fun x : List TyTab × Neg => x.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec fun x : List TyTab × Neg => x.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hg : Primrec fun x : List TyTab × Neg => x.2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hl : Primrec fun x : List TyTab × Neg => x.2.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have h1 : Primrec fun x : List TyTab × Neg =>
      x.2.2.2.2.1.all fun p => (p.1.all (· < x.2.2.2.1)) && (p.2.all (· < x.2.2.2.1)) :=
    list_all hd (Primrec.and.comp
      (list_all (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_lt.comp Primrec.snd (hw.comp (Primrec.fst.comp Primrec.fst))).to₂)
      (list_all (Primrec.snd.comp Primrec.snd)
        (Primrec.nat_lt.comp Primrec.snd (hw.comp (Primrec.fst.comp Primrec.fst))).to₂)).to₂
  have h2 : Primrec fun x : List TyTab × Neg => hasLift x.2.2.2.2.2.2 (dom x.2.1) :=
    hasLift_prim.comp hl (dom_prim.comp hc)
  have h3 : Primrec fun x : List TyTab × Neg => hasLift x.2.2.2.2.2.2 (cod x.2.1) :=
    hasLift_prim.comp hl (cod_prim.comp hc)
  have h4 : Primrec fun x : List TyTab × Neg => x.2.2.2.2.2.2.all fun e =>
      e.1 == 0 || (hasLift x.2.2.2.2.2.2 (dom e.1) && hasLift x.2.2.2.2.2.2 (cod e.1)) :=
    list_all hl (Primrec.or.comp (beq'.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
      (Primrec.and.comp (hasLift_prim.comp (hl.comp Primrec.fst) (dom_prim.comp (Primrec.fst.comp Primrec.snd)))
        (hasLift_prim.comp (hl.comp Primrec.fst) (cod_prim.comp (Primrec.fst.comp Primrec.snd))))).to₂
  have h5 : Primrec fun x : List TyTab × Neg => x.2.2.2.2.2.2.all fun e =>
      e.2.all fun u => (tuples (size x.1 e.1) x.2.2.2.1).contains u :=
    list_all hl (list_all (Primrec.snd.comp Primrec.snd)
      (list_contains (tuples_prim.comp (size_prim.comp (htys.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) (hw.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd).to₂).to₂
  have h6 : Primrec fun x : List TyTab × Neg => x.2.2.2.2.2.2.all fun e =>
      (tuples (size x.1 e.1) x.2.2.2.1).all fun u =>
        e.2.contains u == cond x.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.2 e.1 u :=
    list_all hl (list_all (tuples_prim.comp (size_prim.comp (htys.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)) (hw.comp Primrec.fst))
      (beq'.comp (list_contains (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        (cond_prim.comp (Primrec.pair (htys.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (hw.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.pair (hd.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.pair (hl.comp (Primrec.fst.comp Primrec.fst))
                (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))))))).to₂).to₂
  have h7 : Primrec fun x : List TyTab × Neg => (tuples (size x.1 (dom x.2.1)) x.2.2.2.1).contains x.2.2.2.2.2.1 :=
    list_contains (tuples_prim.comp (size_prim.comp htys (dom_prim.comp hc)) hw) hg
  have h8 : Primrec fun x : List TyTab × Neg => (liftSet x.2.2.2.2.2.2 (dom x.2.1)).contains x.2.2.2.2.2.1 :=
    list_contains (liftSet_prim.comp hl (dom_prim.comp hc)) hg
  have h9 : Primrec fun x : List TyTab × Neg =>
      (liftSet x.2.2.2.2.2.2 (cod x.2.1)).contains (x.2.2.2.2.2.1.map fun gi => x.2.2.1.getD gi 0) :=
    list_contains (liftSet_prim.comp hl (cod_prim.comp hc))
      (Primrec.list_map hg ((Primrec.list_getD 0).comp (ht.comp Primrec.fst) Primrec.snd).to₂)
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp h1 h2) h3) h4) h5) h6) h7) h8)
    (Primrec.not.comp h9)).of_eq fun _ => rfl


/-! ## Entries -/

/-- The part of `entryOK` common to all constructors. -/
def entryGen (tys : List TyTab) (e : Entry) : Bool :=
  (e.2.2.1.length == e.1.length) &&
  ((List.range e.1.length).all fun k => decide (e.2.2.1.getD k 0 < size tys (e.1.getD k 0))) &&
  decide (e.2.2.2.2.1 < size tys e.2.2.2.1) &&
  (e.2.2.2.2.2 == 0 || (decide (e.2.2.2.1 < e.2.2.2.2.2) && e.1.all fun c => decide (c < e.2.2.2.2.2)))

def entryVar (e : Entry) : Bool :=
  decide (e.2.1 / 7 < e.1.length) && e.2.2.2.1 == e.1.getD (e.2.1 / 7) 0 &&
    e.2.2.2.2.1 == e.2.2.1.getD (e.2.1 / 7) 0

def entryLam (tys : List TyTab) (trace : List Entry) (e : Entry) : Bool :=
  e.2.2.2.1 != 0 && dom e.2.2.2.1 == (Nat.unpair (e.2.1 / 7)).1 &&
  (List.range (size tys (Nat.unpair (e.2.1 / 7)).1)).all fun a =>
    trace.any fun e' => e' == ((Nat.unpair (e.2.1 / 7)).1 :: e.1, (Nat.unpair (e.2.1 / 7)).2, a :: e.2.2.1,
      cod e.2.2.2.1, ((tabs tys e.2.2.2.1).getD e.2.2.2.2.1 []).getD a 0, e.2.2.2.2.2)

/-- The match on an entry's shape: `e'` has context, term, environment and level `(ctx, m, env, β)`. -/
def sameSlot (e' : Entry) (ctx : List ℕ) (m : ℕ) (env : List ℕ) (β : ℕ) : Bool :=
  e'.1 == ctx && e'.2.1 == m && e'.2.2.1 == env && e'.2.2.2.2.2 == β

def entryApp (tys : List TyTab) (trace : List Entry) (e : Entry) : Bool :=
  trace.any fun e₁ => sameSlot e₁ e.1 (Nat.unpair (Nat.unpair (e.2.1 / 7)).2).1 e.2.2.1 e.2.2.2.2.2 &&
    (e₁.2.2.2.1 == arrow (Nat.unpair (e.2.1 / 7)).1 e.2.2.2.1 &&
      trace.any fun e₂ => sameSlot e₂ e.1 (Nat.unpair (Nat.unpair (e.2.1 / 7)).2).2 e.2.2.1 e.2.2.2.2.2 &&
        (e₂.2.2.2.1 == (Nat.unpair (e.2.1 / 7)).1 && e.2.2.2.2.1 == app tys e₁.2.2.2.1 e₁.2.2.2.2.1 e₂.2.2.2.2.1))

def entryConst (k : ℕ) (e : Entry) : Bool := e.2.1 / 7 == 0 && e.2.2.2.1 == 0 && e.2.2.2.2.1 == k

def entryIte (trace : List Entry) (e : Entry) : Bool :=
  e.2.2.2.1 == 0 &&
  trace.any fun e₀ => sameSlot e₀ e.1 (Nat.unpair (e.2.1 / 7)).1 e.2.2.1 e.2.2.2.2.2 && (e₀.2.2.2.1 == 0 &&
    trace.any fun e₁ => sameSlot e₁ e.1 (Nat.unpair (Nat.unpair (e.2.1 / 7)).2).1 e.2.2.1 e.2.2.2.2.2 &&
      (e₁.2.2.2.1 == 0 &&
      trace.any fun e₂ => sameSlot e₂ e.1 (Nat.unpair (Nat.unpair (e.2.1 / 7)).2).2 e.2.2.1 e.2.2.2.2.2 &&
        (e₂.2.2.2.1 == 0 && e.2.2.2.2.1 == ite e₀.2.2.2.2.1 e₁.2.2.2.2.1 e₂.2.2.2.2.1)))

def entryOK' (tys : List TyTab) (trace : List Entry) (e : Entry) : Bool :=
  entryGen tys e &&
    if e.2.1 % 7 = 0 then entryVar e
    else if e.2.1 % 7 = 1 then entryLam tys trace e
    else if e.2.1 % 7 = 2 then entryApp tys trace e
    else if e.2.1 % 7 = 3 then entryConst 1 e
    else if e.2.1 % 7 = 4 then entryConst 2 e
    else if e.2.1 % 7 = 5 then entryConst 0 e
    else entryIte trace e

theorem entryOK_eq (tys : List TyTab) (trace : List Entry) (e : Entry) :
    entryOK tys trace e = entryOK' tys trace e := by
  obtain ⟨ctx, m, env, τ, v, β⟩ := e
  have hr : m % 7 < 7 := Nat.mod_lt _ (by norm_num)
  simp only [entryOK, entryOK', entryGen]
  interval_cases hmod : m % 7 <;> rfl


/-! ### Projections of entries -/

section Proj
variable {X : Type} [Primcodable X] {f : X → Entry} (hf : Primrec f)
include hf

theorem pctx : Primrec fun x => (f x).1 := Primrec.fst.comp hf
theorem pm : Primrec fun x => (f x).2.1 := Primrec.fst.comp (Primrec.snd.comp hf)
theorem penv : Primrec fun x => (f x).2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hf))
theorem pτ : Primrec fun x => (f x).2.2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf)))
theorem pv : Primrec fun x => (f x).2.2.2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf))))
theorem pβ : Primrec fun x => (f x).2.2.2.2.2 :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf))))
theorem pq : Primrec fun x => (f x).2.1 / 7 := Primrec.nat_div.comp (pm hf) (Primrec.const 7)
theorem pq1 : Primrec fun x => (Nat.unpair ((f x).2.1 / 7)).1 := Primrec.fst.comp (Primrec.unpair.comp (pq hf))
theorem pq2 : Primrec fun x => (Nat.unpair ((f x).2.1 / 7)).2 := Primrec.snd.comp (Primrec.unpair.comp (pq hf))
theorem pq21 : Primrec fun x => (Nat.unpair (Nat.unpair ((f x).2.1 / 7)).2).1 :=
  Primrec.fst.comp (Primrec.unpair.comp (pq2 hf))
theorem pq22 : Primrec fun x => (Nat.unpair (Nat.unpair ((f x).2.1 / 7)).2).2 :=
  Primrec.snd.comp (Primrec.unpair.comp (pq2 hf))

end Proj

theorem mkEntry {X : Type} [Primcodable X] {a : X → List ℕ} {b : X → ℕ} {c : X → List ℕ} {d e g : X → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) (hd : Primrec d) (he : Primrec e) (hg : Primrec g) :
    Primrec fun x => ((a x, b x, c x, d x, e x, g x) : Entry) :=
  Primrec.pair ha (Primrec.pair hb (Primrec.pair hc (Primrec.pair hd (Primrec.pair he hg))))

theorem sameSlot_prim {X : Type} [Primcodable X] {e : X → Entry} {ctx : X → List ℕ} {m : X → ℕ}
    {env : X → List ℕ} {β : X → ℕ} (he : Primrec e) (hctx : Primrec ctx) (hm : Primrec m)
    (henv : Primrec env) (hβ : Primrec β) :
    Primrec fun x => sameSlot (e x) (ctx x) (m x) (env x) (β x) :=
  Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (beq'.comp (pctx he) hctx) (beq'.comp (pm he) hm))
    (beq'.comp (penv he) henv)) (beq'.comp (pβ he) hβ)

theorem entryGen_prim : Primrec₂ entryGen := by
  have E : Primrec fun x : List TyTab × Entry => x.2 := Primrec.snd
  have T : Primrec fun x : List TyTab × Entry => x.1 := Primrec.fst
  refine (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (beq'.comp (Primrec.list_length.comp (penv E)) (Primrec.list_length.comp (pctx E)))
    (list_all (Primrec.list_range.comp (Primrec.list_length.comp (pctx E)))
      (Primrec.nat_lt.comp ((Primrec.list_getD 0).comp (penv (E.comp Primrec.fst)) Primrec.snd)
        (size_prim.comp (T.comp Primrec.fst) ((Primrec.list_getD 0).comp (pctx (E.comp Primrec.fst))
          Primrec.snd))).to₂))
    (Primrec.nat_lt.comp (pv E) (size_prim.comp T (pτ E))))
    (Primrec.or.comp (beq'.comp (pβ E) (Primrec.const 0))
      (Primrec.and.comp (Primrec.nat_lt.comp (pτ E) (pβ E))
        (list_all (pctx E) (Primrec.nat_lt.comp Primrec.snd (pβ (E.comp Primrec.fst))).to₂)))).of_eq
    fun _ => rfl

theorem entryVar_prim : Primrec entryVar := by
  have E : Primrec fun e : Entry => e := Primrec.id
  exact (Primrec.and.comp (Primrec.and.comp
    (Primrec.nat_lt.comp (pq E) (Primrec.list_length.comp (pctx E)))
    (beq'.comp (pτ E) ((Primrec.list_getD 0).comp (pctx E) (pq E))))
    (beq'.comp (pv E) ((Primrec.list_getD 0).comp (penv E) (pq E)))).of_eq fun _ => rfl

theorem entryConst_prim : Primrec₂ entryConst := by
  have E : Primrec fun x : ℕ × Entry => x.2 := Primrec.snd
  exact (Primrec.and.comp (Primrec.and.comp (beq'.comp (pq E) (Primrec.const 0))
    (beq'.comp (pτ E) (Primrec.const 0))) (beq'.comp (pv E) Primrec.fst)).of_eq fun _ => rfl


abbrev EA := (List TyTab × List Entry) × Entry

theorem entryLam_prim : Primrec fun x : EA => entryLam x.1.1 x.1.2 x.2 := by
  have E : Primrec fun x : EA => x.2 := Primrec.snd
  have TY : Primrec fun x : EA => x.1.1 := Primrec.fst.comp Primrec.fst
  have TR : Primrec fun x : EA => x.1.2 := Primrec.snd.comp Primrec.fst
  -- y : EA × ℕ  (the index a);  z : (EA × ℕ) × Entry
  have hY : Primrec fun y : EA × ℕ => y.1 := Primrec.fst
  have tuple : Primrec fun y : EA × ℕ => (((Nat.unpair (y.1.2.2.1 / 7)).1 :: y.1.2.1,
      (Nat.unpair (y.1.2.2.1 / 7)).2, y.2 :: y.1.2.2.2.1, cod y.1.2.2.2.2.1,
      ((tabs y.1.1.1 y.1.2.2.2.2.1).getD y.1.2.2.2.2.2.1 []).getD y.2 0, y.1.2.2.2.2.2.2) : Entry) :=
    mkEntry (Primrec.list_cons.comp (pq1 (E.comp hY)) (pctx (E.comp hY))) (pq2 (E.comp hY))
      (Primrec.list_cons.comp Primrec.snd (penv (E.comp hY))) (cod_prim.comp (pτ (E.comp hY)))
      ((Primrec.list_getD 0).comp ((Primrec.list_getD []).comp (tabs_prim.comp (TY.comp hY) (pτ (E.comp hY)))
        (pv (E.comp hY))) Primrec.snd)
      (pβ (E.comp hY))
  have hall : Primrec fun x : EA => (List.range (size x.1.1 (Nat.unpair (x.2.2.1 / 7)).1)).all fun a =>
      x.1.2.any fun e' => e' == (((Nat.unpair (x.2.2.1 / 7)).1 :: x.2.1, (Nat.unpair (x.2.2.1 / 7)).2,
        a :: x.2.2.2.1, cod x.2.2.2.2.1, ((tabs x.1.1 x.2.2.2.2.1).getD x.2.2.2.2.2.1 []).getD a 0,
        x.2.2.2.2.2.2) : Entry) :=
    list_all (Primrec.list_range.comp (size_prim.comp TY (pq1 E)))
      (list_any (TR.comp hY) (beq'.comp Primrec.snd (tuple.comp Primrec.fst)).to₂).to₂
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.not.comp (beq'.comp (pτ E) (Primrec.const 0)))
    (beq'.comp (dom_prim.comp (pτ E)) (pq1 E))) hall).of_eq fun _ => rfl

theorem entryApp_prim : Primrec fun x : EA => entryApp x.1.1 x.1.2 x.2 := by
  have E : Primrec fun x : EA => x.2 := Primrec.snd
  have TY : Primrec fun x : EA => x.1.1 := Primrec.fst.comp Primrec.fst
  have TR : Primrec fun x : EA => x.1.2 := Primrec.snd.comp Primrec.fst
  -- y : EA × Entry (e₁);  z : (EA × Entry) × Entry (e₂)
  have y1 : Primrec fun y : EA × Entry => y.1 := Primrec.fst
  have z1 : Primrec fun z : (EA × Entry) × Entry => z.1.1 := Primrec.fst.comp Primrec.fst
  have z2 : Primrec fun z : (EA × Entry) × Entry => z.1.2 := Primrec.snd.comp Primrec.fst
  have inner : Primrec fun y : EA × Entry => y.1.1.2.any fun e₂ =>
      sameSlot e₂ y.1.2.1 (Nat.unpair (Nat.unpair (y.1.2.2.1 / 7)).2).2 y.1.2.2.2.1 y.1.2.2.2.2.2.2 &&
        (e₂.2.2.2.1 == (Nat.unpair (y.1.2.2.1 / 7)).1 &&
          y.1.2.2.2.2.2.1 == app y.1.1.1 y.2.2.2.2.1 y.2.2.2.2.2.1 e₂.2.2.2.2.1) :=
    list_any (TR.comp y1)
      (Primrec.and.comp
        (sameSlot_prim Primrec.snd (pctx (E.comp z1)) (pq22 (E.comp z1)) (penv (E.comp z1)) (pβ (E.comp z1)))
        (Primrec.and.comp (beq'.comp (pτ Primrec.snd) (pq1 (E.comp z1)))
          (beq'.comp (pv (E.comp z1)) (app_prim.comp (Primrec.pair (TY.comp z1)
            (Primrec.pair (pτ z2) (Primrec.pair (pv z2) (pv Primrec.snd)))))))).to₂
  exact (list_any TR (Primrec.and.comp
    (sameSlot_prim Primrec.snd (pctx (E.comp y1)) (pq21 (E.comp y1)) (penv (E.comp y1)) (pβ (E.comp y1)))
    (Primrec.and.comp (beq'.comp (pτ Primrec.snd) (arrow_prim.comp (pq1 (E.comp y1)) (pτ (E.comp y1))))
      inner)).to₂).of_eq fun _ => rfl

theorem ite_prim : Primrec fun x : ℕ × ℕ × ℕ => ite x.1 x.2.1 x.2.2 := by
  classical
  exact (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) (Primrec.fst.comp Primrec.snd)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2)) (Primrec.snd.comp Primrec.snd)
      (Primrec.const 0))).of_eq fun _ => rfl

theorem entryIte_prim : Primrec₂ entryIte := by
  -- x : List Entry × Entry; y : x × e₀; z : y × e₁; u : z × e₂
  have E : Primrec fun x : List Entry × Entry => x.2 := Primrec.snd
  have TR : Primrec fun x : List Entry × Entry => x.1 := Primrec.fst
  have Ey : Primrec fun y : (List Entry × Entry) × Entry => y.1.2 := E.comp Primrec.fst
  have Ez : Primrec fun z : ((List Entry × Entry) × Entry) × Entry => z.1.1.2 := Ey.comp Primrec.fst
  have Eu : Primrec fun u : (((List Entry × Entry) × Entry) × Entry) × Entry => u.1.1.1.2 := Ez.comp Primrec.fst
  have lvl3 : Primrec fun z : ((List Entry × Entry) × Entry) × Entry => z.1.1.1.any fun e₂ =>
      sameSlot e₂ z.1.1.2.1 (Nat.unpair (Nat.unpair (z.1.1.2.2.1 / 7)).2).2 z.1.1.2.2.2.1 z.1.1.2.2.2.2.2.2 &&
        (e₂.2.2.2.1 == 0 && z.1.1.2.2.2.2.2.1 == ite z.1.2.2.2.2.2.1 z.2.2.2.2.2.1 e₂.2.2.2.2.1) :=
    list_any (TR.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.and.comp (sameSlot_prim Primrec.snd (pctx Eu) (pq22 Eu) (penv Eu) (pβ Eu))
        (Primrec.and.comp (beq'.comp (pτ Primrec.snd) (Primrec.const 0))
          (beq'.comp (pv Eu) (ite_prim.comp (Primrec.pair (pv (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.pair (pv (Primrec.snd.comp Primrec.fst)) (pv Primrec.snd))))))).to₂
  have lvl2 : Primrec fun y : (List Entry × Entry) × Entry => y.1.1.any fun e₁ =>
      sameSlot e₁ y.1.2.1 (Nat.unpair (Nat.unpair (y.1.2.2.1 / 7)).2).1 y.1.2.2.2.1 y.1.2.2.2.2.2.2 &&
        (e₁.2.2.2.1 == 0 && y.1.1.any fun e₂ =>
          sameSlot e₂ y.1.2.1 (Nat.unpair (Nat.unpair (y.1.2.2.1 / 7)).2).2 y.1.2.2.2.1 y.1.2.2.2.2.2.2 &&
            (e₂.2.2.2.1 == 0 && y.1.2.2.2.2.2.1 == ite y.2.2.2.2.2.1 e₁.2.2.2.2.1 e₂.2.2.2.2.1)) :=
    list_any (TR.comp Primrec.fst)
      (Primrec.and.comp (sameSlot_prim Primrec.snd (pctx Ez) (pq21 Ez) (penv Ez) (pβ Ez))
        (Primrec.and.comp (beq'.comp (pτ Primrec.snd) (Primrec.const 0)) lvl3)).to₂
  exact (Primrec.and.comp (beq'.comp (pτ E) (Primrec.const 0))
    (list_any TR (Primrec.and.comp (sameSlot_prim Primrec.snd (pctx Ey) (pq1 Ey) (penv Ey) (pβ Ey))
      (Primrec.and.comp (beq'.comp (pτ Primrec.snd) (Primrec.const 0)) lvl2)).to₂)).of_eq fun _ => rfl

theorem entryOK_prim : Primrec fun x : EA => entryOK x.1.1 x.1.2 x.2 := by
  classical
  have E : Primrec fun x : EA => x.2 := Primrec.snd
  have hmod : Primrec fun x : EA => x.2.2.1 % 7 := Primrec.nat_mod.comp (pm E) (Primrec.const 7)
  have hk : ∀ k : ℕ, PrimrecPred fun x : EA => x.2.2.1 % 7 = k := fun k =>
    Primrec.eq.comp hmod (Primrec.const k)
  refine (Primrec.and.comp (entryGen_prim.comp (Primrec.fst.comp Primrec.fst) E)
    (Primrec.ite (hk 0) (entryVar_prim.comp E)
    (Primrec.ite (hk 1) entryLam_prim
    (Primrec.ite (hk 2) entryApp_prim
    (Primrec.ite (hk 3) (entryConst_prim.comp (Primrec.const 1) E)
    (Primrec.ite (hk 4) (entryConst_prim.comp (Primrec.const 2) E)
    (Primrec.ite (hk 5) (entryConst_prim.comp (Primrec.const 0) E)
      (entryIte_prim.comp (Primrec.snd.comp Primrec.fst) E)))))))).of_eq fun x => ?_
  rw [entryOK_eq]
  rfl


/-! ## Carriers and verdicts -/

theorem witnesses_prim : Primrec₂ witnesses :=
  (lookupD (f := fun p : List Wit × ℕ => p.1) (g := fun p => p.2) Primrec.fst Primrec.snd).of_eq
    fun _ => rfl

/-- Arguments of `witOK`: `(tys, trace, c, t, wm)`. -/
abbrev WitArgs := List TyTab × List Entry × ℕ × List ℕ × ℕ

theorem witOK_prim : Primrec fun x : WitArgs => witOK x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have TY : Primrec fun x : WitArgs => x.1 := Primrec.fst
  have TR : Primrec fun x : WitArgs => x.2.1 := Primrec.fst.comp Primrec.snd
  have C : Primrec fun x : WitArgs => x.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have T : Primrec fun x : WitArgs => x.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have W : Primrec fun x : WitArgs => x.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have Q : Primrec fun x : WitArgs => Nat.unpair (x.2.2.2.2 / 7) :=
    Primrec.unpair.comp (Primrec.nat_div.comp W (Primrec.const 7))
  have S : Primrec fun x : WitArgs => (Nat.unpair (x.2.2.2.2 / 7)).1 := Primrec.fst.comp Q
  have Bd : Primrec fun x : WitArgs => (Nat.unpair (x.2.2.2.2 / 7)).2 := Primrec.snd.comp Q
  have y1 : Primrec fun y : WitArgs × ℕ => y.1 := Primrec.fst
  have tuple : Primrec fun y : WitArgs × ℕ => (([(Nat.unpair (y.1.2.2.2.2 / 7)).1], (Nat.unpair (y.1.2.2.2.2 / 7)).2,
      [y.2], cod y.1.2.2.1, y.1.2.2.2.1.getD y.2 0, y.1.2.2.1) : Entry) :=
    mkEntry (Primrec.list_cons.comp (S.comp y1) (Primrec.const [])) (Bd.comp y1)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])) (cod_prim.comp (C.comp y1))
      ((Primrec.list_getD 0).comp (T.comp y1) Primrec.snd) (C.comp y1)
  exact (Primrec.and.comp (Primrec.and.comp
    (beq'.comp (Primrec.nat_mod.comp W (Primrec.const 7)) (Primrec.const 1))
    (beq'.comp S (dom_prim.comp C)))
    (list_all (Primrec.list_range.comp (size_prim.comp TY S))
      (list_any (TR.comp y1) (beq'.comp Primrec.snd (tuple.comp Primrec.fst)).to₂).to₂)).of_eq fun _ => rfl

theorem carrierOK_prim : Primrec₂ carrierOK := by
  -- x : Cert × TyTab
  have TY : Primrec fun x : Cert × TyTab => x.1.1 := Primrec.fst.comp Primrec.fst
  have WI : Primrec fun x : Cert × TyTab => x.1.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have TR : Primrec fun x : Cert × TyTab => x.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have NG : Primrec fun x : Cert × TyTab => x.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have C : Primrec fun x : Cert × TyTab => x.2.1 := Primrec.fst.comp Primrec.snd
  have TS : Primrec fun x : Cert × TyTab => x.2.2 := Primrec.snd.comp Primrec.snd
  have hasTabs : Primrec₂ carrierOK.hasTabs :=
    (list_any (f := fun p : List TyTab × ℕ => p.1) Primrec.fst
      (beq'.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂).of_eq fun _ => rfl
  have DC : Primrec fun x : Cert × TyTab => dom x.2.1 := dom_prim.comp C
  have CC : Primrec fun x : Cert × TyTab => cod x.2.1 := cod_prim.comp C
  have y1 : Primrec fun y : (Cert × TyTab) × ℕ => y.1 := Primrec.fst
  have h1 := Primrec.not.comp (beq'.comp C (Primrec.const 0))
  have h2 := Primrec.or.comp (beq'.comp DC (Primrec.const 0)) (hasTabs.comp TY DC)
  have h3 := Primrec.or.comp (beq'.comp CC (Primrec.const 0)) (hasTabs.comp TY CC)
  have h4 : Primrec fun x : Cert × TyTab => x.2.2.all fun t =>
      t.length == size x.1.1 (dom x.2.1) && t.all (· < size x.1.1 (cod x.2.1)) :=
    list_all TS (Primrec.and.comp
      (beq'.comp (Primrec.list_length.comp Primrec.snd) (size_prim.comp (TY.comp Primrec.fst) (DC.comp Primrec.fst)))
      (list_all Primrec.snd (Primrec.nat_lt.comp Primrec.snd
        (size_prim.comp (TY.comp (Primrec.fst.comp Primrec.fst)) (CC.comp (Primrec.fst.comp Primrec.fst)))).to₂)).to₂
  have h5 : Primrec fun x : Cert × TyTab => (List.range x.2.2.length).all fun i =>
      (List.range x.2.2.length).all fun j => i == j || x.2.2.getD i [] != x.2.2.getD j [] :=
    list_all (Primrec.list_range.comp (Primrec.list_length.comp TS))
      (list_all (Primrec.list_range.comp (Primrec.list_length.comp (TS.comp Primrec.fst)))
        (Primrec.or.comp (beq'.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
          (Primrec.not.comp (beq'.comp
            ((Primrec.list_getD []).comp (TS.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
            ((Primrec.list_getD []).comp (TS.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))).to₂).to₂
  have h6 := beq'.comp (Primrec.list_length.comp (witnesses_prim.comp WI C)) (Primrec.list_length.comp TS)
  have h7 : Primrec fun x : Cert × TyTab => (List.range x.2.2.length).all fun i =>
      witOK x.1.1 x.1.2.2.1 x.2.1 (x.2.2.getD i []) ((witnesses x.1.2.1 x.2.1).getD i 0) :=
    list_all (Primrec.list_range.comp (Primrec.list_length.comp TS))
      (witOK_prim.comp (Primrec.pair (TY.comp y1) (Primrec.pair (TR.comp y1) (Primrec.pair (C.comp y1)
        (Primrec.pair ((Primrec.list_getD []).comp (TS.comp y1) Primrec.snd)
          ((Primrec.list_getD 0).comp (witnesses_prim.comp (WI.comp y1) (C.comp y1)) Primrec.snd)))))).to₂
  have h8 : Primrec fun x : Cert × TyTab => (tuples (size x.1.1 (cod x.2.1)) (size x.1.1 (dom x.2.1))).all fun t =>
      x.2.2.contains t || x.1.2.2.2.any fun n => n.1 == x.2.1 && n.2.1 == t && negValid x.1.1 n :=
    list_all (tuples_prim.comp (size_prim.comp TY CC) (size_prim.comp TY DC))
      (Primrec.or.comp (list_contains (TS.comp Primrec.fst) Primrec.snd)
        (list_any (NG.comp Primrec.fst)
          (Primrec.and.comp (Primrec.and.comp
            (beq'.comp (Primrec.fst.comp Primrec.snd) (C.comp (Primrec.fst.comp Primrec.fst)))
            (beq'.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst)))
            (negValid_prim.comp (TY.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂)).to₂
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp h1 h2) h3) h4) h5) h6) h7) h8).of_eq fun _ => rfl

theorem valid_prim : Primrec valid := by
  have TY : Primrec fun c : Cert => c.1 := Primrec.fst
  have TR : Primrec fun c : Cert => c.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.and.comp (list_all TY carrierOK_prim)
    (list_all TR (entryOK_prim.comp (Primrec.pair (Primrec.pair (TY.comp Primrec.fst) (TR.comp Primrec.fst))
      Primrec.snd)).to₂)).of_eq fun _ => rfl

theorem closedValue_prim : Primrec₂ closedValue := by
  have hp : Primrec₂ fun (x : List Entry × ℕ) (e : Entry) =>
      e.1 == [] && e.2.1 == x.2 && e.2.2.1 == [] && e.2.2.2.2.2 == 0 :=
    (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
      (beq'.comp (pctx Primrec.snd) (Primrec.const []))
      (beq'.comp (pm Primrec.snd) (Primrec.snd.comp Primrec.fst)))
      (beq'.comp (penv Primrec.snd) (Primrec.const [])))
      (beq'.comp (pβ Primrec.snd) (Primrec.const 0))).to₂
  exact (Primrec.option_map (list_find? Primrec.fst hp)
    (Primrec.pair (pτ Primrec.snd) (pv Primrec.snd)).to₂).of_eq fun _ => rfl

theorem verdict_eq (a b : ℕ) (cert : Cert) : verdict a b cert =
    if valid cert = true then
      (closedValue cert.2.2.1 a).bind fun pa => (closedValue cert.2.2.1 b).bind fun pb =>
        if pa.1 = pb.1 then some (pa.2 == pb.2) else none
    else none := by
  unfold verdict
  split_ifs with hv
  · cases closedValue cert.2.2.1 a <;> cases closedValue cert.2.2.1 b <;> rfl
  · rfl

theorem verdict_prim : Primrec fun x : (ℕ × ℕ) × Cert => verdict x.1.1 x.1.2 x.2 := by
  classical
  have C : Primrec fun x : (ℕ × ℕ) × Cert => x.2 := Primrec.snd
  have TR : Primrec fun x : (ℕ × ℕ) × Cert => x.2.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp C))
  have inner : Primrec₂ fun (y : ((ℕ × ℕ) × Cert) × (ℕ × ℕ)) (pb : ℕ × ℕ) =>
      if y.2.1 = pb.1 then some (y.2.2 == pb.2) else none :=
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp (beq'.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)))
      (Primrec.const none)).to₂
  have hbind : Primrec fun x : (ℕ × ℕ) × Cert =>
      (closedValue x.2.2.2.1 x.1.1).bind fun pa => (closedValue x.2.2.2.1 x.1.2).bind fun pb =>
        if pa.1 = pb.1 then some (pa.2 == pb.2) else none :=
    Primrec.option_bind (closedValue_prim.comp TR (Primrec.fst.comp Primrec.fst))
      (Primrec.option_bind (closedValue_prim.comp (TR.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) inner).to₂
  refine (Primrec.ite (Primrec.eq.comp (valid_prim.comp C) (Primrec.const true)) hbind
    (Primrec.const none)).of_eq fun x => ?_
  rw [verdict_eq]


/-! ## Typing certificates -/

theorem appRes_prim : Primrec fun x : ℕ × ℕ × ℕ => appRes x.1 x.2.1 x.2.2 := by
  classical
  have S : Primrec fun x : ℕ × ℕ × ℕ => x.1 := Primrec.fst
  have R1 : Primrec fun x : ℕ × ℕ × ℕ => x.2.1 := Primrec.fst.comp Primrec.snd
  have R2 : Primrec fun x : ℕ × ℕ × ℕ => x.2.2 := Primrec.snd.comp Primrec.snd
  have T : Primrec fun x : ℕ × ℕ × ℕ => x.2.1 - 1 := Primrec.nat_sub.comp R1 (Primrec.const 1)
  have hc : PrimrecPred fun x : ℕ × ℕ × ℕ => x.2.1 ≠ 0 ∧ x.2.1 - 1 ≠ 0 ∧ dom (x.2.1 - 1) = x.1 ∧ x.2.2 = x.1 + 1 :=
    PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp R1 (Primrec.const 0)))
      (PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp T (Primrec.const 0)))
        (PrimrecPred.and (Primrec.eq.comp (dom_prim.comp T) S)
          (Primrec.eq.comp R2 (Primrec.succ.comp S))))
  exact (Primrec.ite hc (Primrec.succ.comp (cod_prim.comp T)) (Primrec.const 0)).of_eq fun _ => rfl

theorem iteRes_prim : Primrec fun x : ℕ × ℕ × ℕ => iteRes x.1 x.2.1 x.2.2 := by
  classical
  have hc : PrimrecPred fun x : ℕ × ℕ × ℕ => x.1 = 1 ∧ x.2.1 = 1 ∧ x.2.2 = 1 :=
    PrimrecPred.and (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (PrimrecPred.and (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
        (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)))
  exact (Primrec.ite hc (Primrec.const 1) (Primrec.const 0)).of_eq fun _ => rfl

/-- `tyChild` with its predicate given as a primitive recursive function of an outer argument. -/
theorem tyChild_prim {X : Type} [Primcodable X] {tt : X → List TyEntry} {ctx : X → List ℕ} {m : X → ℕ}
    {p : X → ℕ → Bool} (htt : Primrec tt) (hctx : Primrec ctx) (hm : Primrec m) (hp : Primrec₂ p) :
    Primrec fun x => tyChild (tt x) (ctx x) (m x) (p x) :=
  (list_any htt (Primrec.and.comp (Primrec.and.comp
    (beq'.comp (Primrec.fst.comp Primrec.snd) (hctx.comp Primrec.fst))
    (beq'.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (hm.comp Primrec.fst)))
    (hp.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂).of_eq fun _ => rfl

def tyEntryOK' (tt : List TyEntry) (e : TyEntry) : Bool :=
  let ctx := e.1
  let m := e.2.1
  let r := e.2.2
  let q := m / 7
  if m % 7 = 0 then r == if q < ctx.length then ctx.getD q 0 + 1 else 0
  else if m % 7 = 1 then
    tyChild tt ((Nat.unpair q).1 :: ctx) (Nat.unpair q).2 fun rb =>
      r == if rb = 0 then 0 else arrow (Nat.unpair q).1 (rb - 1) + 1
  else if m % 7 = 2 then
    tyChild tt ctx (Nat.unpair (Nat.unpair q).2).1 fun r₁ =>
      tyChild tt ctx (Nat.unpair (Nat.unpair q).2).2 fun r₂ => r == appRes (Nat.unpair q).1 r₁ r₂
  else if m % 7 = 3 ∨ m % 7 = 4 ∨ m % 7 = 5 then r == if q = 0 then 1 else 0
  else
    tyChild tt ctx (Nat.unpair q).1 fun rc =>
      tyChild tt ctx (Nat.unpair (Nat.unpair q).2).1 fun r₁ =>
        tyChild tt ctx (Nat.unpair (Nat.unpair q).2).2 fun r₂ => r == iteRes rc r₁ r₂

theorem tyEntryOK_eq (tt : List TyEntry) (e : TyEntry) : tyEntryOK tt e = tyEntryOK' tt e := by
  obtain ⟨ctx, m, r⟩ := e
  have hr : m % 7 < 7 := Nat.mod_lt _ (by norm_num)
  simp only [tyEntryOK, tyEntryOK']
  interval_cases hmod : m % 7 <;> simp

theorem tyEntryOK_prim : Primrec₂ tyEntryOK := by
  classical
  -- x : List TyEntry × TyEntry
  have TT : Primrec fun x : List TyEntry × TyEntry => x.1 := Primrec.fst
  have CTX : Primrec fun x : List TyEntry × TyEntry => x.2.1 := Primrec.fst.comp Primrec.snd
  have M : Primrec fun x : List TyEntry × TyEntry => x.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have R : Primrec fun x : List TyEntry × TyEntry => x.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have Q : Primrec fun x : List TyEntry × TyEntry => x.2.2.1 / 7 := Primrec.nat_div.comp M (Primrec.const 7)
  have Q1 := Primrec.fst.comp (Primrec.unpair.comp Q)
  have Q2 := Primrec.snd.comp (Primrec.unpair.comp Q)
  have Q21 := Primrec.fst.comp (Primrec.unpair.comp Q2)
  have Q22 := Primrec.snd.comp (Primrec.unpair.comp Q2)
  have hmod : Primrec fun x : List TyEntry × TyEntry => x.2.2.1 % 7 := Primrec.nat_mod.comp M (Primrec.const 7)
  have hk : ∀ k : ℕ, PrimrecPred fun x : List TyEntry × TyEntry => x.2.2.1 % 7 = k := fun k =>
    Primrec.eq.comp hmod (Primrec.const k)
  have b0 := beq'.comp R (Primrec.ite (Primrec.nat_lt.comp Q (Primrec.list_length.comp CTX))
    (Primrec.succ.comp ((Primrec.list_getD 0).comp CTX Q)) (Primrec.const 0))
  have b1 := tyChild_prim TT (Primrec.list_cons.comp Q1 CTX) Q2
    (beq'.comp (R.comp Primrec.fst) (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
      (Primrec.succ.comp (arrow_prim.comp (Q1.comp Primrec.fst)
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))))).to₂
  have b2 := tyChild_prim TT CTX Q21
    (tyChild_prim (TT.comp Primrec.fst) (CTX.comp Primrec.fst) (Q22.comp Primrec.fst)
      (beq'.comp (R.comp (Primrec.fst.comp Primrec.fst))
        (appRes_prim.comp (Primrec.pair (Q1.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))).to₂).to₂
  have b3 := beq'.comp R (Primrec.ite (Primrec.eq.comp Q (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0))
  have b6 := tyChild_prim TT CTX Q1
    (tyChild_prim (TT.comp Primrec.fst) (CTX.comp Primrec.fst) (Q21.comp Primrec.fst)
      (tyChild_prim (TT.comp (Primrec.fst.comp Primrec.fst)) (CTX.comp (Primrec.fst.comp Primrec.fst))
        (Q22.comp (Primrec.fst.comp Primrec.fst))
        (beq'.comp (R.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (iteRes_prim.comp (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))).to₂).to₂).to₂
  refine (Primrec.ite (hk 0) b0 (Primrec.ite (hk 1) b1 (Primrec.ite (hk 2) b2
    (Primrec.ite (PrimrecPred.or (hk 3) (PrimrecPred.or (hk 4) (hk 5))) b3 b6)))).of_eq fun x => ?_
  rw [tyEntryOK_eq]
  rfl

theorem tyValid_prim : Primrec tyValid :=
  (list_all Primrec.id tyEntryOK_prim).of_eq fun _ => rfl

theorem closedTy_prim : Primrec₂ closedTy :=
  (Primrec.option_map (list_find? Primrec.fst
    (Primrec.and.comp (beq'.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
      (beq'.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst))).to₂)
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

theorem invalidPair_eq (a b : ℕ) (tt : List TyEntry) : invalidPair a b tt =
    (tyValid tt && ((closedTy tt a).bind fun ra => (closedTy tt b).map fun rb =>
      ra == 0 || rb == 0 || ra != rb).getD false) := by
  unfold invalidPair
  cases closedTy tt a <;> cases closedTy tt b <;> rfl

theorem invalidPair_prim : Primrec fun x : (ℕ × ℕ) × List TyEntry => invalidPair x.1.1 x.1.2 x.2 := by
  have TT : Primrec fun x : (ℕ × ℕ) × List TyEntry => x.2 := Primrec.snd
  have inner : Primrec₂ fun (y : ((ℕ × ℕ) × List TyEntry) × ℕ) (rb : ℕ) =>
      y.2 == 0 || rb == 0 || y.2 != rb :=
    (Primrec.or.comp (Primrec.or.comp (beq'.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0))
      (beq'.comp Primrec.snd (Primrec.const 0)))
      (Primrec.not.comp (beq'.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  refine (Primrec.and.comp (tyValid_prim.comp TT)
    (Primrec.option_getD.comp (Primrec.option_bind (closedTy_prim.comp TT (Primrec.fst.comp Primrec.fst))
      (Primrec.option_map (closedTy_prim.comp (TT.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) inner).to₂) (Primrec.const false))).of_eq fun x => ?_
  rw [invalidPair_eq]

end OR.Sieber.Check
