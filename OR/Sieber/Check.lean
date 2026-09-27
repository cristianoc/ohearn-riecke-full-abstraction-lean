import OR.Sieber.Normal

/-!
# A certificate checker for Sieber's model

Assuming universality, observational equivalence of two closed terms (given by
their codes) is certified by a finite *certificate*, checked by a function with
no recursion: every intermediate result is part of the certificate, and the
checker only performs local consistency checks over lists.

Conventions (all data are natural numbers or lists of them):

* A type is its code (`Ty.code` is a bijection with `ℕ`); `0` is `B`, and a code
  `c > 0` is the arrow type with domain `dom c` and codomain `cod c`.
* Ground values are `0 = ⊥`, `1 = tt`, `2 = ff`. An element of an arrow type is
  an index into the list of *tables* of that type; a table lists, for each
  element of the domain, the index of the result.
* An environment lists the indices of the values of the context variables,
  newest variable first.

A certificate has four parts:

* `tys`: for each arrow type, its tables (the claimed carrier);
* `wit`: for each arrow type, one closed normal form per table, whose
  evaluation only uses strictly smaller types (acceptance witnesses);
* `trace`: evaluation entries `(ctx, term, env, type, value, level)`;
* `negs`: for every other candidate table, a failed test with the exact lifted
  relations at all types involved (rejection witnesses).
-/

set_option autoImplicit false

namespace OR.Sieber.Check

/-! ## Types as codes -/

def dom (c : ℕ) : ℕ := (Nat.unpair (c - 1)).1
def cod (c : ℕ) : ℕ := (Nat.unpair (c - 1)).2
def arrow (s t : ℕ) : ℕ := Nat.pair s t + 1

/-! ## Certificates -/

abbrev TyTab := ℕ × List (List ℕ)
abbrev Wit := ℕ × List ℕ
/-- `(ctx, term, env, type, value, level)`; level `0` is unrestricted, level `β > 0`
requires every type involved to have code `< β`. -/
abbrev Entry := List ℕ × ℕ × List ℕ × ℕ × ℕ × ℕ
abbrev Lift := ℕ × List (List ℕ)
/-- `(type, candidate, arity, test, argument tuple, lifted relations)`. -/
abbrev Neg := ℕ × List ℕ × ℕ × List (List ℕ × List ℕ) × List ℕ × List Lift
abbrev Cert := List TyTab × List Wit × List Entry × List Neg

section
variable (tys : List TyTab)

def tabs (c : ℕ) : List (List ℕ) := ((tys.find? (fun e => e.1 == c)).map Prod.snd).getD []

def size (c : ℕ) : ℕ := if c = 0 then 3 else (tabs tys c).length

/-- Application of element `u` of arrow type `c` to element `h`. -/
def app (c u h : ℕ) : ℕ := ((tabs tys c).getD u []).getD h 0

end

/-! ## Enumeration -/

/-- All lists of length `w` with entries `< n`. -/
def tuples (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | w + 1 => (tuples n w).flatMap (fun t => (List.range n).map (fun x => x :: t))

/-! ## Relations -/

/-- The test `d` holds of the ground tuple `u` (values `0 = ⊥`). -/
def holds (d : List (List ℕ × List ℕ)) (u : List ℕ) : Bool :=
  d.all fun p =>
    !(p.1.all fun i => p.2.contains i) ||
    (p.1.any fun i => u.getD i 0 == 0) ||
    (p.2.all fun i => p.2.all fun j => u.getD i 0 == u.getD j 0)

def liftSet (lifts : List Lift) (c : ℕ) : List (List ℕ) :=
  ((lifts.find? (fun e => e.1 == c)).map Prod.snd).getD []

/-- Pointwise application of a `w`-tuple of functions to a `w`-tuple of arguments. -/
def appTuple (tys : List TyTab) (w c : ℕ) (u h : List ℕ) : List ℕ :=
  (List.range w).map fun i => app tys c (u.getD i 0) (h.getD i 0)

/-- The defining condition of the lifted relation at type `c`. -/
def cond (tys : List TyTab) (w : ℕ) (d : List (List ℕ × List ℕ)) (lifts : List Lift)
    (c : ℕ) (u : List ℕ) : Bool :=
  if c = 0 then holds d u
  else (liftSet lifts (dom c)).all fun h =>
    (liftSet lifts (cod c)).contains (appTuple tys w c u h)

def hasLift (lifts : List Lift) (c : ℕ) : Bool := lifts.any fun e => e.1 == c

/-- A rejection witness is valid. -/
def negValid (tys : List TyTab) (n : Neg) : Bool :=
  let (c, t, w, d, g, lifts) := n
  (d.all fun p => (p.1.all (· < w)) && (p.2.all (· < w))) &&
  hasLift lifts (dom c) && hasLift lifts (cod c) &&
  (lifts.all fun e => e.1 == 0 || (hasLift lifts (dom e.1) && hasLift lifts (cod e.1))) &&
  (lifts.all fun e => e.2.all fun u => (tuples (size tys e.1) w).contains u) &&
  (lifts.all fun e => (tuples (size tys e.1) w).all fun u =>
    e.2.contains u == cond tys w d lifts e.1 u) &&
  (tuples (size tys (dom c)) w).contains g &&
  (liftSet lifts (dom c)).contains g &&
  !((liftSet lifts (cod c)).contains (g.map fun gi => t.getD gi 0))

/-! ## Evaluation traces -/

def ite (c a b : ℕ) : ℕ := if c = 1 then a else if c = 2 then b else 0

/-- The children of an entry are present and consistent. -/
def entryOK (tys : List TyTab) (trace : List Entry) (e : Entry) : Bool :=
  let (ctx, m, env, τ, v, β) := e
  let q := m / 7
  let child (ctx' : List ℕ) (m' : ℕ) (env' : List ℕ) (τ' v' : ℕ) : Bool :=
    trace.any fun e' => e' == (ctx', m', env', τ', v', β)
  let childTy (ctx' : List ℕ) (m' : ℕ) (env' : List ℕ) (p : ℕ → ℕ → Bool) : Bool :=
    trace.any fun e' => e'.1 == ctx' && e'.2.1 == m' && e'.2.2.1 == env' && e'.2.2.2.2.2 == β &&
      p e'.2.2.2.1 e'.2.2.2.2.1
  (env.length == ctx.length) &&
  ((List.range ctx.length).all fun k => env.getD k 0 < size tys (ctx.getD k 0)) &&
  v < size tys τ &&
  (β == 0 || (τ < β && ctx.all (· < β))) &&
  match m % 7 with
  | 0 => q < ctx.length && τ == ctx.getD q 0 && v == env.getD q 0
  | 1 =>
      let s := (Nat.unpair q).1
      let body := (Nat.unpair q).2
      τ != 0 && dom τ == s &&
      (List.range (size tys s)).all fun a =>
        child (s :: ctx) body (a :: env) (cod τ) (((tabs tys τ).getD v []).getD a 0)
  | 2 =>
      let s := (Nat.unpair q).1
      let m₁ := (Nat.unpair (Nat.unpair q).2).1
      let m₂ := (Nat.unpair (Nat.unpair q).2).2
      childTy ctx m₁ env fun τ₁ v₁ => τ₁ == arrow s τ &&
        childTy ctx m₂ env fun τ₂ v₂ => τ₂ == s && v == app tys τ₁ v₁ v₂
  | 3 => q == 0 && τ == 0 && v == 1
  | 4 => q == 0 && τ == 0 && v == 2
  | 5 => q == 0 && τ == 0 && v == 0
  | _ =>
      let mc := (Nat.unpair q).1
      let m₁ := (Nat.unpair (Nat.unpair q).2).1
      let m₂ := (Nat.unpair (Nat.unpair q).2).2
      τ == 0 &&
      childTy ctx mc env fun τc vc => τc == 0 &&
        childTy ctx m₁ env fun τ₁ v₁ => τ₁ == 0 &&
          childTy ctx m₂ env fun τ₂ v₂ => τ₂ == 0 && v == ite vc v₁ v₂

/-! ## Carriers and witnesses -/

def witnesses (wit : List Wit) (c : ℕ) : List ℕ := ((wit.find? (fun e => e.1 == c)).map Prod.snd).getD []

/-- The table `t` of arrow type `c` is the evaluation of the closed normal form `wm`,
using only types smaller than `c`. -/
def witOK (tys : List TyTab) (trace : List Entry) (c : ℕ) (t : List ℕ) (wm : ℕ) : Bool :=
  let s := (Nat.unpair (wm / 7)).1
  let body := (Nat.unpair (wm / 7)).2
  wm % 7 == 1 && s == dom c &&
  (List.range (size tys s)).all fun a =>
    trace.any fun e => e == ([s], body, [a], cod c, t.getD a 0, c)

def carrierOK (cert : Cert) (e : TyTab) : Bool :=
  let (tys, wit, trace, negs) := cert
  let (c, ts) := e
  c != 0 &&
  (dom c == 0 || hasTabs tys (dom c)) && (cod c == 0 || hasTabs tys (cod c)) &&
  (ts.all fun t => t.length == size tys (dom c) && t.all (· < size tys (cod c))) &&
  ((List.range ts.length).all fun i => (List.range ts.length).all fun j =>
    i == j || ts.getD i [] != ts.getD j []) &&
  (witnesses wit c).length == ts.length &&
  ((List.range ts.length).all fun i => witOK tys trace c (ts.getD i []) ((witnesses wit c).getD i 0)) &&
  ((tuples (size tys (cod c)) (size tys (dom c))).all fun t =>
    ts.contains t || negs.any fun n => n.1 == c && n.2.1 == t && negValid tys n)
where
  hasTabs (tys : List TyTab) (c : ℕ) : Bool := tys.any fun e => e.1 == c

/-- The certificate is valid. -/
def valid (cert : Cert) : Bool :=
  let (tys, _, trace, _) := cert
  (tys.all fun e => carrierOK cert e) && (trace.all fun e => entryOK tys trace e)

/-- The value of the closed term with code `m` recorded in the trace, with its type. -/
def closedValue (trace : List Entry) (m : ℕ) : Option (ℕ × ℕ) :=
  (trace.find? fun e => e.1 == [] && e.2.1 == m && e.2.2.1 == [] && e.2.2.2.2.2 == 0).map
    fun e => (e.2.2.2.1, e.2.2.2.2.1)

/-- The certificate's verdict on the pair `(a, b)`: `some true` (equivalent),
`some false` (inequivalent), or `none` (no verdict). -/
def verdict (a b : ℕ) (cert : Cert) : Option Bool :=
  if valid cert then
    match closedValue cert.2.2.1 a, closedValue cert.2.2.1 b with
    | some (τa, va), some (τb, vb) => if τa = τb then some (va == vb) else none
    | _, _ => none
  else none

end OR.Sieber.Check
