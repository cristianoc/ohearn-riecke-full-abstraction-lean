import OR.Sieber.Standard

/-!
# Sieber's model of finitary PCF

The ordinary (single-world) sequentiality-relation model over `{⊥, tt, ff}`.

A *test* of arity `w` is a finite set `d` of pairs `(A, B)` of subsets of
`Fin w`; it denotes the intersection of Sieber's relations
`S^w_{A,B} = {g | (∃ i ∈ A, g i = ⊥) ∨ g is constant on B}` over the pairs with
`A ⊆ B`. These are exactly the sequentiality relations of arity `w`.

Each type denotes a carrier with an order and, for every test, a relation on
`w`-tuples, lifted logically. At `σ ⇒ τ` the carrier consists of the monotone
maps between the carriers of `σ` and `τ` that preserve every test.
-/

set_option autoImplicit false

namespace OR.Sieber

/-! ## Ground values -/

def Val.le (a b : Val) : Prop := a = .bot ∨ a = b

/-- Sieber's elementary relation `S^w_{A,B}`. -/
def Elem {w : ℕ} (A B : Finset (Fin w)) (g : Fin w → Val) : Prop :=
  (∃ i ∈ A, g i = .bot) ∨ ∀ i ∈ B, ∀ j ∈ B, g i = g j

/-- A test: a finite family of pairs `(A, B)`. -/
abbrev Test (w : ℕ) := Finset (Finset (Fin w) × Finset (Fin w))

/-- The sequentiality relation denoted by a test. -/
def Test.holds {w : ℕ} (d : Test w) (g : Fin w → Val) : Prop :=
  ∀ p ∈ d, p.1 ⊆ p.2 → Elem p.1 p.2 g

/-! ## The model -/

/-- The data attached to a type: carrier, order, and lifted relations. -/
structure Lvl where
  car : Type
  le : car → car → Prop
  rel : (w : ℕ) → Test w → (Fin w → car) → Prop

/-- Sieber's model, type by type. -/
def Model : Ty → Lvl
  | .B => ⟨Val, Val.le, fun _ d g => d.holds g⟩
  | .arr σ τ =>
    let S := Model σ
    let T := Model τ
    { car := {f : S.car → T.car //
        (∀ a b, S.le a b → T.le (f a) (f b)) ∧
        ∀ w (d : Test w) (g : Fin w → S.car), S.rel w d g → T.rel w d (fun i => f (g i))}
      le := fun f g => ∀ a, T.le (f.1 a) (g.1 a)
      rel := fun w d F => ∀ g : Fin w → S.car, S.rel w d g → T.rel w d (fun i => (F i).1 (g i)) }

/-- Elements of Sieber's model at type `τ`. -/
abbrev SieberBool (τ : Ty) : Type := (Model τ).car

/-! ## Basic properties -/

theorem Model.le_refl : ∀ (τ : Ty) (x : (Model τ).car), (Model τ).le x x
  | .B, _ => Or.inr rfl
  | .arr _ τ, _ => fun _ => Model.le_refl τ _

theorem Model.le_trans : ∀ (τ : Ty) (x y z : (Model τ).car),
    (Model τ).le x y → (Model τ).le y z → (Model τ).le x z
  | .B, x, y, z, hxy, hyz => by
      rcases hxy with rfl | rfl
      · exact Or.inl rfl
      · exact hyz
  | .arr _ τ, _, _, _, hxy, hyz => fun a => Model.le_trans τ _ _ _ (hxy a) (hyz a)

/-- Constant tuples are related: every element preserves every test. -/
theorem Model.concrete : ∀ (τ : Ty) (w : ℕ) (d : Test w) (x : (Model τ).car),
    (Model τ).rel w d (fun _ => x)
  | .B, _, _, _ => fun _ _ _ => Or.inr (fun _ _ _ _ => rfl)
  | .arr _ _, w, d, x => fun g hg => x.2.2 w d g hg

/-! ## Interpretation of terms -/

def Env : Ctx → Type
  | [] => PUnit
  | σ :: Γ => Env Γ × (Model σ).car

def Env.le : (Γ : Ctx) → Env Γ → Env Γ → Prop
  | [], _, _ => True
  | σ :: Γ, ρ, ρ' => Env.le Γ ρ.1 ρ'.1 ∧ (Model σ).le ρ.2 ρ'.2

def Env.rel : (Γ : Ctx) → (w : ℕ) → Test w → (Fin w → Env Γ) → Prop
  | [], _, _, _ => True
  | σ :: Γ, w, d, R => Env.rel Γ w d (fun i => (R i).1) ∧ (Model σ).rel w d (fun i => (R i).2)

theorem Env.concrete : ∀ (Γ : Ctx) (w : ℕ) (d : Test w) (ρ : Env Γ), Env.rel Γ w d (fun _ => ρ)
  | [], _, _, _ => trivial
  | σ :: Γ, w, d, ρ => ⟨Env.concrete Γ w d ρ.1, Model.concrete σ w d ρ.2⟩

/-- Monotone, relation-preserving maps from environments. -/
def Sem (Γ : Ctx) (τ : Ty) : Type :=
  {h : Env Γ → (Model τ).car //
    (∀ ρ ρ', Env.le Γ ρ ρ' → (Model τ).le (h ρ) (h ρ')) ∧
    ∀ w (d : Test w) (R : Fin w → Env Γ), Env.rel Γ w d R → (Model τ).rel w d (fun i => h (R i))}

def Var.sem : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Sem Γ τ
  | _ :: _, _, .vz => ⟨fun ρ => ρ.2, fun _ _ h => h.2, fun _ _ _ h => h.2⟩
  | _ :: _, _, .vs x =>
      ⟨fun ρ => x.sem.1 ρ.1, fun _ _ h => x.sem.2.1 _ _ h.1, fun _ _ _ h => x.sem.2.2 _ _ _ h.1⟩

theorem Val.ite_mono {c c' a a' b b' : Val} (hc : Val.le c c') (ha : Val.le a a') (hb : Val.le b b') :
    Val.le (Val.ite c a b) (Val.ite c' a' b') := by
  rcases hc with rfl | rfl
  · exact Or.inl rfl
  · cases c <;> simp only [Val.ite] <;> first | exact Or.inl rfl | assumption

theorem Elem.ite {w : ℕ} {A B : Finset (Fin w)} (hAB : A ⊆ B) {c a b : Fin w → Val}
    (hc : Elem A B c) (ha : Elem A B a) (hb : Elem A B b) :
    Elem A B (fun i => Val.ite (c i) (a i) (b i)) := by
  rcases hc with ⟨i, hi, hci⟩ | hc
  · exact Or.inl ⟨i, hi, by simp only [hci, Val.ite]⟩
  by_cases hB : ∃ j, j ∈ B
  · obtain ⟨j, hj⟩ := hB
    have hconst : ∀ i ∈ B, c i = c j := fun i hi => hc i hi j hj
    cases hcj : c j with
    | bot => exact Or.inr (fun i hi k hk => by simp only [hconst i hi, hconst k hk, hcj, Val.ite])
    | tt =>
        rcases ha with ⟨i, hi, hai⟩ | ha
        · exact Or.inl ⟨i, hi, by simp only [hconst i (hAB hi), hcj, Val.ite, hai]⟩
        · exact Or.inr (fun i hi k hk => by
            simp only [hconst i hi, hconst k hk, hcj, Val.ite]; exact ha i hi k hk)
    | ff =>
        rcases hb with ⟨i, hi, hbi⟩ | hb
        · exact Or.inl ⟨i, hi, by simp only [hconst i (hAB hi), hcj, Val.ite, hbi]⟩
        · exact Or.inr (fun i hi k hk => by
            simp only [hconst i hi, hconst k hk, hcj, Val.ite]; exact hb i hi k hk)
  · exact Or.inr (fun i hi => absurd ⟨i, hi⟩ hB)

theorem Test.holds_ite {w : ℕ} (d : Test w) {c a b : Fin w → Val}
    (hc : d.holds c) (ha : d.holds a) (hb : d.holds b) :
    d.holds (fun i => Val.ite (c i) (a i) (b i)) :=
  fun p hp hAB => Elem.ite hAB (hc p hp hAB) (ha p hp hAB) (hb p hp hAB)

def constSem {Γ : Ctx} (v : Val) : Sem Γ .B :=
  ⟨fun _ => v, fun _ _ _ => Or.inr rfl, fun _ _ _ _ => Model.concrete .B _ _ v⟩

/-- The interpretation of terms in Sieber's model. -/
def Tm.sem : {Γ : Ctx} → {τ : Ty} → Tm Γ τ → Sem Γ τ
  | _, _, .var x => x.sem
  | Γ, .arr σ _, .lam M =>
      ⟨fun ρ => ⟨fun a => M.sem.1 (ρ, a),
          fun _ _ h => M.sem.2.1 _ _ ⟨Env.le_refl Γ ρ, h⟩,
          fun w d g hg => M.sem.2.2 w d (fun i => (ρ, g i)) ⟨Env.concrete Γ w d ρ, hg⟩⟩,
        fun _ _ h a => M.sem.2.1 _ _ ⟨h, Model.le_refl σ a⟩,
        fun w d R hR g hg => M.sem.2.2 w d (fun i => (R i, g i)) ⟨hR, hg⟩⟩
  | _, _, .app M N =>
      ⟨fun ρ => (M.sem.1 ρ).1 (N.sem.1 ρ),
        fun _ _ h => Model.le_trans _ _ _ _ ((M.sem.1 _).2.1 _ _ (N.sem.2.1 _ _ h)) (M.sem.2.1 _ _ h _),
        fun w d R hR => M.sem.2.2 w d R hR _ (N.sem.2.2 w d R hR)⟩
  | _, _, .tt => constSem .tt
  | _, _, .ff => constSem .ff
  | _, _, .bot => constSem .bot
  | _, _, .ite C M N =>
      ⟨fun ρ => Val.ite (C.sem.1 ρ) (M.sem.1 ρ) (N.sem.1 ρ),
        fun _ _ h => Val.ite_mono (C.sem.2.1 _ _ h) (M.sem.2.1 _ _ h) (N.sem.2.1 _ _ h),
        fun w d R hR => Test.holds_ite d (C.sem.2.2 w d R hR) (M.sem.2.2 w d R hR) (N.sem.2.2 w d R hR)⟩
where
  Env.le_refl : ∀ (Γ : Ctx) (ρ : Env Γ), Env.le Γ ρ ρ
    | [], _ => trivial
    | σ :: Γ, ρ => ⟨Env.le_refl Γ ρ.1, Model.le_refl σ ρ.2⟩

/-- The denotation of a closed term. -/
def Tm.den {τ : Ty} (M : Tm [] τ) : SieberBool τ := M.sem.1 PUnit.unit

/-- An element of Sieber's model is definable when it is the denotation of a closed term. -/
def Definable {τ : Ty} (f : SieberBool τ) : Prop := ∃ M : Tm [] τ, M.den = f

/-- Every element at every type is definable. -/
def Universal : Prop := ∀ (τ : Ty) (f : SieberBool τ), Definable f

end OR.Sieber
