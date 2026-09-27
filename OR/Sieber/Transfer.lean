import OR.Projections
import OR.Sieber.NatModel
import OR.Sieber.Soundness

/-!
# From the Boolean Sieber model to level 1 of the natural one

`SIEBER.md`, Section 4, Lemmas 7–9: the ordinary Boolean Sieber model `D^B` is
embedded in the ordinary natural Sieber model `D^N` by maps `i`, `r` with
`r ∘ i = id` and `i ∘ r = ψ¹`, which preserve and reflect the ordinary tests,
and the level-1 elements are exactly the images `i h`.
Compactness (Lemma 10) is `level_compact` in `Algebraic`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable section

namespace OR.NS

/-! ## Projections in the ordinary natural model -/

/-- The level-`n` projection `ψⁿ`, as the denotation of the PCF term `Ψⁿ`. -/
def psi (τ : Ty) (n : ℕ) : Hom (typeObj τ) (typeObj τ) := denoteClosed (projectionTerm τ n)

theorem psi_nat_zero (d : Ground) : psi .nat 0 d = Ground.ifz d (.val 0) .bot := by
  simp [psi, projectionTerm, groundProjectionTerm, denoteClosed, denote_lam, denote_ifz, denote_var,
    lookup, denote_omega]
  rfl

theorem psi_nat_succ (n : ℕ) (d : Ground) :
    psi .nat (n + 1) d = Ground.ifz d (.val 0) (Ground.succ (psi .nat n (Ground.pred d))) := by
  simp [psi, projectionTerm, groundProjectionTerm, denoteClosed, denote_lam, denote_ifz, denote_var,
    lookup, denote_succ, denote_app, denote_closed, denote_pred]

theorem psi_nat (n : ℕ) (d : Ground) : psi .nat n d = Ground.cut n d := by
  induction n generalizing d with
  | zero =>
      rw [psi_nat_zero]
      cases d with
      | bot => rfl
      | val k => cases k <;> simp [Ground.cut]
  | succ n ih =>
      rw [psi_nat_succ]
      cases d with
      | bot => rfl
      | val k =>
          cases k with
          | zero => simp [Ground.cut]
          | succ k =>
              rw [Ground.ifz_succ, Ground.pred_succ, ih]
              by_cases hk : k ≤ n
              · simp [Ground.cut, hk, Nat.succ_le_succ_iff]
              · simp [Ground.cut, hk, Nat.succ_le_succ_iff]

theorem psi_arr (σ τ : Ty) (n : ℕ) (f : D (σ ⇒ τ)) (x : D σ) :
    psi (σ ⇒ τ) n f x = psi τ n (f (psi σ n x)) := by
  simp [psi, projectionTerm, denoteClosed, denote_lam, denote_app, denote_closed, denote_var, lookup]

theorem cut_le (n : ℕ) (d : Ground) : Ground.cut n d ≤ d := by
  cases d with
  | bot => exact bot_le
  | val k =>
      by_cases h : k ≤ n
      · simp [Ground.cut, h]
      · simp only [Ground.cut, h, if_false]; exact bot_le

/-- Projections lie below the identity. -/
theorem psi_le : ∀ (τ : Ty) (n : ℕ) (x : D τ), psi τ n x ≤ x
  | .nat, n, x => by rw [psi_nat]; exact cut_le n x
  | .arr σ τ, n, f => fun x => by
      rw [psi_arr]
      exact le_trans (psi_le τ n _) (f.mono (psi_le σ n x))

end OR.NS

namespace OR.Sieber

open OR.NS

/-- Boolean types as natural-number types. -/
def natTy : Ty → OR.Ty
  | .B => .nat
  | .arr σ τ => .arr (natTy σ) (natTy τ)

/-! ## Ground maps (Lemma 7) -/

/-- `⊥ ↦ ⊥`, `tt ↦ 0`, `ff ↦ 1`. -/
def jv : Val → Ground
  | .bot => .bot
  | .tt => .val 0
  | .ff => .val 1

/-- `0 ↦ tt`, `1 ↦ ff`, everything else `↦ ⊥`. -/
def qv : Ground → Val
  | .val 0 => .tt
  | .val 1 => .ff
  | _ => .bot

theorem qv_jv (v : Val) : qv (jv v) = v := by cases v <;> rfl

theorem jv_qv (d : Ground) : jv (qv d) = Ground.cut 1 d := by
  rcases d with _ | _ | _ | k
  · rfl
  · rfl
  · rfl
  · simp [jv, qv, Ground.cut]

theorem qv_cut (d : Ground) : qv (Ground.cut 1 d) = qv d := by
  rcases d with _ | _ | _ | k
  · rfl
  · rfl
  · rfl
  · simp [qv, Ground.cut]

theorem jv_eq_bot {v : Val} : jv v = .bot ↔ v = .bot := by cases v <;> simp [jv]

theorem jv_inj {a b : Val} (h : jv a = jv b) : a = b := by
  rw [← qv_jv a, h, qv_jv]

theorem qv_bot : qv .bot = .bot := rfl

theorem jv_mono {a b : Val} (h : Val.le a b) : jv a ≤ jv b := by
  rcases h with rfl | rfl
  · exact bot_le
  · exact le_rfl

theorem qv_mono {a b : Ground} (h : a ≤ b) : Val.le (qv a) (qv b) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Lemma (7a): a test holds of a Boolean tuple iff it holds of its image in `ℕ⊥`. -/
theorem test_jv {w : ℕ} (d : Test w) (g : Fin w → Val) :
    d.holds g ↔ gholds ⟨w, d⟩ (fun k => jv (g k)) := by
  simp only [Test.holds, gholds]
  apply forall_congr'; intro p; apply forall_congr'; intro _; apply forall_congr'; intro _
  simp only [Elem, Elementary, jv_eq_bot]
  exact or_congr Iff.rfl ⟨fun h i hi k hk => by rw [h i hi k hk], fun h i hi k hk => jv_inj (h i hi k hk)⟩

/-- Lemma (7b): the projection to Boolean values preserves every test. -/
theorem test_qv {w : ℕ} (d : Test w) (h : Fin w → Ground) (hh : gholds ⟨w, d⟩ h) :
    d.holds (fun k => qv (h k)) := by
  intro p hp hAB
  rcases hh p hp hAB with ⟨i, hi, hbot⟩ | hc
  · exact Or.inl ⟨i, hi, by simp [hbot, qv_bot]⟩
  · exact Or.inr fun i hi k hk => by simp [hc i hi k hk]


theorem Model.le_antisymm : ∀ (τ : Ty) (a b : (Model τ).car), (Model τ).le a b → (Model τ).le b a → a = b
  | .B, a, b, h, h' => by
      change Val at a b
      rcases h with rfl | rfl
      · rcases h' with h' | h' <;> exact h'.symm
      · rfl
  | .arr _ ρ, a, b, h, h' => Subtype.ext (funext fun x => Model.le_antisymm ρ _ _ (h x) (h' x))

/-! ## The transfer maps (Lemma 8) -/

/-- The maps `i`, `r` at one type, with the properties of Lemma 8 and an attained form
of continuity of `r`. -/
structure Tr (τ : Ty) where
  i : SieberBool τ → NS.D (natTy τ)
  r : NS.D (natTy τ) → SieberBool τ
  i_mono : ∀ a b, (Model τ).le a b → i a ≤ i b
  r_mono : ∀ x y, x ≤ y → (Model τ).le (r x) (r y)
  rel_i : ∀ (w : ℕ) (d : Test w) (g : Fin w → SieberBool τ),
    (Model τ).rel w d g ↔ (NS.typeObj (natTy τ)).R ⟨w, d⟩ (fun k => i (g k))
  rel_r : ∀ (w : ℕ) (d : Test w) (h : Fin w → NS.D (natTy τ)),
    (NS.typeObj (natTy τ)).R ⟨w, d⟩ h → (Model τ).rel w d (fun k => r (h k))
  r_i : ∀ a, r (i a) = a
  i_r : ∀ x, i (r x) = NS.psi (natTy τ) 1 x
  r_attain : ∀ (s : Set (NS.D (natTy τ))) (hs : Dir s), ∃ e ∈ s, r e = r (dSup s hs)

def trB : Tr .B where
  i := jv
  r := qv
  i_mono _ _ h := jv_mono h
  r_mono _ _ h := qv_mono h
  rel_i w d g := test_jv d g
  rel_r w d h hh := test_qv d h hh
  r_i := qv_jv
  i_r x := by
    change jv (qv x) = NS.psi .nat 1 x
    rw [jv_qv, NS.psi_nat]
  r_attain s hs := ⟨dSup s hs, Flat.dSup_mem hs, rfl⟩

/-- The arrow step. -/
def trArr {σ ρ : Ty} (A : Tr σ) (C : Tr ρ) : Tr (σ ⇒ ρ) where
  i f := ⟨⟨fun x => C.i (f.1 (A.r x)),
      fun x y h => C.i_mono _ _ (f.2.1 _ _ (A.r_mono _ _ h)),
      fun s hs b hb => by
        obtain ⟨e, he, hre⟩ := A.r_attain s hs
        change C.i (f.1 (A.r (dSup s hs))) ≤ b
        rw [← hre]
        exact hb e he⟩,
    fun t G hG => by
      obtain ⟨w, d⟩ := t
      exact (C.rel_i w d _).mp (f.2.2 w d _ (A.rel_r w d G hG))⟩
  r := fun (F : NS.D (natTy σ ⇒ natTy ρ)) => ⟨fun a => C.r (F (A.i a)),
    fun a b h => C.r_mono _ _ (F.mono (A.i_mono _ _ h)),
    fun w d g hg => C.rel_r w d _ (F.uniform ⟨w, d⟩ _ ((A.rel_i w d g).mp hg))⟩
  i_mono f f' h x := C.i_mono _ _ (h (A.r x))
  r_mono := fun (F F' : NS.D (natTy σ ⇒ natTy ρ)) h a => C.r_mono _ _ (h (A.i a))
  rel_i w d fs := by
    constructor
    · intro hf G hG
      exact (C.rel_i w d _).mp (hf _ (A.rel_r w d G hG))
    · intro hf g hg
      have := hf _ ((A.rel_i w d g).mp hg)
      simp only [A.r_i] at this
      exact (C.rel_i w d _).mpr this
  rel_r w d Fs hF g hg := C.rel_r w d _ (hF _ ((A.rel_i w d g).mp hg))
  r_i f := by
    apply Subtype.ext
    funext a
    change C.r (C.i (f.1 (A.r (A.i a)))) = f.1 a
    rw [A.r_i, C.r_i]
  i_r := fun (F : NS.D (natTy σ ⇒ natTy ρ)) => by
    apply NS.Hom.ext
    intro x
    change C.i (C.r (F (A.i (A.r x)))) = _
    rw [C.i_r, A.i_r]
    exact (NS.psi_arr ..).symm
  r_attain := fun (s : Set (NS.D (natTy σ ⇒ natTy ρ))) hs => by
    classical
    haveI := finite_car σ
    haveI := Fintype.ofFinite (SieberBool σ)
    have hpt : ∀ a : SieberBool σ, ∃ F ∈ s, C.r (F (A.i a)) = C.r ((dSup s hs) (A.i a)) := by
      intro a
      have happ := NS.Hom.dSup_apply s hs (A.i a)
      obtain ⟨y, hy, hry⟩ := C.r_attain _ (hs.image (fun F : NS.Hom _ _ => F (A.i a)) (fun _ _ h => h (A.i a)))
      obtain ⟨F, hF, rfl⟩ := hy
      refine ⟨F, hF, ?_⟩
      rw [hry]
      exact congrArg C.r happ.symm
    choose Fa hFa hrFa using hpt
    obtain ⟨(Fb : NS.D (natTy σ ⇒ natTy ρ)), hFb, hle⟩ := hs.finite_bound Finset.univ Fa (fun a _ => hFa a)
    refine ⟨Fb, hFb, Subtype.ext (funext fun a => ?_)⟩
    change C.r (Fb (A.i a)) = C.r ((dSup s hs) (A.i a))
    apply Model.le_antisymm
    · exact C.r_mono _ _ ((le_dSup hs hFb) (A.i a))
    · rw [← hrFa a]
      exact C.r_mono _ _ (hle a (Finset.mem_univ a) (A.i a))

def tr : (τ : Ty) → Tr τ
  | .B => trB
  | .arr σ ρ => trArr (tr σ) (tr ρ)

/-- `i h` is fixed by `ψ¹`. -/
theorem psi_i (τ : Ty) (h : SieberBool τ) : NS.psi (natTy τ) 1 ((tr τ).i h) = (tr τ).i h := by
  rw [← (tr τ).i_r, (tr τ).r_i]

end OR.Sieber
