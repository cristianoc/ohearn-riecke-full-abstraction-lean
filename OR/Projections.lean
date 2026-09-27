import OR.Interpretation

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

noncomputable section

namespace OR

 def groundProjectionTerm : ℕ → Tm [] (.nat ⇒ .nat)
  | 0 => .lam (.ifz (.var .vz) .zero (Tm.omega .nat))
  | n + 1 => .lam (.ifz (.var .vz) .zero
      (.succ (.app (Tm.closed (groundProjectionTerm n)) (.pred (.var .vz)))))

 def projectionTerm : (τ : Ty) → ℕ → Tm [] (τ ⇒ τ)
  | .nat, n => groundProjectionTerm n
  | .arr σ τ, n =>
      .lam (.lam (.app (Tm.closed (projectionTerm τ n))
        (.app (.var (.vs .vz)) (.app (Tm.closed (projectionTerm σ n)) (.var .vz)))))

/-- Definability, continuity, and relational uniformity of projections are by construction. -/
 def projection (τ : Ty) (n : ℕ) : Hom (typeObj τ) (typeObj τ) :=
  denoteClosed (projectionTerm τ n)

 def Ground.cut (n : ℕ) : Ground → Ground
  | .bot => .bot
  | .val k => if k ≤ n then .val k else .bot

 theorem projection_nat_zero (d : Ground) :
    projection .nat 0 d = Ground.ifz d (.val 0) .bot := by
  simp [projection, projectionTerm, groundProjectionTerm, denoteClosed, denote_lam,
    denote_ifz, denote_var, lookup, denote_omega]

 theorem projection_nat_succ (n : ℕ) (d : Ground) :
    projection .nat (n + 1) d =
      Ground.ifz d (.val 0) (Ground.succ (projection .nat n (Ground.pred d))) := by
  simp [projection, projectionTerm, groundProjectionTerm, denoteClosed, denote_lam,
    denote_ifz, denote_var, lookup, denote_succ, denote_app, denote_closed, denote_pred]

 theorem projection_nat (n : ℕ) (d : Ground) : projection .nat n d = Ground.cut n d := by
  induction n generalizing d with
  | zero =>
      rw [projection_nat_zero]
      cases d with
      | bot => rfl
      | val k => cases k <;> simp [Ground.cut]
  | succ n ih =>
      rw [projection_nat_succ]
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

 theorem projection_arr_apply (σ τ : Ty) (n : ℕ) (f : D (σ ⇒ τ)) (x : D σ) :
    projection (σ ⇒ τ) n f x = projection τ n (f (projection σ n x)) := by
  simp [projection, projectionTerm, denoteClosed, denote_lam, denote_app,
    denote_closed, denote_var, lookup]

 theorem projection_le : ∀ (τ : Ty) (n : ℕ) (d : D τ), projection τ n d ≤ d := by
  intro τ
  induction τ with
  | nat =>
      intro n d
      rw [projection_nat]
      cases d with
      | bot => exact le_rfl
      | val k =>
          by_cases h : k ≤ n
          · simp [Ground.cut, h]
          · simp [Ground.cut, h]
  | arr σ τ ihσ ihτ =>
      intro n f x
      rw [projection_arr_apply]
      exact (ihτ n _).trans (f.mono (ihσ n x))

 theorem projection_index_mono : ∀ (τ : Ty) (d : D τ),
    Monotone (fun n => projection τ n d) := by
  intro τ
  induction τ with
  | nat =>
      intro d n m hnm
      rw [projection_nat, projection_nat]
      cases d with
      | bot => exact le_rfl
      | val k =>
          by_cases hkn : k ≤ n
          · simp [Ground.cut, hkn, hkn.trans hnm]
          · simp [Ground.cut, hkn]
  | arr σ τ ihσ ihτ =>
      intro f n m hnm x
      rw [projection_arr_apply, projection_arr_apply]
      exact ((projection τ n).mono (f.mono (ihσ x hnm))).trans (ihτ _ hnm)

 theorem projection_comp : ∀ (τ : Ty) (m n : ℕ) (d : D τ),
    projection τ m (projection τ n d) = projection τ (min m n) d := by
  intro τ
  induction τ with
  | nat =>
      intro m n d
      cases d with
      | bot => simp [projection_nat, Ground.cut]
      | val k =>
          by_cases hn : k ≤ n <;> by_cases hm : k ≤ m <;>
            simp [projection_nat, Ground.cut, hn, hm, le_min_iff]
  | arr σ τ ihσ ihτ =>
      intro m n f
      apply Hom.ext
      intro x
      simp only [projection_arr_apply]
      rw [ihτ, ihσ]
      rw [min_comm n m]

@[simp] theorem projection_idem (τ : Ty) (n : ℕ) (d : D τ) :
    projection τ n (projection τ n d) = projection τ n d := by
  simpa only [min_self] using projection_comp τ n n d

@[simp] theorem projection_bot (τ : Ty) (n : ℕ) : projection τ n ⊥ = ⊥ :=
  le_antisymm (projection_le τ n ⊥) bot_le

 def projectionChain (τ : Ty) (d : D τ) : Chain (D τ) :=
  ⟨fun n => projection τ n d, projection_index_mono τ d⟩

/-- The arrow step explicitly dominates a double approximation by the `max` diagonal. -/
 theorem projection_approximates : ∀ (τ : Ty) (d : D τ), (projectionChain τ d).sup = d := by
  intro τ
  induction τ with
  | nat =>
      intro d
      apply le_antisymm
      · exact (projectionChain .nat d).sup_le (fun n => projection_le .nat n d)
      · cases d with
        | bot => exact bot_le
        | val k =>
            have h := (projectionChain .nat (.val k)).le_sup k
            simpa [projectionChain, projection_nat, Ground.cut] using h
  | arr σ τ ihσ ihτ =>
      intro f
      apply Hom.ext
      intro x
      rw [Hom.chain_sup_apply]
      let c : Chain (D τ) :=
        ⟨fun n => projection (σ ⇒ τ) n f x,
          fun _ _ h => projection_index_mono (σ ⇒ τ) f h x⟩
      change c.sup = f x
      apply le_antisymm
      · exact c.sup_le (fun n => projection_le (σ ⇒ τ) n f x)
      · have hx : x = (projectionChain σ x).sup := (ihσ x).symm
        rw [hx]
        apply f.val.map_le _ (projectionChain σ x).dir
        rintro _ ⟨n, rfl⟩
        calc
          f (projection σ n x) = (projectionChain τ (f (projection σ n x))).sup :=
            (ihτ _).symm
          _ ≤ c.sup := by
            apply Chain.sup_le
            intro m
            let k := max m n
            have hm : m ≤ k := le_max_left _ _
            have hn : n ≤ k := le_max_right _ _
            calc
              projection τ m (f (projection σ n x)) ≤
                  projection τ k (f (projection σ n x)) := projection_index_mono τ _ hm
              _ ≤ projection τ k (f (projection σ k x)) :=
                (projection τ k).mono (f.mono (projection_index_mono σ x hn))
              _ = c k := (projection_arr_apply σ τ k f x).symm
              _ ≤ c.sup := c.le_sup k

abbrev Level (τ : Ty) (n : ℕ) := {d : D τ // projection τ n d = d}

/-- Input absorption must hold on arbitrary, not just finite, arguments. -/
 theorem finite_input_absorption {σ τ : Ty} {n : ℕ} {f : D (σ ⇒ τ)}
    (hf : projection (σ ⇒ τ) n f = f) (x : D σ) :
    f (projection σ n x) = f x := by
  have hpoint : ∀ y, projection τ n (f (projection σ n y)) = f y := by
    intro y
    have h := congrArg (fun g : D (σ ⇒ τ) => g y) hf
    simpa only [projection_arr_apply] using h
  calc
    f (projection σ n x) = projection τ n (f (projection σ n (projection σ n x))) :=
      (hpoint _).symm
    _ = projection τ n (f (projection σ n x)) := by rw [projection_idem]
    _ = f x := hpoint x

 theorem finite_output_fixed {σ τ : Ty} {n : ℕ} {f : D (σ ⇒ τ)}
    (hf : projection (σ ⇒ τ) n f = f) (x : D σ) : projection τ n (f x) = f x := by
  have he : projection τ n (f (projection σ n x)) = f x := by
    simpa only [projection_arr_apply] using congrArg (fun g : D (σ ⇒ τ) => g x) hf
  rw [← he, projection_idem]

 theorem finite_nat_bound {n k : ℕ} (a : Level .nat n) (ha : a.val = .val k) : k ≤ n := by
  have hp := a.property
  rw [projection_nat, ha] at hp
  by_contra hk
  simp [Ground.cut, hk] at hp

 def finiteNatCode {n : ℕ} (a : Level .nat n) : Fin (n + 2) :=
  match h : a.val with
  | .bot => ⟨0, by omega⟩
  | .val k => ⟨k + 1, by have hk := finite_nat_bound a h; omega⟩

 theorem finiteNatCode_injective (n : ℕ) : Function.Injective (@finiteNatCode n) := by
  intro a b h
  have he := congrArg Fin.val h
  apply Subtype.ext
  cases ha : a.val with
  | bot =>
      cases hb : b.val with
      | bot => simp only [ha, hb]
      | val k => simp [finiteNatCode, ha, hb] at he
  | val k =>
      cases hb : b.val with
      | bot => simp [finiteNatCode, ha, hb] at he
      | val j =>
          have hkj : k = j := by simpa [finiteNatCode, ha, hb] using he
          simp only [ha, hb, hkj]

 def finiteRestriction {σ τ : Ty} {n : ℕ} (f : Level (σ ⇒ τ) n) :
    Level σ n → Level τ n :=
  fun a => ⟨f.val a.val, finite_output_fixed f.property a.val⟩

 theorem finiteRestriction_injective (σ τ : Ty) (n : ℕ) :
    Function.Injective (@finiteRestriction σ τ n) := by
  intro f g h
  apply Subtype.ext
  apply Hom.ext
  intro x
  let a : Level σ n := ⟨projection σ n x, projection_idem σ n x⟩
  have he := congrArg (fun k : Level σ n → Level τ n => (k a).val) h
  change f.val (projection σ n x) = g.val (projection σ n x) at he
  rw [finite_input_absorption f.property x, finite_input_absorption g.property x] at he
  exact he

 theorem finite_level : ∀ (τ : Ty) (n : ℕ), Finite (Level τ n) := by
  intro τ
  induction τ with
  | nat =>
      intro n
      exact Finite.of_injective finiteNatCode (finiteNatCode_injective n)
  | arr σ τ ihσ ihτ =>
      intro n
      letI : Finite (Level σ n) := ihσ n
      letI : Finite (Level τ n) := ihτ n
      exact Finite.of_injective finiteRestriction (finiteRestriction_injective σ τ n)

instance levelFinite (τ : Ty) (n : ℕ) : Finite (Level τ n) := finite_level τ n
instance levelInhabited (τ : Ty) (n : ℕ) : Inhabited (Level τ n) :=
  ⟨⟨⊥, projection_bot τ n⟩⟩

 def envProjection : (Γ : Ctx) → ℕ → Hom (envObj Γ) (envObj Γ)
  | [], _ => Hom.id
  | σ :: Γ, n =>
      ((envProjection Γ n).comp Hom.fst).pair ((projection σ n).comp Hom.snd)

@[simp] theorem envProjection_cons (Γ : Ctx) (σ : Ty) (n : ℕ) (ρ : Env Γ) (a : D σ) :
    envProjection (σ :: Γ) n (ρ, a) = (envProjection Γ n ρ, projection σ n a) := rfl

 theorem envProjection_le : ∀ (Γ : Ctx) (n : ℕ) (ρ : Env Γ), envProjection Γ n ρ ≤ ρ := by
  intro Γ
  induction Γ with
  | nil => intro n ρ; exact le_rfl
  | cons σ Γ ih => intro n ρ; exact ⟨ih n ρ.1, projection_le σ n ρ.2⟩

 theorem envProjection_index_mono : ∀ (Γ : Ctx) (ρ : Env Γ),
    Monotone (fun n => envProjection Γ n ρ) := by
  intro Γ
  induction Γ with
  | nil => intro ρ n m h; exact le_rfl
  | cons σ Γ ih =>
      intro ρ n m h
      exact ⟨ih ρ.1 h, projection_index_mono σ ρ.2 h⟩

@[simp] theorem lookup_envProjection {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (n : ℕ) (ρ : Env Γ) :
    lookup x (envProjection Γ n ρ) = projection τ n (lookup x ρ) := by
  induction x generalizing n ρ with
  | vz => rfl
  | vs x ih => exact ih n ρ.1

 theorem envProjection_idem : ∀ (Γ : Ctx) (n : ℕ) (ρ : Env Γ),
    envProjection Γ n (envProjection Γ n ρ) = envProjection Γ n ρ := by
  intro Γ n ρ
  apply env_ext
  intro τ x
  simp only [lookup_envProjection, projection_idem]

 def envProjectionChain (Γ : Ctx) (ρ : Env Γ) : Chain (Env Γ) :=
  ⟨fun n => envProjection Γ n ρ, envProjection_index_mono Γ ρ⟩

 theorem envProjection_approximates : ∀ (Γ : Ctx) (ρ : Env Γ),
    (envProjectionChain Γ ρ).sup = ρ := by
  intro Γ
  induction Γ with
  | nil => intro ρ; exact Subsingleton.elim _ _
  | cons σ Γ ih =>
      intro ρ
      apply Prod.ext
      · calc
          ((envProjectionChain (σ :: Γ) ρ).sup).1 = (envProjectionChain Γ ρ.1).sup :=
            (envProjectionChain (σ :: Γ) ρ).map_sup CMap.fst
          _ = ρ.1 := ih ρ.1
      · calc
          ((envProjectionChain (σ :: Γ) ρ).sup).2 = (projectionChain σ ρ.2).sup :=
            (envProjectionChain (σ :: Γ) ρ).map_sup CMap.snd
          _ = ρ.2 := projection_approximates σ ρ.2

end OR
