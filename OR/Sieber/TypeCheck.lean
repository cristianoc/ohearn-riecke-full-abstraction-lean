import OR.Sieber.CheckSound

/-!
# Certificates for type inference

A typing certificate is a list of entries `(ctx, m, r)`: `r = t + 1` claims that `m`
is the code of a term of type `t` in context `ctx`, and `r = 0` claims that it is
the code of no term. As for evaluation traces, each entry is checked locally
against the entries of its immediate subterms. This makes invalid pairs of codes
semi-decidable.
-/

set_option autoImplicit false

namespace OR.Sieber.Check

abbrev TyEntry := List ℕ × ℕ × ℕ

/-- The result of an application, from the results of its function and argument. -/
def appRes (s r₁ r₂ : ℕ) : ℕ :=
  if r₁ ≠ 0 ∧ r₁ - 1 ≠ 0 ∧ dom (r₁ - 1) = s ∧ r₂ = s + 1 then cod (r₁ - 1) + 1 else 0

def iteRes (rc r₁ r₂ : ℕ) : ℕ := if rc = 1 ∧ r₁ = 1 ∧ r₂ = 1 then 1 else 0

def tyChild (tt : List TyEntry) (ctx : List ℕ) (m : ℕ) (p : ℕ → Bool) : Bool :=
  tt.any fun e => e.1 == ctx && e.2.1 == m && p e.2.2

def tyEntryOK (tt : List TyEntry) (e : TyEntry) : Bool :=
  let (ctx, m, r) := e
  let q := m / 7
  match m % 7 with
  | 0 => r == if q < ctx.length then ctx.getD q 0 + 1 else 0
  | 1 =>
      let s := (Nat.unpair q).1
      tyChild tt (s :: ctx) (Nat.unpair q).2 fun rb => r == if rb = 0 then 0 else arrow s (rb - 1) + 1
  | 2 =>
      let s := (Nat.unpair q).1
      tyChild tt ctx (Nat.unpair (Nat.unpair q).2).1 fun r₁ =>
        tyChild tt ctx (Nat.unpair (Nat.unpair q).2).2 fun r₂ => r == appRes s r₁ r₂
  | 3 => r == if q = 0 then 1 else 0
  | 4 => r == if q = 0 then 1 else 0
  | 5 => r == if q = 0 then 1 else 0
  | _ =>
      tyChild tt ctx (Nat.unpair q).1 fun rc =>
        tyChild tt ctx (Nat.unpair (Nat.unpair q).2).1 fun r₁ =>
          tyChild tt ctx (Nat.unpair (Nat.unpair q).2).2 fun r₂ => r == iteRes rc r₁ r₂

def tyValid (tt : List TyEntry) : Bool := tt.all (tyEntryOK tt)

/-- The certified type result of the closed term code `m`. -/
def closedTy (tt : List TyEntry) (m : ℕ) : Option ℕ :=
  (tt.find? fun e => e.1 == [] && e.2.1 == m).map fun e => e.2.2

/-- A typing certificate showing that `(a, b)` is not a pair of closed terms of the same type. -/
def invalidPair (a b : ℕ) (tt : List TyEntry) : Bool :=
  tyValid tt &&
    match closedTy tt a, closedTy tt b with
    | some ra, some rb => ra == 0 || rb == 0 || ra != rb
    | _, _ => false

/-! ## Soundness -/

/-- `m` codes a term of type `t` in context `ctx`. -/
def TypedAs (ctx : List ℕ) (m t : ℕ) : Prop :=
  ∃ M : Tm (ctx.map Ty.decode) (Ty.decode t), M.code = m

theorem typedAs_iff {ctx : List ℕ} {m t : ℕ} :
    TypedAs ctx m t ↔ ∃ (τ : Ty) (M : Tm (ctx.map Ty.decode) τ), M.code = m ∧ τ.code = t := by
  constructor
  · rintro ⟨M, hM⟩; exact ⟨_, M, hM, Ty.code_decode t⟩
  · rintro ⟨τ, M, hM, rfl⟩; unfold TypedAs; rw [Ty.decode_code]; exact ⟨M, hM⟩

/-- A code determines the type of the term it codes. -/
theorem typedAs_unique {ctx : List ℕ} {m t t' : ℕ} (h : TypedAs ctx m t) (h' : TypedAs ctx m t') :
    t = t' := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨M', hM'⟩ := h'
  obtain ⟨hty, -⟩ := Tm.code_inj M M' (hM.trans hM'.symm)
  rw [← Ty.code_decode t, hty, Ty.code_decode]


/-! ## Typing by constructor -/

theorem Var.code_lt : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), x.code < Γ.length
  | _ :: _, _, .vz => by simp [Var.code]
  | _ :: _, _, .vs x => by simp [Var.code]; exact Var.code_lt x

theorem Var.type_get : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), Γ.getD x.code .B = τ
  | _ :: _, _, .vz => rfl
  | _ :: _, _, .vs x => by simp only [Var.code, List.getD_cons_succ]; exact Var.type_get x

theorem var_of_lt : ∀ (Γ : Ctx) (k : ℕ), k < Γ.length → ∃ x : Var Γ (Γ.getD k .B), x.code = k
  | [], _, hk => absurd hk (by simp)
  | σ :: Γ, 0, _ => ⟨.vz, rfl⟩
  | σ :: Γ, k + 1, hk => by
      obtain ⟨x, hx⟩ := var_of_lt Γ k (by simpa using hk)
      exact ⟨.vs x, by simp [Var.code, hx]⟩

theorem getD_map_decode {ctx : List ℕ} {k : ℕ} (hk : k < ctx.length) :
    (ctx.map Ty.decode).getD k .B = Ty.decode (ctx.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem typed_var {ctx : List ℕ} {m t : ℕ} (hm : m % 7 = 0) :
    TypedAs ctx m t ↔ m / 7 < ctx.length ∧ t = ctx.getD (m / 7) 0 := by
  rw [typedAs_iff]
  constructor
  · rintro ⟨τ, M, hM, rfl⟩
    cases M with
    | var x =>
        simp only [Tm.code] at hM
        have hx : x.code = m / 7 := by omega
        have hlt := Var.code_lt x
        have hty := Var.type_get x
        rw [List.length_map] at hlt
        rw [hx] at hlt hty
        refine ⟨hlt, ?_⟩
        rw [getD_map_decode hlt] at hty
        rw [← hty, Ty.code_decode]
    | _ => simp only [Tm.code] at hM; omega
  · rintro ⟨hlt, rfl⟩
    obtain ⟨x, hx⟩ := var_of_lt (ctx.map Ty.decode) (m / 7) (by simpa using hlt)
    refine ⟨_, .var x, by simp only [Tm.code, hx]; omega, ?_⟩
    rw [getD_map_decode hlt, Ty.code_decode]

theorem typed_lam {ctx : List ℕ} {m t : ℕ} (hm : m % 7 = 1) :
    TypedAs ctx m t ↔ ∃ tb, TypedAs ((Nat.unpair (m / 7)).1 :: ctx) (Nat.unpair (m / 7)).2 tb ∧
      t = arrow (Nat.unpair (m / 7)).1 tb := by
  constructor
  · rw [typedAs_iff]
    rintro ⟨τ, M, hM, rfl⟩
    cases M with
    | @lam _ σ ρ M' =>
        simp only [Tm.code] at hM
        have hq : m / 7 = Nat.pair σ.code M'.code := by omega
        rw [hq, Nat.unpair_pair]
        refine ⟨ρ.code, typedAs_iff.mpr ?_, rfl⟩
        have e : (σ.code :: ctx).map Ty.decode = σ :: ctx.map Ty.decode := by simp [Ty.decode_code]
        rw [e]
        exact ⟨ρ, M', rfl, rfl⟩
    | _ => simp only [Tm.code] at hM; omega
  · rintro ⟨tb, ⟨M', hM'⟩, rfl⟩
    refine typedAs_iff.mpr ⟨_, .lam M', ?_, ?_⟩
    · simp only [Tm.code, Ty.code_decode, hM', Nat.pair_unpair]; omega
    · simp only [code_arr, Ty.code_decode]

theorem typed_app {ctx : List ℕ} {m t : ℕ} (hm : m % 7 = 2) :
    TypedAs ctx m t ↔ TypedAs ctx (Nat.unpair (Nat.unpair (m / 7)).2).1 (arrow (Nat.unpair (m / 7)).1 t) ∧
      TypedAs ctx (Nat.unpair (Nat.unpair (m / 7)).2).2 (Nat.unpair (m / 7)).1 := by
  constructor
  · rw [typedAs_iff]
    rintro ⟨τ, M, hM, rfl⟩
    cases M with
    | @app _ σ _ M₁ M₂ =>
        simp only [Tm.code] at hM
        have hq : m / 7 = Nat.pair σ.code (Nat.pair M₁.code M₂.code) := by omega
        rw [hq, Nat.unpair_pair, Nat.unpair_pair]
        exact ⟨typedAs_iff.mpr ⟨_, M₁, rfl, code_arr σ τ⟩, typedAs_iff.mpr ⟨_, M₂, rfl, rfl⟩⟩
    | _ => simp only [Tm.code] at hM; omega
  · rintro ⟨h₁, ⟨M₂, hM₂⟩⟩
    unfold TypedAs at h₁
    rw [decode_arrow] at h₁
    obtain ⟨M₁, hM₁⟩ := h₁
    refine typedAs_iff.mpr ⟨_, .app M₁ M₂, ?_, Ty.code_decode t⟩
    simp only [Tm.code, Ty.code_decode, hM₁, hM₂, Nat.pair_unpair]; omega

theorem typed_const {ctx : List ℕ} {m t : ℕ} (hm : m % 7 = 3 ∨ m % 7 = 4 ∨ m % 7 = 5) :
    TypedAs ctx m t ↔ m / 7 = 0 ∧ t = 0 := by
  constructor
  · rw [typedAs_iff]
    rintro ⟨τ, M, hM, rfl⟩
    cases M <;> simp only [Tm.code] at hM <;> first | omega | exact ⟨by omega, rfl⟩
  · rintro ⟨hq, rfl⟩
    have hm' : m = m % 7 := by omega
    unfold TypedAs
    rw [Ty.decode_zero]
    rcases hm with h | h | h
    · exact ⟨.tt, by simp only [Tm.code]; omega⟩
    · exact ⟨.ff, by simp only [Tm.code]; omega⟩
    · exact ⟨.bot, by simp only [Tm.code]; omega⟩

theorem typed_ite {ctx : List ℕ} {m t : ℕ} (hm : m % 7 = 6) :
    TypedAs ctx m t ↔ t = 0 ∧ TypedAs ctx (Nat.unpair (m / 7)).1 0 ∧
      TypedAs ctx (Nat.unpair (Nat.unpair (m / 7)).2).1 0 ∧
      TypedAs ctx (Nat.unpair (Nat.unpair (m / 7)).2).2 0 := by
  constructor
  · rw [typedAs_iff]
    rintro ⟨τ, M, hM, rfl⟩
    cases M with
    | ite C M₁ M₂ =>
        simp only [Tm.code] at hM
        have hq : m / 7 = Nat.pair C.code (Nat.pair M₁.code M₂.code) := by omega
        rw [hq, Nat.unpair_pair, Nat.unpair_pair]
        exact ⟨rfl, typedAs_iff.mpr ⟨_, C, rfl, rfl⟩, typedAs_iff.mpr ⟨_, M₁, rfl, rfl⟩,
          typedAs_iff.mpr ⟨_, M₂, rfl, rfl⟩⟩
    | _ => simp only [Tm.code] at hM; omega
  · rintro ⟨rfl, hC, h₁, h₂⟩
    unfold TypedAs at hC h₁ h₂ ⊢
    rw [Ty.decode_zero] at hC h₁ h₂ ⊢
    obtain ⟨C, hC⟩ := hC
    obtain ⟨M₁, hM₁⟩ := h₁
    obtain ⟨M₂, hM₂⟩ := h₂
    exact ⟨.ite C M₁ M₂, by simp only [Tm.code, hC, hM₁, hM₂, Nat.pair_unpair]; omega⟩

/-! ## The intended results -/

open Classical in
/-- The intended result: `t + 1` if `m` codes a term of type `t`, and `0` otherwise. -/
noncomputable def tyres (ctx : List ℕ) (m : ℕ) : ℕ :=
  if h : ∃ t, TypedAs ctx m t then Classical.choose h + 1 else 0

theorem tyres_of_typed {ctx : List ℕ} {m t : ℕ} (h : TypedAs ctx m t) : tyres ctx m = t + 1 := by
  have hex : ∃ t, TypedAs ctx m t := ⟨t, h⟩
  unfold tyres
  rw [dif_pos hex, typedAs_unique (Classical.choose_spec hex) h]

theorem tyres_of_untyped {ctx : List ℕ} {m : ℕ} (h : ∀ t, ¬ TypedAs ctx m t) : tyres ctx m = 0 := by
  unfold tyres
  rw [dif_neg (fun ⟨t, ht⟩ => h t ht)]

theorem typed_of_tyres {ctx : List ℕ} {m : ℕ} (h : tyres ctx m ≠ 0) : TypedAs ctx m (tyres ctx m - 1) := by
  by_cases hex : ∃ t, TypedAs ctx m t
  · obtain ⟨t, ht⟩ := hex
    rw [tyres_of_typed ht]; simpa using ht
  · push_neg at hex
    exact absurd (tyres_of_untyped hex) h

theorem untyped_of_tyres {ctx : List ℕ} {m : ℕ} (h : tyres ctx m = 0) (t : ℕ) : ¬ TypedAs ctx m t :=
  fun ht => by rw [tyres_of_typed ht] at h; omega

theorem tyres_iff {ctx : List ℕ} {m t : ℕ} : tyres ctx m = t + 1 ↔ TypedAs ctx m t := by
  constructor
  · intro h
    have := typed_of_tyres (ctx := ctx) (m := m) (by omega)
    rwa [h, Nat.add_sub_cancel] at this
  · exact tyres_of_typed

/-- The local equation satisfied by the results, in terms of the results `R` of subterms. -/
def tyFormula (R : List ℕ → ℕ → ℕ) (ctx : List ℕ) (m : ℕ) : ℕ :=
  let q := m / 7
  match m % 7 with
  | 0 => if q < ctx.length then ctx.getD q 0 + 1 else 0
  | 1 =>
      let rb := R ((Nat.unpair q).1 :: ctx) (Nat.unpair q).2
      if rb = 0 then 0 else arrow (Nat.unpair q).1 (rb - 1) + 1
  | 2 => appRes (Nat.unpair q).1 (R ctx (Nat.unpair (Nat.unpair q).2).1) (R ctx (Nat.unpair (Nat.unpair q).2).2)
  | 3 => if q = 0 then 1 else 0
  | 4 => if q = 0 then 1 else 0
  | 5 => if q = 0 then 1 else 0
  | _ => iteRes (R ctx (Nat.unpair q).1) (R ctx (Nat.unpair (Nat.unpair q).2).1)
      (R ctx (Nat.unpair (Nat.unpair q).2).2)

theorem tyres_eq (ctx : List ℕ) (m : ℕ) : tyres ctx m = tyFormula tyres ctx m := by
  have hr : m % 7 < 7 := Nat.mod_lt _ (by norm_num)
  unfold tyFormula
  interval_cases hmod : m % 7
  · simp only
    split_ifs with h
    · exact tyres_of_typed ((typed_var hmod).mpr ⟨h, rfl⟩)
    · exact tyres_of_untyped fun t ht => h ((typed_var hmod).mp ht).1
  · simp only
    split_ifs with h
    · exact tyres_of_untyped fun t ht => by
        obtain ⟨tb, htb, -⟩ := (typed_lam hmod).mp ht
        exact untyped_of_tyres h tb htb
    · exact tyres_of_typed ((typed_lam hmod).mpr ⟨_, typed_of_tyres h, rfl⟩)
  · simp only
    unfold appRes
    split_ifs with h
    · obtain ⟨h1, h2, h3, h4⟩ := h
      apply tyres_of_typed
      apply (typed_app hmod).mpr
      refine ⟨?_, ?_⟩
      · have := typed_of_tyres h1
        rwa [← h3, arrow_dom_cod h2] 
      · have := typed_of_tyres (ctx := ctx) (m := (Nat.unpair (Nat.unpair (m / 7)).2).2) (by omega)
        rwa [h4, Nat.add_sub_cancel] at this
    · apply tyres_of_untyped
      intro t ht
      obtain ⟨h1, h2⟩ := (typed_app hmod).mp ht
      apply h
      have e1 := tyres_of_typed h1
      have e2 := tyres_of_typed h2
      refine ⟨by omega, ?_, ?_, e2⟩
      · rw [e1, Nat.add_sub_cancel]; simp [arrow]
      · rw [e1, Nat.add_sub_cancel, dom_arrow]
  · simp only
    split_ifs with h
    · exact tyres_of_typed ((typed_const (Or.inl hmod)).mpr ⟨h, rfl⟩)
    · exact tyres_of_untyped fun t ht => h ((typed_const (Or.inl hmod)).mp ht).1
  · simp only
    split_ifs with h
    · exact tyres_of_typed ((typed_const (Or.inr (Or.inl hmod))).mpr ⟨h, rfl⟩)
    · exact tyres_of_untyped fun t ht => h ((typed_const (Or.inr (Or.inl hmod))).mp ht).1
  · simp only
    split_ifs with h
    · exact tyres_of_typed ((typed_const (Or.inr (Or.inr hmod))).mpr ⟨h, rfl⟩)
    · exact tyres_of_untyped fun t ht => h ((typed_const (Or.inr (Or.inr hmod))).mp ht).1
  · simp only
    unfold iteRes
    split_ifs with h
    · obtain ⟨h1, h2, h3⟩ := h
      exact tyres_of_typed ((typed_ite hmod).mpr ⟨rfl, tyres_iff.mp h1, tyres_iff.mp h2, tyres_iff.mp h3⟩)
    · apply tyres_of_untyped
      intro t ht
      obtain ⟨-, h1, h2, h3⟩ := (typed_ite hmod).mp ht
      exact h ⟨tyres_of_typed h1, tyres_of_typed h2, tyres_of_typed h3⟩

/-! ## Soundness and completeness of typing certificates -/

theorem tyChild_spec {tt : List TyEntry} {ctx : List ℕ} {m : ℕ} {p : ℕ → Bool}
    (h : tyChild tt ctx m p = true) : ∃ r, (ctx, m, r) ∈ tt ∧ p r = true := by
  simp only [tyChild, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨c', m', r⟩, he, ⟨h1, h2⟩, hp⟩ := h
  simp only at h1 h2 hp
  subst h1 h2
  exact ⟨r, he, hp⟩

/-- In a valid typing certificate every entry records the intended result. -/
theorem ty_sound {tt : List TyEntry} (hv : tyValid tt = true) :
    ∀ e ∈ tt, e.2.2 = tyres e.1 e.2.1 := by
  have hok : ∀ e ∈ tt, tyEntryOK tt e = true := by
    simpa [tyValid, List.all_eq_true] using hv
  suffices H : ∀ m, ∀ e ∈ tt, e.2.1 = m → e.2.2 = tyres e.1 e.2.1 from fun e he => H _ e he rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rintro ⟨ctx, m', r⟩ he hm
  simp only at hm ⊢
  subst hm
  have h := hok _ he
  rw [tyres_eq]
  have hr : m' % 7 < 7 := Nat.mod_lt _ (by norm_num)
  simp only [tyEntryOK] at h
  unfold tyFormula
  interval_cases hmod : m' % 7
  · simpa using h
  · obtain ⟨rb, hrb, hp⟩ := tyChild_spec h
    have := ih _ (unpair_right_lt (by rw [hmod]; norm_num)) _ hrb rfl
    simp only at this
    simp only [beq_iff_eq] at hp
    simp only [← this]; exact hp
  · obtain ⟨r₁, h₁, hp⟩ := tyChild_spec h
    obtain ⟨r₂, h₂, hp'⟩ := tyChild_spec hp
    have e₁ := ih _ (unpair_rl_lt (by rw [hmod]; norm_num)) _ h₁ rfl
    have e₂ := ih _ (unpair_rr_lt (by rw [hmod]; norm_num)) _ h₂ rfl
    simp only at e₁ e₂
    simp only [beq_iff_eq] at hp'
    simp only [← e₁, ← e₂]; exact hp'
  · simpa using h
  · simpa using h
  · simpa using h
  · obtain ⟨rc, hc, hp⟩ := tyChild_spec h
    obtain ⟨r₁, h₁, hp₁⟩ := tyChild_spec hp
    obtain ⟨r₂, h₂, hp₂⟩ := tyChild_spec hp₁
    have ec := ih _ (unpair_left_lt (by rw [hmod]; norm_num)) _ hc rfl
    have e₁ := ih _ (unpair_rl_lt (by rw [hmod]; norm_num)) _ h₁ rfl
    have e₂ := ih _ (unpair_rr_lt (by rw [hmod]; norm_num)) _ h₂ rfl
    simp only at ec e₁ e₂
    simp only [beq_iff_eq] at hp₂
    simp only [← ec, ← e₁, ← e₂]; exact hp₂

/-- The entries for a code and all its sub-codes. -/
noncomputable def tyEntries (ctx : List ℕ) (m : ℕ) : List TyEntry :=
  (ctx, m, tyres ctx m) ::
    (if h₁ : m % 7 = 1 then tyEntries ((Nat.unpair (m / 7)).1 :: ctx) (Nat.unpair (m / 7)).2
    else if _h₂ : m % 7 = 2 then
      tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).1 ++ tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).2
    else if _h₆ : m % 7 = 6 then
      tyEntries ctx (Nat.unpair (m / 7)).1 ++ tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).1 ++
        tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).2
    else [])
termination_by m
decreasing_by
  · exact unpair_right_lt (by omega)
  · exact unpair_rl_lt (by omega)
  · exact unpair_rr_lt (by omega)
  · exact unpair_left_lt (by omega)
  · exact unpair_rl_lt (by omega)
  · exact unpair_rr_lt (by omega)

theorem tyEntries_head (ctx : List ℕ) (m : ℕ) : (ctx, m, tyres ctx m) ∈ tyEntries ctx m := by
  rw [tyEntries]; exact List.mem_cons_self

theorem tyEntries_ok {tt : List TyEntry} :
    ∀ m ctx, (∀ e ∈ tyEntries ctx m, e ∈ tt) → ∀ e ∈ tyEntries ctx m, tyEntryOK tt e = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro ctx hsub e he
  have hsub' := hsub
  rw [tyEntries] at he hsub'
  rcases List.mem_cons.mp he with rfl | he
  · -- the head entry
    have hr : m % 7 < 7 := Nat.mod_lt _ (by norm_num)
    have heq := tyres_eq ctx m
    unfold tyFormula at heq
    simp only [tyEntryOK]
    have kid : ∀ ctx' m', m' < m → (∀ e ∈ tyEntries ctx' m', e ∈ tt) → (ctx', m', tyres ctx' m') ∈ tt :=
      fun ctx' m' _ h => h _ (tyEntries_head ctx' m')
    interval_cases hmod : m % 7
    · simpa using heq
    · simp only [dif_pos hmod] at hsub'
      apply List.any_eq_true.mpr
      refine ⟨_, kid _ _ (unpair_right_lt (by rw [hmod]; norm_num))
        (fun e he => hsub' e (List.mem_cons_of_mem _ he)), ?_⟩
      simpa using heq
    · simp only [show m % 7 ≠ 1 by omega, dif_neg, not_false_eq_true, dif_pos hmod] at hsub'
      apply List.any_eq_true.mpr
      refine ⟨_, kid _ _ (unpair_rl_lt (by rw [hmod]; norm_num))
        (fun e he => hsub' e (List.mem_cons_of_mem _ (List.mem_append_left _ he))), ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, true_and]
      apply List.any_eq_true.mpr
      refine ⟨_, kid _ _ (unpair_rr_lt (by rw [hmod]; norm_num))
        (fun e he => hsub' e (List.mem_cons_of_mem _ (List.mem_append_right _ he))), ?_⟩
      simpa using heq
    · simpa using heq
    · simpa using heq
    · simpa using heq
    · simp only [show m % 7 ≠ 1 by omega, show m % 7 ≠ 2 by omega, dif_neg, not_false_eq_true,
        dif_pos hmod] at hsub'
      apply List.any_eq_true.mpr
      refine ⟨_, kid _ _ (unpair_left_lt (by rw [hmod]; norm_num))
        (fun e he => hsub' e (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ he)))), ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, true_and]
      apply List.any_eq_true.mpr
      refine ⟨_, kid _ _ (unpair_rl_lt (by rw [hmod]; norm_num))
        (fun e he => hsub' e (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ he)))), ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, true_and]
      apply List.any_eq_true.mpr
      refine ⟨_, kid _ _ (unpair_rr_lt (by rw [hmod]; norm_num))
        (fun e he => hsub' e (List.mem_cons_of_mem _ (List.mem_append_right _ he))), ?_⟩
      simpa using heq
  · -- entries of sub-codes
    have hsubTail : ∀ e ∈ (if h₁ : m % 7 = 1 then tyEntries ((Nat.unpair (m / 7)).1 :: ctx) (Nat.unpair (m / 7)).2
        else if _h₂ : m % 7 = 2 then
          tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).1 ++ tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).2
        else if _h₆ : m % 7 = 6 then
          tyEntries ctx (Nat.unpair (m / 7)).1 ++ tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).1 ++
            tyEntries ctx (Nat.unpair (Nat.unpair (m / 7)).2).2
        else []), e ∈ tt := fun e he => hsub' e (List.mem_cons_of_mem _ he)
    split_ifs at he hsubTail with h₁ h₂ h₆
    · exact ih _ (unpair_right_lt (by omega)) _ hsubTail e he
    · rcases List.mem_append.mp he with he | he
      · exact ih _ (unpair_rl_lt (by omega)) _ (fun e h => hsubTail e (List.mem_append_left _ h)) e he
      · exact ih _ (unpair_rr_lt (by omega)) _ (fun e h => hsubTail e (List.mem_append_right _ h)) e he
    · rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · exact ih _ (unpair_left_lt (by omega)) _
            (fun e h => hsubTail e (List.mem_append_left _ (List.mem_append_left _ h))) e he
        · exact ih _ (unpair_rl_lt (by omega)) _
            (fun e h => hsubTail e (List.mem_append_left _ (List.mem_append_right _ h))) e he
      · exact ih _ (unpair_rr_lt (by omega)) _ (fun e h => hsubTail e (List.mem_append_right _ h)) e he
    · simp at he

/-! ## Invalid pairs -/

/-- `(a, b)` is a pair of closed terms of the same type. -/
def ValidPair (a b : ℕ) : Prop := ∃ (τ : Ty) (M N : Tm [] τ), M.code = a ∧ N.code = b

theorem validPair_iff (a b : ℕ) :
    ValidPair a b ↔ tyres [] a ≠ 0 ∧ tyres [] b ≠ 0 ∧ tyres [] a = tyres [] b := by
  constructor
  · rintro ⟨τ, M, N, rfl, rfl⟩
    have hM := tyres_of_typed (typedAs_iff.mpr ⟨τ, M, rfl, rfl⟩ : TypedAs [] M.code τ.code)
    have hN := tyres_of_typed (typedAs_iff.mpr ⟨τ, N, rfl, rfl⟩ : TypedAs [] N.code τ.code)
    refine ⟨by omega, by omega, by rw [hM, hN]⟩
  · rintro ⟨ha, hb, hab⟩
    have hM' := typed_of_tyres ha
    rw [hab] at hM'
    obtain ⟨M, hM⟩ := hM'
    obtain ⟨N, hN⟩ := typed_of_tyres hb
    exact ⟨_, M, N, hM, hN⟩

theorem closedTy_sound {tt : List TyEntry} (hv : tyValid tt = true) {m r : ℕ}
    (h : closedTy tt m = some r) : r = tyres [] m := by
  simp only [closedTy, Option.map_eq_some_iff] at h
  obtain ⟨⟨ctx, m', r'⟩, hf, rfl⟩ := h
  have hp := List.find?_some (p := fun e : TyEntry => e.1 == [] && e.2.1 == m) hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ty_sound hv _ (List.mem_of_find?_eq_some hf)

theorem invalidPair_sound {a b : ℕ} {tt : List TyEntry} (h : invalidPair a b tt = true) :
    ¬ ValidPair a b := by
  simp only [invalidPair, Bool.and_eq_true] at h
  obtain ⟨hv, hm⟩ := h
  cases ha : closedTy tt a with
  | none => simp [ha] at hm
  | some ra =>
  cases hb : closedTy tt b with
  | none => simp [ha, hb] at hm
  | some rb =>
  simp only [ha, hb, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hm
  rw [closedTy_sound hv ha, closedTy_sound hv hb] at hm
  rw [validPair_iff]
  omega

theorem invalidPair_complete {a b : ℕ} (h : ¬ ValidPair a b) :
    ∃ tt : List TyEntry, invalidPair a b tt = true := by
  let tt := tyEntries [] a ++ tyEntries [] b
  have hv : tyValid tt = true := by
    simp only [tyValid, List.all_eq_true]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact tyEntries_ok a [] (fun e h => List.mem_append_left _ h) e he
    · exact tyEntries_ok b [] (fun e h => List.mem_append_right _ h) e he
  have hc : ∀ m, (m = a ∨ m = b) → closedTy tt m = some (tyres [] m) := by
    intro m hm
    have hmem : ([], m, tyres [] m) ∈ tt := by
      rcases hm with rfl | rfl
      · exact List.mem_append_left _ (tyEntries_head _ _)
      · exact List.mem_append_right _ (tyEntries_head _ _)
    unfold closedTy
    cases hf : tt.find? (fun e => e.1 == [] && e.2.1 == m) with
    | none =>
        have := List.find?_eq_none.mp hf _ hmem
        simp at this
    | some e =>
        have hp := List.find?_some (p := fun e : TyEntry => e.1 == [] && e.2.1 == m) hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        have := ty_sound hv e (List.mem_of_find?_eq_some hf)
        rw [hp.1, hp.2] at this
        simp [this]
  refine ⟨tt, ?_⟩
  simp only [invalidPair, hv, hc a (Or.inl rfl), hc b (Or.inr rfl), Bool.true_and, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  rw [validPair_iff] at h
  omega

end OR.Sieber.Check
