import OR.Sieber.Check

/-!
# Soundness of the certificate checker

A valid certificate describes Sieber's model correctly on the types it covers,
and its verdict on a pair of closed terms is equality of their denotations.
-/

set_option autoImplicit false

namespace OR.Sieber

/-! ## Decoding types -/

def Ty.decode : ℕ → Ty
  | 0 => .B
  | n + 1 => .arr (Ty.decode (Nat.unpair n).1) (Ty.decode (Nat.unpair n).2)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.unpair_left_le n)
  · exact Nat.lt_succ_of_le (Nat.unpair_right_le n)

theorem Ty.decode_code : ∀ τ : Ty, Ty.decode τ.code = τ
  | .B => by simp [Ty.code, Ty.decode]
  | .arr σ ρ => by
      rw [Ty.code, Ty.decode, Nat.unpair_pair, Ty.decode_code σ, Ty.decode_code ρ]

theorem Ty.code_decode (n : ℕ) : (Ty.decode n).code = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [Ty.decode, Ty.code]
    | succ n =>
        rw [Ty.decode, Ty.code, ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
          ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le n)), Nat.pair_unpair]

namespace Check

theorem dom_arrow (s t : ℕ) : dom (arrow s t) = s := by simp [dom, arrow, Nat.unpair_pair]
theorem cod_arrow (s t : ℕ) : cod (arrow s t) = t := by simp [cod, arrow, Nat.unpair_pair]

theorem code_arr (σ ρ : Ty) : (σ ⇒ ρ).code = arrow σ.code ρ.code := rfl

theorem dom_code (σ ρ : Ty) : dom (σ ⇒ ρ).code = σ.code := dom_arrow _ _
theorem cod_code (σ ρ : Ty) : cod (σ ⇒ ρ).code = ρ.code := cod_arrow _ _

theorem decode_pos {c : ℕ} (hc : c ≠ 0) : Ty.decode c = Ty.decode (dom c) ⇒ Ty.decode (cod c) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  simp [Ty.decode, dom, cod]

theorem dom_lt {c : ℕ} (hc : c ≠ 0) : dom c < c := by
  have := Nat.unpair_left_le (c - 1); simp only [dom]; omega

theorem cod_lt {c : ℕ} (hc : c ≠ 0) : cod c < c := by
  have := Nat.unpair_right_le (c - 1); simp only [cod]; omega

/-! ## Ground values -/

def val : ℕ → Val
  | 1 => .tt
  | 2 => .ff
  | _ => .bot

theorem val_injective {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : val a = val b) : a = b := by
  interval_cases a <;> interval_cases b <;> first | rfl | cases h

theorem val_eq_bot {a : ℕ} (ha : a < 3) : val a = .bot ↔ a = 0 := by
  interval_cases a <;> simp [val]

theorem val_ite (c a b : ℕ) : val (ite c a b) = Val.ite (val c) (val a) (val b) := by
  unfold ite
  split_ifs with h1 h2
  · subst h1; rfl
  · subst h2; rfl
  · rcases c with _ | _ | _ | c
    · rfl
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rfl


/-! ## Enumeration -/

theorem mem_tuples {n : ℕ} : ∀ {w : ℕ} {u : List ℕ}, u ∈ tuples n w ↔ u.length = w ∧ ∀ x ∈ u, x < n
  | 0, u => by
      simp only [tuples, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | w + 1, u => by
      simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        obtain ⟨hl, hlt⟩ := mem_tuples.mp ht
        refine ⟨by simp [hl], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hlt y hy
      · rintro ⟨hl, hlt⟩
        cases u with
        | nil => simp at hl
        | cons x t =>
            refine ⟨t, mem_tuples.mpr ⟨by simpa using hl, fun y hy => hlt y (by simp [hy])⟩, x,
              hlt x (by simp), rfl⟩

/-! ## Tests -/

def toFin (w : ℕ) (l : List ℕ) : Finset (Fin w) :=
  (l.filterMap fun i => if h : i < w then some ⟨i, h⟩ else none).toFinset

theorem mem_toFin {w : ℕ} {l : List ℕ} (_hl : ∀ i ∈ l, i < w) {i : Fin w} : i ∈ toFin w l ↔ i.1 ∈ l := by
  simp only [toFin, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, hji⟩
    split_ifs at hji with h
    cases hji
    exact hj
  · intro hi
    exact ⟨i.1, hi, by simp [i.2]⟩

def toTest (w : ℕ) (d : List (List ℕ × List ℕ)) : Test w :=
  (d.map fun p => (toFin w p.1, toFin w p.2)).toFinset

/-- The ground tuple denoted by a list of value codes. -/
def gtuple (w : ℕ) (u : List ℕ) : Fin w → Val := fun i => val (u.getD i 0)

theorem holds_iff {w : ℕ} {d : List (List ℕ × List ℕ)}
    (hd : ∀ p ∈ d, (∀ i ∈ p.1, i < w) ∧ (∀ i ∈ p.2, i < w))
    {u : List ℕ} (hu : u ∈ tuples 3 w) :
    holds d u = true ↔ (toTest w d).holds (gtuple w u) := by
  obtain ⟨hlen, hlt⟩ := mem_tuples.mp hu
  have hval : ∀ i < w, u.getD i 0 < 3 := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hlt _ (List.getElem_mem _)
  simp only [holds, List.all_eq_true, Test.holds, toTest, List.mem_toFinset, List.mem_map]
  constructor
  · rintro h p ⟨q, hq, rfl⟩ hsub
    obtain ⟨h1, h2⟩ := hd q hq
    have hq' := h q hq
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false, List.contains_iff_mem,
      List.any_eq_true, beq_iff_eq, List.all_eq_true] at hq'
    rcases hq' with (⟨i, hi, hni⟩ | ⟨i, hi, hi0⟩) | hc
    · exact absurd ((mem_toFin h2 (i := ⟨i, h1 i hi⟩)).mp (hsub ((mem_toFin h1 (i := ⟨i, h1 i hi⟩)).mpr hi)))
        (by simpa using hni)
    · exact Or.inl ⟨⟨i, h1 i hi⟩, (mem_toFin h1).mpr hi, by
        simp only [gtuple]; exact (val_eq_bot (hval i (h1 i hi))).mpr hi0⟩
    · exact Or.inr fun i hi j hj => by
        simp only [gtuple]
        rw [hc _ ((mem_toFin h2).mp hi) _ ((mem_toFin h2).mp hj)]
  · intro h q hq
    obtain ⟨h1, h2⟩ := hd q hq
    have hq' := h _ ⟨q, hq, rfl⟩
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false, List.contains_iff_mem,
      List.any_eq_true, beq_iff_eq, List.all_eq_true]
    by_cases hsub : ∀ i ∈ q.1, i ∈ q.2
    · have hsub' : toFin w q.1 ⊆ toFin w q.2 := fun i hi =>
        (mem_toFin h2).mpr (hsub _ ((mem_toFin h1).mp hi))
      rcases hq' hsub' with ⟨i, hi, hi0⟩ | hc
      · exact Or.inl (Or.inr ⟨i.1, (mem_toFin h1).mp hi,
          (val_eq_bot (hval i.1 i.2)).mp hi0⟩)
      · exact Or.inr fun i hi j hj => val_injective (hval i (h2 i hi)) (hval j (h2 j hj))
          (hc ⟨i, h2 i hi⟩ ((mem_toFin h2).mpr hi) ⟨j, h2 j hj⟩ ((mem_toFin h2).mpr hj))
    · push_neg at hsub
      obtain ⟨i, hi, hni⟩ := hsub
      exact Or.inl (Or.inl ⟨i, hi, by simpa using hni⟩)

/-! ## Decoding certificate indices -/

/-- A closed term inhabiting each type. -/
def botTm : (Γ : Ctx) → (τ : Ty) → Tm Γ τ
  | _, .B => .bot
  | Γ, .arr σ ρ => .lam (botTm (σ :: Γ) ρ)

open Classical in
/-- The element of Sieber's model denoted by index `i` at type `τ`. -/
noncomputable def dec (tys : List TyTab) : (τ : Ty) → ℕ → SieberBool τ
  | .B, i => (val i : Val)
  | .arr σ ρ, i =>
      if h : ∃ f : SieberBool (σ ⇒ ρ), ∀ a < size tys σ.code,
          f.1 (dec tys σ a) = dec tys ρ (app tys (σ ⇒ ρ).code i a)
      then Classical.choose h else (botTm [] _).den

noncomputable def decEnv (tys : List TyTab) : (Γ : Ctx) → List ℕ → Env Γ
  | [], _ => PUnit.unit
  | σ :: Γ, env => (decEnv tys Γ env.tail, dec tys σ (env.getD 0 0))

theorem dec_spec {tys : List TyTab} {σ ρ : Ty} {i : ℕ}
    (h : ∃ f : SieberBool (σ ⇒ ρ), ∀ a < size tys σ.code,
      f.1 (dec tys σ a) = dec tys ρ (app tys (σ ⇒ ρ).code i a)) :
    ∀ a < size tys σ.code, (dec tys (σ ⇒ ρ) i).1 (dec tys σ a) = dec tys ρ (app tys (σ ⇒ ρ).code i a) := by
  have : dec tys (σ ⇒ ρ) i = Classical.choose h := by
    rw [dec]; exact dif_pos h
  rw [this]
  exact Classical.choose_spec h


/-! ## Good types -/

/-- `dec` is a bijection between indices and the carrier at `τ`. -/
structure Good (tys : List TyTab) (τ : Ty) : Prop where
  surj : ∀ x : SieberBool τ, ∃ i < size tys τ.code, dec tys τ i = x
  inj : ∀ i j, i < size tys τ.code → j < size tys τ.code → dec tys τ i = dec tys τ j → i = j

/-- `dec` matches the tables under application. -/
def GoodApp (tys : List TyTab) : Ty → Prop
  | .B => True
  | .arr σ ρ => ∀ i < size tys (σ ⇒ ρ).code, ∀ a < size tys σ.code,
      (dec tys (σ ⇒ ρ) i).1 (dec tys σ a) = dec tys ρ (app tys (σ ⇒ ρ).code i a)

theorem good_B (tys : List TyTab) : Good tys .B where
  surj x := by
    change Val at x
    cases x
    · exact ⟨0, by simp [size, Ty.code], rfl⟩
    · exact ⟨1, by simp [size, Ty.code], rfl⟩
    · exact ⟨2, by simp [size, Ty.code], rfl⟩
  inj i j hi hj h := by
    simp only [size, Ty.code, if_true] at hi hj
    exact val_injective hi hj h

theorem Good.size_pos {tys : List TyTab} {τ : Ty} (h : Good tys τ) : 0 < size tys τ.code := by
  obtain ⟨i, hi, -⟩ := h.surj (botTm [] τ).den
  omega

/-! ## Variables and environments -/

theorem getD_tail (env : List ℕ) (k : ℕ) : env.tail.getD k 0 = env.getD (k + 1) 0 := by
  cases env <;> simp

theorem var_exists (tys : List TyTab) : ∀ (Γ : Ctx) (k : ℕ) (hk : k < Γ.length),
    ∃ x : Var Γ (Γ.get ⟨k, hk⟩), x.code = k ∧
      ∀ env : List ℕ, x.sem.1 (decEnv tys Γ env) = dec tys (Γ.get ⟨k, hk⟩) (env.getD k 0)
  | [], _, hk => absurd hk (by simp)
  | σ :: Γ, 0, _ => ⟨.vz, rfl, fun env => rfl⟩
  | σ :: Γ, k + 1, hk => by
      obtain ⟨x, hx, hsem⟩ := var_exists tys Γ k (by simpa using hk)
      refine ⟨.vs x, by simp [Var.code, hx], fun env => ?_⟩
      have := hsem env.tail
      rw [getD_tail] at this
      exact this

theorem decode_map_code (Γ : Ctx) : (Γ.map Ty.code).map Ty.decode = Γ := by
  simp [Function.comp_def, Ty.decode_code]

/-! ## Soundness of traces -/

def covered (tys : List TyTab) (c : ℕ) : Prop := c = 0 ∨ (tys.any fun e => e.1 == c) = true

theorem covered_of_size {tys : List TyTab} {c v : ℕ} (h : v < size tys c) : covered tys c := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    simp only [size, hc, if_false, tabs] at h
    cases hf : tys.find? (fun e => e.1 == c) with
    | none => simp [hf] at h
    | some e =>
        simp only [List.any_eq_true]
        exact ⟨e, List.mem_of_find?_eq_some hf, List.find?_some (p := fun e : TyTab => e.1 == c) hf⟩

theorem unpair_left_lt {m : ℕ} (hm : m % 7 ≠ 0) : (Nat.unpair (m / 7)).1 < m := by
  have := Nat.unpair_left_le (m / 7); omega

theorem unpair_right_lt {m : ℕ} (hm : m % 7 ≠ 0) : (Nat.unpair (m / 7)).2 < m := by
  have := Nat.unpair_right_le (m / 7); omega

theorem unpair_rl_lt {m : ℕ} (hm : m % 7 ≠ 0) : (Nat.unpair (Nat.unpair (m / 7)).2).1 < m := by
  have := Nat.unpair_left_le (Nat.unpair (m / 7)).2; have := Nat.unpair_right_le (m / 7); omega

theorem unpair_rr_lt {m : ℕ} (hm : m % 7 ≠ 0) : (Nat.unpair (Nat.unpair (m / 7)).2).2 < m := by
  have := Nat.unpair_right_le (Nat.unpair (m / 7)).2; have := Nat.unpair_right_le (m / 7); omega

theorem arrow_dom_cod {c : ℕ} (hc : c ≠ 0) : arrow (dom c) (cod c) = c := by
  simp only [arrow, dom, cod, Nat.pair_unpair]; omega


theorem Ty.decode_zero : Ty.decode 0 = .B := by rw [Ty.decode]

theorem decode_arrow (s t : ℕ) : Ty.decode (arrow s t) = (Ty.decode s ⇒ Ty.decode t) := by
  rw [decode_pos (by simp [arrow]), dom_arrow, cod_arrow]

theorem child_of_any {trace : List Entry} {ctx : List ℕ} {m : ℕ} {env : List ℕ} {β : ℕ}
    {p : ℕ → ℕ → Bool}
    (h : (trace.any fun e' => e'.1 == ctx && e'.2.1 == m && e'.2.2.1 == env &&
      e'.2.2.2.2.2 == β && p e'.2.2.2.1 e'.2.2.2.2.1) = true) :
    ∃ τ' v', (ctx, m, env, τ', v', β) ∈ trace ∧ p τ' v' = true := by
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨c', m', env', τ', v', β'⟩, he, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hp⟩⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  exact ⟨τ', v', he, hp⟩

theorem any_eq_entry {trace : List Entry} {x : Entry} (h : (trace.any fun e' => e' == x) = true) :
    x ∈ trace := by
  simp only [List.any_eq_true, beq_iff_eq] at h
  obtain ⟨e', he', rfl⟩ := h
  exact he'

theorem entryOK_general {tys : List TyTab} {trace : List Entry} {ctx : List ℕ} {m : ℕ}
    {env : List ℕ} {τc v β : ℕ} (h : entryOK tys trace (ctx, m, env, τc, v, β) = true) :
    env.length = ctx.length ∧ (∀ k < ctx.length, env.getD k 0 < size tys (ctx.getD k 0)) ∧
      v < size tys τc ∧ (β = 0 ∨ (τc < β ∧ ∀ c ∈ ctx, c < β)) := by
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- Soundness of a trace: a valid entry at level `β` (using only good types) is the
code of a term whose denotation, in the decoded environment, is the decoded value. -/
theorem trace_sound {tys : List TyTab} {trace : List Entry}
    (hT : ∀ e ∈ trace, entryOK tys trace e = true)
    (hcov : ∀ c, covered tys c → c ≠ 0 → covered tys (dom c) ∧ covered tys (cod c))
    (β : ℕ)
    (hG : ∀ τ : Ty, (β = 0 ∨ τ.code < β) → covered tys τ.code → Good tys τ ∧ GoodApp tys τ) :
    ∀ (m : ℕ) (e : Entry), e ∈ trace → e.2.1 = m → e.2.2.2.2.2 = β →
      ∃ M : Tm (e.1.map Ty.decode) (Ty.decode e.2.2.2.1), M.code = m ∧
        M.sem.1 (decEnv tys _ e.2.2.1) = dec tys _ e.2.2.2.2.1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rintro ⟨ctx, m', env, τc, v, β'⟩ he hm hβ
  simp only at hm hβ
  subst hm hβ
  have hok := hT _ he
  obtain ⟨hlen, henv, hv, hlev⟩ := entryOK_general hok
  have hlev' : β' = 0 ∨ τc < β' := hlev.imp id (fun h => h.1)
  set q := m' / 7 with hq
  have hmq : m' = 7 * q + m' % 7 := (Nat.div_add_mod m' 7).symm
  have hr : m' % 7 < 7 := Nat.mod_lt _ (by norm_num)
  simp only [entryOK] at hok
  show ∃ M : Tm (ctx.map Ty.decode) (Ty.decode τc), M.code = m' ∧
    M.sem.1 (decEnv tys _ env) = dec tys _ v
  -- the good types available at this level
  have hGτ : ∀ c, covered tys c → (β' = 0 ∨ c < β') →
      Good tys (Ty.decode c) ∧ GoodApp tys (Ty.decode c) := fun c hc hl =>
    hG _ (by rw [Ty.code_decode]; exact hl) (by rw [Ty.code_decode]; exact hc)
  interval_cases hmod : m' % 7
  · -- variable
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨-, ⟨hqlen, hτ⟩, hveq⟩ := hok
    have hk : q < (ctx.map Ty.decode).length := by simpa using hqlen
    obtain ⟨x, hx, hsem⟩ := var_exists tys (ctx.map Ty.decode) q hk
    have hty : (ctx.map Ty.decode).get ⟨q, hk⟩ = Ty.decode τc := by
      rw [List.get_eq_getElem, List.getElem_map, hτ, List.getD_eq_getElem _ _ hqlen]
    rw [← hty]
    refine ⟨.var x, by simp only [Tm.code, hx]; omega, ?_⟩
    simp only [Tm.sem]
    rw [hsem env, hveq]
  · -- abstraction
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
      List.mem_range] at hok
    obtain ⟨-, ⟨hτ0, hds⟩, hch⟩ := hok
    set s := (Nat.unpair q).1 with hs
    set body := (Nat.unpair q).2 with hbody
    have hcovτ := covered_of_size hv
    obtain ⟨-, hGAτ⟩ := hGτ τc hcovτ hlev'
    have hcovs := (hcov τc hcovτ hτ0).1
    have hlevs : β' = 0 ∨ dom τc < β' := hlev'.imp id (fun h => lt_trans (dom_lt hτ0) h)
    obtain ⟨hGs, -⟩ := hGτ (dom τc) hcovs hlevs
    have hpos := hGs.size_pos
    rw [Ty.code_decode, hds] at hpos
    rw [decode_pos hτ0] at hGAτ ⊢
    rw [hds] at hGAτ hGs ⊢
    have hchild : ∀ a < size tys s, ∃ Ma : Tm (Ty.decode s :: ctx.map Ty.decode) (Ty.decode (cod τc)),
        Ma.code = body ∧ Ma.sem.1 (decEnv tys _ (a :: env)) =
          dec tys _ (((tabs tys τc).getD v []).getD a 0) := fun a ha =>
      ih body (unpair_right_lt (by rw [hmod]; norm_num)) _ (any_eq_entry (hch a ha)) rfl rfl
    obtain ⟨M0, hM0, -⟩ := hchild 0 hpos
    refine ⟨.lam M0, ?_, ?_⟩
    · simp only [Tm.code, Ty.code_decode, hM0, hs, hbody, Nat.pair_unpair]; omega
    · apply Model.arr_ext
      intro x
      obtain ⟨a, ha, rfl⟩ := hGs.surj x
      rw [Ty.code_decode] at ha
      obtain ⟨Ma, hMa, hsem⟩ := hchild a ha
      obtain ⟨-, hMaM0⟩ := Tm.code_inj Ma M0 (hMa.trans hM0.symm)
      rw [eq_of_heq hMaM0] at hsem
      have hcode : (Ty.decode s ⇒ Ty.decode (cod τc)).code = τc := by
        rw [code_arr, Ty.code_decode, Ty.code_decode, ← hds, arrow_dom_cod hτ0]
      have key := hGAτ v (by rw [hcode]; exact hv) a (by rw [Ty.code_decode]; exact ha)
      rw [hcode] at key
      simp only [Tm.sem]
      rw [key]
      exact hsem
  · -- application
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨c₁, m₁, env₁, τ₁, v₁, β₁⟩, he₁, hp₁⟩ := List.any_eq_true.mp hok.2
    simp only [Bool.and_eq_true, beq_iff_eq] at hp₁
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hτ₁, hp₂⟩ := hp₁
    obtain ⟨⟨c₂, m₂, env₂, τ₂, v₂, β₂⟩, he₂, hp₃⟩ := List.any_eq_true.mp hp₂
    simp only [Bool.and_eq_true, beq_iff_eq] at hp₃
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hτ₂, hvapp⟩ := hp₃
    have hlt := unpair_rl_lt (m := m') (by rw [hmod]; norm_num)
    have hlt' := unpair_rr_lt (m := m') (by rw [hmod]; norm_num)
    obtain ⟨-, -, hv₁, hlev₁⟩ := entryOK_general (hT _ he₁)
    obtain ⟨-, -, hv₂, -⟩ := entryOK_general (hT _ he₂)
    have h1 := ih _ hlt _ he₁ rfl rfl
    have h2 := ih _ hlt' _ he₂ rfl rfl
    simp only at h1 h2
    obtain ⟨-, hGA₁⟩ := hGτ τ₁ (covered_of_size hv₁) (hlev₁.imp id (fun h => h.1))
    rw [hτ₁, decode_arrow] at h1 hGA₁
    rw [hτ₂] at h2
    obtain ⟨M₁, hM₁, hsem₁⟩ := h1
    obtain ⟨M₂, hM₂, hsem₂⟩ := h2
    refine ⟨.app M₁ M₂, ?_, ?_⟩
    · simp only [Tm.code, Ty.code_decode, hM₁, hM₂, Nat.pair_unpair]; omega
    · have hcode : (Ty.decode (Nat.unpair q).1 ⇒ Ty.decode τc).code = arrow (Nat.unpair q).1 τc := by
        rw [code_arr, Ty.code_decode, Ty.code_decode]
      rw [hτ₁] at hv₁ hvapp
      rw [hτ₂] at hv₂
      have key := hGA₁ v₁ (by rw [hcode]; exact hv₁) v₂ (by rw [Ty.code_decode]; exact hv₂)
      rw [hcode] at key
      simp only [Tm.sem]
      rw [hsem₁, hsem₂, key, hvapp]
  · -- tt
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨-, ⟨hq0, rfl⟩, rfl⟩ := hok
    rw [Ty.decode_zero]
    exact ⟨.tt, by simp only [Tm.code]; omega, by simp only [Tm.sem, constSem]; rfl⟩
  · -- ff
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨-, ⟨hq0, rfl⟩, rfl⟩ := hok
    rw [Ty.decode_zero]
    exact ⟨.ff, by simp only [Tm.code]; omega, by simp only [Tm.sem, constSem]; rfl⟩
  · -- bot
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨-, ⟨hq0, rfl⟩, rfl⟩ := hok
    rw [Ty.decode_zero]
    exact ⟨.bot, by simp only [Tm.code]; omega, by simp only [Tm.sem, constSem]; rfl⟩
  · -- conditional
    simp only [Bool.and_eq_true] at hok
    obtain ⟨-, hτ0, hpc⟩ := hok
    simp only [beq_iff_eq] at hτ0
    subst hτ0
    obtain ⟨⟨c₀, m₀, env₀, τ₀, v₀, β₀⟩, he₀, hp₀⟩ := List.any_eq_true.mp hpc
    simp only [Bool.and_eq_true, beq_iff_eq] at hp₀
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl, hp₁⟩ := hp₀
    obtain ⟨⟨c₁, m₁, env₁, τ₁, v₁, β₁⟩, he₁, hp₁'⟩ := List.any_eq_true.mp hp₁
    simp only [Bool.and_eq_true, beq_iff_eq] at hp₁'
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl, hp₂⟩ := hp₁'
    obtain ⟨⟨c₂, m₂, env₂, τ₂, v₂, β₂⟩, he₂, hp₂'⟩ := List.any_eq_true.mp hp₂
    simp only [Bool.and_eq_true, beq_iff_eq] at hp₂'
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl, hvite⟩ := hp₂'
    have h0 := ih _ (unpair_left_lt (m := m') (by rw [hmod]; norm_num)) _ he₀ rfl rfl
    have h1 := ih _ (unpair_rl_lt (m := m') (by rw [hmod]; norm_num)) _ he₁ rfl rfl
    have h2 := ih _ (unpair_rr_lt (m := m') (by rw [hmod]; norm_num)) _ he₂ rfl rfl
    simp only at h0 h1 h2
    rw [Ty.decode_zero] at h0 h1 h2 ⊢
    obtain ⟨M₀, hM₀, hsem₀⟩ := h0
    obtain ⟨M₁, hM₁, hsem₁⟩ := h1
    obtain ⟨M₂, hM₂, hsem₂⟩ := h2
    refine ⟨.ite M₀ M₁ M₂, ?_, ?_⟩
    · simp only [Tm.code, hM₀, hM₁, hM₂, Nat.pair_unpair]; omega
    · simp only [Tm.sem]
      rw [hsem₀, hsem₁, hsem₂, hvite]
      exact (val_ite _ _ _).symm


/-! ## Unpacking the checks -/

theorem liftSet_spec {lifts : List Lift} {c : ℕ} (h : hasLift lifts c = true) :
    ∃ e ∈ lifts, e.1 = c ∧ liftSet lifts c = e.2 := by
  cases hf : lifts.find? (fun e => e.1 == c) with
  | none =>
      simp only [hasLift, List.any_eq_true, beq_iff_eq] at h
      obtain ⟨e, he, hec⟩ := h
      have := List.find?_eq_none.mp hf e he
      simp [hec] at this
  | some e =>
      refine ⟨e, List.mem_of_find?_eq_some hf, ?_, by simp [liftSet, hf]⟩
      simpa using List.find?_some (p := fun e : Lift => e.1 == c) hf

theorem tabs_spec {tys : List TyTab} {c : ℕ} (h : (tys.any fun e => e.1 == c) = true) :
    (c, tabs tys c) ∈ tys := by
  cases hf : tys.find? (fun e => e.1 == c) with
  | none =>
      simp only [List.any_eq_true, beq_iff_eq] at h
      obtain ⟨e, he, hec⟩ := h
      have := List.find?_eq_none.mp hf e he
      simp [hec] at this
  | some e =>
      have hc : e.1 = c := by simpa using List.find?_some (p := fun e : TyTab => e.1 == c) hf
      have : e = (c, tabs tys c) := by
        rw [tabs, hf, ← hc]; rfl
      rw [← this]; exact List.mem_of_find?_eq_some hf

/-- The components of a valid rejection witness. -/
structure NegSpec (tys : List TyTab) (c : ℕ) (t : List ℕ) (w : ℕ) (d : List (List ℕ × List ℕ))
    (g : List ℕ) (lifts : List Lift) : Prop where
  hd : ∀ p ∈ d, (∀ i ∈ p.1, i < w) ∧ (∀ i ∈ p.2, i < w)
  hdom : hasLift lifts (dom c) = true
  hcod : hasLift lifts (cod c) = true
  hclo : ∀ e ∈ lifts, e.1 = 0 ∨ (hasLift lifts (dom e.1) = true ∧ hasLift lifts (cod e.1) = true)
  hsub : ∀ e ∈ lifts, ∀ u ∈ e.2, u ∈ tuples (size tys e.1) w
  hex : ∀ e ∈ lifts, ∀ u ∈ tuples (size tys e.1) w, (u ∈ e.2 ↔ cond tys w d lifts e.1 u = true)
  hg : g ∈ tuples (size tys (dom c)) w
  hgl : g ∈ liftSet lifts (dom c)
  hng : g.map (fun gi => t.getD gi 0) ∉ liftSet lifts (cod c)

theorem negSpec_of_valid {tys : List TyTab} {c : ℕ} {t : List ℕ} {w : ℕ}
    {d : List (List ℕ × List ℕ)} {g : List ℕ} {lifts : List Lift}
    (h : negValid tys (c, t, w, d, g, lifts) = true) : NegSpec tys c t w d g lifts := by
  simp only [negValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq, List.contains_iff_mem, Bool.not_eq_true', Bool.eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hd, hdom⟩, hcod⟩, hclo⟩, hsub⟩, hex⟩, hg⟩, hgl⟩, hng⟩ := h
  refine ⟨hd, hdom, hcod, hclo, hsub, fun e he u hu => ?_, hg, hgl, ?_⟩
  · have := hex e he u hu
    simp only [Bool.beq_eq_decide_eq, List.contains_iff_mem, decide_eq_true_eq] at this
    exact ⟨fun hu' => by rw [← this]; simpa using hu', fun hc => by rw [← this] at hc; simpa using hc⟩
  · intro hmem; exact hng (by simpa [List.contains_iff_mem] using hmem)


/-! ## Lifted relations -/

theorem getD_lt_of_tuples {n w : ℕ} {u : List ℕ} (hu : u ∈ tuples n w) {i : ℕ} (hi : i < w) :
    u.getD i 0 < n := by
  obtain ⟨hl, hlt⟩ := mem_tuples.mp hu
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hlt _ (List.getElem_mem _)

theorem appTuple_getD {tys : List TyTab} {w c : ℕ} {u h : List ℕ} {i : ℕ} (hi : i < w) :
    (appTuple tys w c u h).getD i 0 = app tys c (u.getD i 0) (h.getD i 0) := by
  simp [appTuple, List.getD_eq_getElem?_getD, hi]

theorem ofFn_tuples {n w : ℕ} (f : Fin w → ℕ) (hf : ∀ i, f i < n) : List.ofFn f ∈ tuples n w := by
  refine mem_tuples.mpr ⟨by simp, ?_⟩
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hf i

theorem ofFn_getD {w : ℕ} (f : Fin w → ℕ) (i : Fin w) : (List.ofFn f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD]

theorem app_lt {tys : List TyTab} {c : ℕ}
    (hshape : ∀ row ∈ tabs tys c, ∀ x ∈ row, x < size tys (cod c)) (hpos : 0 < size tys (cod c))
    {u h : ℕ} (hu : u < (tabs tys c).length) : app tys c u h < size tys (cod c) := by
  unfold app
  rw [List.getD_eq_getElem _ _ hu]
  rw [List.getD_eq_getElem?_getD]
  cases hx : ((tabs tys c)[u])[h]? with
  | none => simpa using hpos
  | some x => exact hshape _ (List.getElem_mem _) x (List.mem_of_getElem? hx)

/-- Claimed lift sets are the lifted relations of Sieber's model. -/
theorem lift_iff {tys : List TyTab} {c : ℕ} {t : List ℕ} {w : ℕ} {d : List (List ℕ × List ℕ)}
    {g : List ℕ} {lifts : List Lift} (hn : NegSpec tys c t w d g lifts) (c0 : ℕ)
    (hGall : ∀ τ : Ty, τ.code < c0 → covered tys τ.code → Good tys τ ∧ GoodApp tys τ)
    (hcov : ∀ c', covered tys c' → c' ≠ 0 → covered tys (dom c') ∧ covered tys (cod c'))
    (hshape : ∀ c', covered tys c' → c' ≠ 0 → ∀ row ∈ tabs tys c', ∀ x ∈ row, x < size tys (cod c')) :
    ∀ τ : Ty, τ.code < c0 → covered tys τ.code → hasLift lifts τ.code = true →
      ∀ u ∈ tuples (size tys τ.code) w,
        (u ∈ liftSet lifts τ.code ↔ (Model τ).rel w (toTest w d) (fun i => dec tys τ (u.getD i 0))) := by
  intro τ
  induction τ with
  | B =>
      intro _ _ hl u hu
      obtain ⟨e, he, he1, hls⟩ := liftSet_spec hl
      rw [hls, hn.hex e he u (by rwa [he1])]
      have hu3 : u ∈ tuples 3 w := by simpa [size, Ty.code] using hu
      rw [he1]
      simp only [cond, Ty.code, if_true]
      exact holds_iff hn.hd hu3
  | arr σ ρ ihσ ihρ =>
      intro hc hcovτ hl u hu
      have hc0 : (σ ⇒ ρ).code ≠ 0 := by simp [Ty.code]
      obtain ⟨e, he, he1, hls⟩ := liftSet_spec hl
      rw [hls, hn.hex e he u (by rwa [he1])]
      have hclo := hn.hclo e he
      rw [he1] at hclo
      obtain ⟨hlσ, hlρ⟩ := hclo.resolve_left hc0
      simp only [dom_code, cod_code] at hlσ hlρ
      obtain ⟨hcovσ, hcovρ⟩ := hcov _ hcovτ hc0
      simp only [dom_code, cod_code] at hcovσ hcovρ
      have hσlt : σ.code < c0 := lt_trans (by rw [← dom_code σ ρ]; exact dom_lt hc0) hc
      have hρlt : ρ.code < c0 := lt_trans (by rw [← cod_code σ ρ]; exact cod_lt hc0) hc
      obtain ⟨hGσ, -⟩ := hGall σ hσlt hcovσ
      obtain ⟨hGρ, -⟩ := hGall ρ hρlt hcovρ
      obtain ⟨-, hGA⟩ := hGall _ hc hcovτ
      have hpos : 0 < size tys (cod (σ ⇒ ρ).code) := by rw [cod_code]; exact hGρ.size_pos
      have hsize : size tys (σ ⇒ ρ).code = (tabs tys (σ ⇒ ρ).code).length := by
        simp [size, hc0]
      have happ_lt : ∀ i < w, ∀ hh : List ℕ,
          app tys (σ ⇒ ρ).code (u.getD i 0) (hh.getD i 0) < size tys ρ.code := fun i hi hh => by
        rw [← cod_code σ ρ]
        exact app_lt (hshape _ hcovτ hc0) hpos (by rw [← hsize]; exact getD_lt_of_tuples hu hi)
      have happT : ∀ hh : List ℕ, appTuple tys w (σ ⇒ ρ).code u hh ∈ tuples (size tys ρ.code) w := by
        intro hh
        refine mem_tuples.mpr ⟨by simp [appTuple], ?_⟩
        intro x hx
        simp only [appTuple, List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact happ_lt i hi hh
      have hdecapp : ∀ i < w, ∀ hh : List ℕ, hh.getD i 0 < size tys σ.code →
          dec tys ρ ((appTuple tys w (σ ⇒ ρ).code u hh).getD i 0) =
            (dec tys (σ ⇒ ρ) (u.getD i 0)).1 (dec tys σ (hh.getD i 0)) := fun i hi hh hhi => by
        rw [appTuple_getD hi]
        exact (hGA _ (getD_lt_of_tuples hu hi) _ hhi).symm
      rw [he1]
      simp only [cond, hc0, if_false, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq,
        dom_code, cod_code]
      constructor
      · intro hcond G hG
        have : ∀ i : Fin w, ∃ k, k < size tys σ.code ∧ dec tys σ k = G i := fun i => hGσ.surj (G i)
        choose f hf hfG using this
        have hh := ofFn_tuples f hf
        have hrel : (Model σ).rel w (toTest w d) (fun i => dec tys σ ((List.ofFn f).getD i 0)) := by
          have : (fun i : Fin w => dec tys σ ((List.ofFn f).getD i 0)) = G := by
            funext i; rw [ofFn_getD, hfG]
          rw [this]; exact hG
        have hmem := (ihσ hσlt hcovσ hlσ _ hh).mpr hrel
        have hres := (ihρ hρlt hcovρ hlρ _ (happT _)).mp (hcond _ hmem)
        have : (fun i : Fin w => dec tys ρ ((appTuple tys w (σ ⇒ ρ).code u (List.ofFn f)).getD i 0)) =
            (fun i : Fin w => (dec tys (σ ⇒ ρ) (u.getD i 0)).1 (G i)) := by
          funext i
          rw [hdecapp i i.2 _ (by rw [ofFn_getD]; exact hf i), ofFn_getD, hfG]
        rw [this] at hres
        exact hres
      · intro hrel hh hhmem
        obtain ⟨eσ, heσ, heσ1, hlsσ⟩ := liftSet_spec hlσ
        have hht : hh ∈ tuples (size tys σ.code) w := by
          have := hn.hsub eσ heσ hh (by rw [← hlsσ]; exact hhmem)
          rwa [heσ1] at this
        have hrσ := (ihσ hσlt hcovσ hlσ _ hht).mp hhmem
        have hrρ := hrel _ hrσ
        apply (ihρ hρlt hcovρ hlρ _ (happT _)).mpr
        have : (fun i : Fin w => dec tys ρ ((appTuple tys w (σ ⇒ ρ).code u hh).getD i 0)) =
            (fun i : Fin w => (dec tys (σ ⇒ ρ) (u.getD i 0)).1 (dec tys σ (hh.getD i 0))) := by
          funext i
          exact hdecapp i i.2 _ (getD_lt_of_tuples hht i.2)
        rw [this]
        exact hrρ


/-! ## Carriers -/

structure CarrierSpec (cert : Cert) (c : ℕ) (ts : List (List ℕ)) : Prop where
  hc : c ≠ 0
  hdom : covered cert.1 (dom c)
  hcod : covered cert.1 (cod c)
  hshape : ∀ t ∈ ts, t.length = size cert.1 (dom c) ∧ ∀ x ∈ t, x < size cert.1 (cod c)
  hnodup : ∀ i < ts.length, ∀ j < ts.length, i = j ∨ ts.getD i [] ≠ ts.getD j []
  hwlen : (witnesses cert.2.1 c).length = ts.length
  hwit : ∀ i < ts.length, witOK cert.1 cert.2.2.1 c (ts.getD i []) ((witnesses cert.2.1 c).getD i 0) = true
  hcover : ∀ t ∈ tuples (size cert.1 (cod c)) (size cert.1 (dom c)),
    t ∈ ts ∨ ∃ n ∈ cert.2.2.2, n.1 = c ∧ n.2.1 = t ∧ negValid cert.1 n = true

theorem carrierSpec_of {cert : Cert} {c : ℕ} {ts : List (List ℕ)} (h : carrierOK cert (c, ts) = true) :
    CarrierSpec cert c ts := by
  obtain ⟨tys, wit, trace, negs⟩ := cert
  simp only [carrierOK, carrierOK.hasTabs, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
    beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range, List.contains_iff_mem,
    List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, hdom⟩, hcod⟩, hshape⟩, hnodup⟩, hwlen⟩, hwit⟩, hcover⟩ := h
  refine ⟨hc, ?_, ?_, hshape, ?_, hwlen, hwit, ?_⟩
  · rcases hdom with h | ⟨e, he, he1⟩
    · exact Or.inl h
    · exact Or.inr (by simp only [List.any_eq_true, beq_iff_eq]; exact ⟨e, he, he1⟩)
  · rcases hcod with h | ⟨e, he, he1⟩
    · exact Or.inl h
    · exact Or.inr (by simp only [List.any_eq_true, beq_iff_eq]; exact ⟨e, he, he1⟩)
  · intro i hi j hj
    rcases hnodup i hi j hj with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro t ht
    rcases hcover t ht with h | ⟨n, hn, ⟨⟨h1, h2⟩, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hn, h1, h2, h3⟩

theorem valid_spec {cert : Cert} (h : valid cert = true) :
    (∀ e ∈ cert.1, carrierOK cert e = true) ∧ (∀ e ∈ cert.2.2.1, entryOK cert.1 cert.2.2.1 e = true) := by
  obtain ⟨tys, wit, trace, negs⟩ := cert
  simp only [valid, Bool.and_eq_true, List.all_eq_true] at h
  exact h


theorem size_arr {tys : List TyTab} {c : ℕ} (hc : c ≠ 0) : size tys c = (tabs tys c).length := by
  simp [size, hc]

theorem list_eq_of_getD {l₁ l₂ : List ℕ} (h₁ : l₁.length = l₂.length)
    (h : ∀ a < l₁.length, l₁.getD a 0 = l₂.getD a 0) : l₁ = l₂ := by
  apply List.ext_getElem h₁
  intro a ha₁ ha₂
  have := h a ha₁
  rwa [List.getD_eq_getElem _ _ ha₁, List.getD_eq_getElem _ _ ha₂] at this

/-- **Main lemma.** For a valid certificate, `dec` is a bijection onto Sieber's carrier
at every covered type, and agrees with the tables under application. -/
theorem good_all {cert : Cert} (hv : valid cert = true) :
    ∀ τ : Ty, covered cert.1 τ.code → Good cert.1 τ ∧ GoodApp cert.1 τ := by
  obtain ⟨hC, hT⟩ := valid_spec hv
  have hspec : ∀ c, covered cert.1 c → c ≠ 0 → CarrierSpec cert c (tabs cert.1 c) :=
    fun c hc hc0 => carrierSpec_of (hC _ (tabs_spec (hc.resolve_left hc0)))
  have hcov : ∀ c, covered cert.1 c → c ≠ 0 → covered cert.1 (dom c) ∧ covered cert.1 (cod c) :=
    fun c hc hc0 => ⟨(hspec c hc hc0).hdom, (hspec c hc hc0).hcod⟩
  have hshape : ∀ c', covered cert.1 c' → c' ≠ 0 →
      ∀ row ∈ tabs cert.1 c', ∀ x ∈ row, x < size cert.1 (cod c') :=
    fun c' hc hc0 row hr x hx => ((hspec c' hc hc0).hshape row hr).2 x hx
  suffices H : ∀ n, ∀ τ : Ty, τ.code = n → covered cert.1 τ.code → Good cert.1 τ ∧ GoodApp cert.1 τ from
    fun τ => H _ τ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro τ hτn hcovτ
  cases τ with
  | B => exact ⟨good_B _, trivial⟩
  | arr σ ρ =>
  have hc0 : (σ ⇒ ρ).code ≠ 0 := by simp [Ty.code]
  have hG' : ∀ τ' : Ty, τ'.code < (σ ⇒ ρ).code → covered cert.1 τ'.code →
      Good cert.1 τ' ∧ GoodApp cert.1 τ' := fun τ' hlt hc => ih _ (hτn ▸ hlt) τ' rfl hc
  have sp := hspec _ hcovτ hc0
  have hσlt : σ.code < (σ ⇒ ρ).code := by rw [← dom_code σ ρ]; exact dom_lt hc0
  have hρlt : ρ.code < (σ ⇒ ρ).code := by rw [← cod_code σ ρ]; exact cod_lt hc0
  have hcovσ : covered cert.1 σ.code := by rw [← dom_code σ ρ]; exact sp.hdom
  have hcovρ : covered cert.1 ρ.code := by rw [← cod_code σ ρ]; exact sp.hcod
  obtain ⟨hGσ, -⟩ := hG' σ hσlt hcovσ
  obtain ⟨hGρ, -⟩ := hG' ρ hρlt hcovρ
  have hsize := size_arr (tys := cert.1) hc0
  -- application, from the acceptance witnesses
  have hApp : GoodApp cert.1 (σ ⇒ ρ) := by
    intro i hi a ha
    apply dec_spec ?_ a ha
    have hi' : i < (tabs cert.1 (σ ⇒ ρ).code).length := by rwa [← hsize]
    have hw := sp.hwit i hi'
    simp only [witOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hw
    obtain ⟨⟨hmod, hs⟩, hents⟩ := hw
    rw [dom_code] at hs
    have hentry : ∀ a' < size cert.1 σ.code, ∃ M : Tm [σ] ρ,
        M.code = (Nat.unpair ((witnesses cert.2.1 (σ ⇒ ρ).code).getD i 0 / 7)).2 ∧
        M.sem.1 (PUnit.unit, dec cert.1 σ a') =
          dec cert.1 ρ (((tabs cert.1 (σ ⇒ ρ).code).getD i []).getD a' 0) := by
      intro a' ha'
      have he := any_eq_entry (hents a' (by rw [hs]; exact ha'))
      have h := trace_sound hT hcov (σ ⇒ ρ).code
        (fun τ' hl hc => hG' τ' (hl.resolve_left hc0) hc) _ _ he rfl rfl
      simp only [List.map_cons, List.map_nil] at h
      rw [hs, Ty.decode_code, cod_code, Ty.decode_code] at h
      exact h
    obtain ⟨M₀, hM₀, -⟩ := hentry 0 hGσ.size_pos
    refine ⟨(Tm.lam M₀).den, fun a' ha' => ?_⟩
    obtain ⟨Ma, hMa, hsem⟩ := hentry a' ha'
    obtain ⟨-, hMaM₀⟩ := Tm.code_inj Ma M₀ (hMa.trans hM₀.symm)
    rw [eq_of_heq hMaM₀] at hsem
    simp only [Tm.den, Tm.sem]
    exact hsem
  -- injectivity, from the absence of duplicate tables
  have hinj : ∀ i j, i < size cert.1 (σ ⇒ ρ).code → j < size cert.1 (σ ⇒ ρ).code →
      dec cert.1 (σ ⇒ ρ) i = dec cert.1 (σ ⇒ ρ) j → i = j := by
    intro i j hi hj hij
    have hi' : i < (tabs cert.1 (σ ⇒ ρ).code).length := by rwa [← hsize]
    have hj' : j < (tabs cert.1 (σ ⇒ ρ).code).length := by rwa [← hsize]
    have hpos : 0 < size cert.1 (cod (σ ⇒ ρ).code) := by rw [cod_code]; exact hGρ.size_pos
    have hrow : ∀ k < (tabs cert.1 (σ ⇒ ρ).code).length,
        ((tabs cert.1 (σ ⇒ ρ).code).getD k []).length = size cert.1 σ.code := fun k hk => by
      rw [← dom_code σ ρ]
      exact (sp.hshape _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _)).1
    have happ : ∀ a < size cert.1 σ.code,
        app cert.1 (σ ⇒ ρ).code i a = app cert.1 (σ ⇒ ρ).code j a := by
      intro a ha
      have h₁ := hApp i hi a ha
      have h₂ := hApp j hj a ha
      rw [hij] at h₁
      have hlt : ∀ k < (tabs cert.1 (σ ⇒ ρ).code).length,
          app cert.1 (σ ⇒ ρ).code k a < size cert.1 ρ.code := fun k hk => by
        rw [← cod_code σ ρ]; exact app_lt (hshape _ hcovτ hc0) hpos hk
      exact hGρ.inj _ _ (hlt i hi') (hlt j hj') (h₁.symm.trans h₂)
    rcases sp.hnodup i hi' j hj' with h | h
    · exact h
    · exact absurd (list_eq_of_getD (by rw [hrow i hi', hrow j hj'])
        (fun a ha => happ a (by rwa [hrow i hi'] at ha))) h
  -- surjectivity, from the rejection witnesses
  have hsurj : ∀ x : SieberBool (σ ⇒ ρ), ∃ i < size cert.1 (σ ⇒ ρ).code, dec cert.1 (σ ⇒ ρ) i = x := by
    intro x
    have : ∀ a : Fin (size cert.1 σ.code), ∃ k, k < size cert.1 ρ.code ∧
        dec cert.1 ρ k = x.1 (dec cert.1 σ a) := fun a => hGρ.surj _
    choose f hf hfx using this
    have ht : List.ofFn f ∈ tuples (size cert.1 (cod (σ ⇒ ρ).code)) (size cert.1 (dom (σ ⇒ ρ).code)) := by
      rw [dom_code, cod_code]; exact ofFn_tuples f hf
    have hft : ∀ a (ha : a < size cert.1 σ.code), (List.ofFn f).getD a 0 = f ⟨a, ha⟩ := fun a ha =>
      ofFn_getD f ⟨a, ha⟩
    rcases sp.hcover _ ht with hmem | ⟨⟨c', t', w, d, g, lifts⟩, hn, hn1, hn2, hnv⟩
    · obtain ⟨i, hi, hti⟩ := List.getElem_of_mem hmem
      refine ⟨i, by rw [hsize]; exact hi, ?_⟩
      apply Model.arr_ext
      intro y
      obtain ⟨a, ha, rfl⟩ := hGσ.surj y
      rw [hApp i (by rw [hsize]; exact hi) a ha]
      simp only [app, List.getD_eq_getElem _ _ hi, hti, hft a ha, hfx]
    · simp only at hn1 hn2
      subst hn1 hn2
      have ns := negSpec_of_valid hnv
      exfalso
      have hlσ : hasLift lifts σ.code = true := by rw [← dom_code σ ρ]; exact ns.hdom
      have hlρ : hasLift lifts ρ.code = true := by rw [← cod_code σ ρ]; exact ns.hcod
      have hg : g ∈ tuples (size cert.1 σ.code) w := by rw [← dom_code σ ρ]; exact ns.hg
      have hrσ := (lift_iff ns _ hG' hcov hshape σ hσlt hcovσ hlσ g hg).mp
        (by rw [← dom_code σ ρ]; exact ns.hgl)
      have hrρ := x.2.2 w (toTest w d) _ hrσ
      have htg : g.map (fun gi => (List.ofFn f).getD gi 0) ∈ tuples (size cert.1 ρ.code) w := by
        obtain ⟨hgl, hglt⟩ := mem_tuples.mp hg
        refine mem_tuples.mpr ⟨by simp [hgl], ?_⟩
        intro y hy
        obtain ⟨gi, hgi, rfl⟩ := List.mem_map.mp hy
        rw [hft gi (hglt gi hgi)]
        exact hf _
      apply ns.hng
      rw [cod_code]
      apply (lift_iff ns _ hG' hcov hshape ρ hρlt hcovρ hlρ _ htg).mpr
      have : (fun i : Fin w => dec cert.1 ρ ((g.map fun gi => (List.ofFn f).getD gi 0).getD i 0)) =
          (fun i : Fin w => x.1 (dec cert.1 σ (g.getD i 0))) := by
        funext i
        have hgi : g.getD i 0 < size cert.1 σ.code := getD_lt_of_tuples hg i.2
        have hlen : i.1 < g.length := by rw [(mem_tuples.mp hg).1]; exact i.2
        rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map,
          ← List.getD_eq_getElem g 0 hlen, hft _ hgi, hfx]
      rw [this]
      exact hrρ
  exact ⟨⟨hsurj, hinj⟩, hApp⟩


/-! ## Verdicts -/

theorem closedValue_spec {trace : List Entry} {m τ v : ℕ} (h : closedValue trace m = some (τ, v)) :
    (([] : List ℕ), m, ([] : List ℕ), τ, v, 0) ∈ trace := by
  simp only [closedValue, Option.map_eq_some_iff] at h
  obtain ⟨⟨ctx, m', env, τ', v', β⟩, hf, heq⟩ := h
  have hp := List.find?_some (p := fun e : Entry => e.1 == [] && e.2.1 == m && e.2.2.1 == [] &&
    e.2.2.2.2.2 == 0) hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hp
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact List.mem_of_find?_eq_some hf

theorem closed_sound {cert : Cert} (hv : valid cert = true) {m τ v : ℕ}
    (h : closedValue cert.2.2.1 m = some (τ, v)) :
    ∃ M : Tm [] (Ty.decode τ), M.code = m ∧ M.den = dec cert.1 _ v ∧ v < size cert.1 τ := by
  obtain ⟨hC, hT⟩ := valid_spec hv
  have hcov : ∀ c, covered cert.1 c → c ≠ 0 → covered cert.1 (dom c) ∧ covered cert.1 (cod c) :=
    fun c hc hc0 =>
      let sp := carrierSpec_of (hC _ (tabs_spec (hc.resolve_left hc0)))
      ⟨sp.hdom, sp.hcod⟩
  have he := closedValue_spec h
  obtain ⟨-, -, hvlt, -⟩ := entryOK_general (hT _ he)
  obtain ⟨M, hM, hsem⟩ := trace_sound hT hcov 0 (fun τ' _ hc => good_all hv τ' hc) m _ he rfl rfl
  exact ⟨M, hM, hsem, hvlt⟩

/-- **Soundness of verdicts**: a verdict on `(a, b)` is a statement about two closed
terms of the same type with codes `a` and `b`: equality of their denotations. -/
theorem verdict_sound {a b : ℕ} {cert : Cert} {r : Bool} (h : verdict a b cert = some r) :
    ∃ (τ : Ty) (M N : Tm [] τ), M.code = a ∧ N.code = b ∧ (r = true ↔ M.den = N.den) := by
  unfold verdict at h
  split_ifs at h with hv
  cases ha : closedValue cert.2.2.1 a with
  | none => simp [ha] at h
  | some pa =>
  cases hb : closedValue cert.2.2.1 b with
  | none => simp [ha, hb] at h
  | some pb =>
  obtain ⟨τa, va⟩ := pa
  obtain ⟨τb, vb⟩ := pb
  simp only [ha, hb] at h
  split_ifs at h with hτ
  subst hτ
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨M, hM, hMd, hva⟩ := closed_sound hv ha
  obtain ⟨N, hN, hNd, hvb⟩ := closed_sound hv hb
  refine ⟨_, M, N, hM, hN, ?_⟩
  have hG := (good_all hv (Ty.decode τa) (by rw [Ty.code_decode]; exact covered_of_size hva)).1
  rw [hMd, hNd, beq_iff_eq]
  constructor
  · rintro rfl; rfl
  · intro hdec
    exact hG.inj _ _ (by rwa [Ty.code_decode]) (by rwa [Ty.code_decode]) hdec

end Check
end OR.Sieber
