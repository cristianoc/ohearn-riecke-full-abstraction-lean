import OR.Sieber.CheckSound
import OR.Sieber.Soundness

/-!
# Completeness of the certificate checker

If every element of Sieber's model is definable, every pair of closed terms of
the same type has a certificate whose verdict is equality of denotations.

The certificate covers all types with code at most a bound `K`, lists every
carrier (via finiteness), uses normal forms as acceptance witnesses (via
universality and normalisation), records the value of every subterm under
every environment, and takes its rejection witnesses from the definition of the
carriers.
-/

set_option autoImplicit false

namespace OR.Sieber

instance (τ : Ty) : Inhabited (SieberBool τ) := ⟨(Check.botTm [] τ).den⟩

noncomputable instance (τ : Ty) : DecidableEq (SieberBool τ) := Classical.decEq _

namespace Check

/-! ## Listing the carriers -/

open Classical in
/-- Every carrier, as a list without duplicates; ground values in the order `⊥, tt, ff`. -/
noncomputable def els : (τ : Ty) → List (SieberBool τ)
  | .B => [Val.bot, Val.tt, Val.ff]
  | .arr σ ρ =>
      haveI := finite_car (σ ⇒ ρ)
      haveI := Fintype.ofFinite (SieberBool (σ ⇒ ρ))
      (Finset.univ : Finset (SieberBool (σ ⇒ ρ))).toList

theorem els_nodup : ∀ τ : Ty, (els τ).Nodup
  | .B => by simp [els]
  | .arr _ _ => Finset.nodup_toList _

theorem mem_els : ∀ (τ : Ty) (x : SieberBool τ), x ∈ els τ
  | .B, x => by change Val at x; cases x <;> simp [els]
  | .arr _ _, x => by simp [els]

noncomputable def idx (τ : Ty) (x : SieberBool τ) : ℕ := (els τ).idxOf x

theorem idx_lt (τ : Ty) (x : SieberBool τ) : idx τ x < (els τ).length :=
  List.idxOf_lt_length_iff.mpr (mem_els τ x)

theorem getD_idx (τ : Ty) (x : SieberBool τ) : (els τ).getD (idx τ x) default = x := by
  rw [List.getD_eq_getElem _ _ (idx_lt τ x)]
  exact List.getElem_idxOf (idx_lt τ x)

theorem idx_getD (τ : Ty) {i : ℕ} (hi : i < (els τ).length) : idx τ ((els τ).getD i default) = i := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.idxOf_getElem (els_nodup τ) i hi

theorem idx_inj (τ : Ty) {x y : SieberBool τ} (h : idx τ x = idx τ y) : x = y := by
  rw [← getD_idx τ x, ← getD_idx τ y, h]

theorem els_B_getD {i : ℕ} (hi : i < 3) : (els .B).getD i default = (val i : Val) := by
  interval_cases i <;> rfl

/-- The element named by index `a`. -/
noncomputable def el (τ : Ty) (a : ℕ) : SieberBool τ := (els τ).getD a default

/-- The table of an element of arrow type. -/
noncomputable def table (σ ρ : Ty) (x : SieberBool (σ ⇒ ρ)) : List ℕ :=
  (List.range (els σ).length).map fun a => idx ρ (x.1 (el σ a))

noncomputable def tablesOf : Ty → List (List ℕ)
  | .B => []
  | .arr σ ρ => (els (σ ⇒ ρ)).map (table σ ρ)

/-- The carriers of all types with code at most `K`. -/
noncomputable def tysK (K : ℕ) : List TyTab :=
  (List.range (K + 1)).filterMap fun c => if c = 0 then none else some (c, tablesOf (Ty.decode c))

theorem tabs_unique {tys : List TyTab} {c : ℕ} {v : List (List ℕ)} (hmem : (c, v) ∈ tys)
    (huniq : ∀ e ∈ tys, e.1 = c → e = (c, v)) : tabs tys c = v := by
  unfold tabs
  cases hf : tys.find? (fun e => e.1 == c) with
  | none =>
      have := List.find?_eq_none.mp hf _ hmem
      simp at this
  | some e =>
      have he : e.1 = c := by simpa using List.find?_some (p := fun e : TyTab => e.1 == c) hf
      rw [huniq e (List.mem_of_find?_eq_some hf) he]
      rfl

theorem tabs_tysK {K c : ℕ} (hc0 : c ≠ 0) (hcK : c ≤ K) :
    tabs (tysK K) c = tablesOf (Ty.decode c) := by
  apply tabs_unique
  · simp only [tysK, List.mem_filterMap, List.mem_range]
    exact ⟨c, by omega, by simp [hc0]⟩
  · intro e he hec
    simp only [tysK, List.mem_filterMap, List.mem_range] at he
    obtain ⟨c', -, hc'⟩ := he
    split_ifs at hc' with h
    cases hc'
    simp only at hec
    subst hec
    rfl

theorem size_tysK {K c : ℕ} (hcK : c ≤ K) : size (tysK K) c = (els (Ty.decode c)).length := by
  by_cases hc0 : c = 0
  · subst hc0; rw [Ty.decode_zero]; rfl
  · rw [size, if_neg hc0, tabs_tysK hc0 hcK]
    rw [decode_pos hc0]
    simp [tablesOf]

theorem covered_tysK {K c : ℕ} (hcK : c ≤ K) : covered (tysK K) c := by
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  · right
    simp only [List.any_eq_true, beq_iff_eq, tysK, List.mem_filterMap, List.mem_range]
    exact ⟨(c, tablesOf (Ty.decode c)), ⟨c, by omega, by simp [hc0]⟩, rfl⟩


/-! ## Environments -/

/-- All environments over a context, as index lists. -/
noncomputable def envList : Ctx → List (List ℕ)
  | [] => [[]]
  | σ :: Γ => (envList Γ).flatMap fun e => (List.range (els σ).length).map (· :: e)

noncomputable def elEnv : (Γ : Ctx) → List ℕ → Env Γ
  | [], _ => PUnit.unit
  | σ :: Γ, env => (elEnv Γ env.tail, el σ (env.getD 0 0))

theorem mem_envList : ∀ {Γ : Ctx} {env : List ℕ},
    env ∈ envList Γ ↔ env.length = Γ.length ∧ ∀ k (hk : k < Γ.length), env.getD k 0 < (els (Γ.get ⟨k, hk⟩)).length
  | [], env => by
      simp only [envList, List.mem_singleton, List.length_nil]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | σ :: Γ, env => by
      simp only [envList, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨e, he, a, ha, rfl⟩
        obtain ⟨hl, hlt⟩ := mem_envList.mp he
        refine ⟨by simp [hl], fun k hk => ?_⟩
        cases k with
        | zero => simpa using ha
        | succ k => simpa using hlt k (by simpa using hk)
      · rintro ⟨hl, hlt⟩
        cases env with
        | nil => simp at hl
        | cons a e =>
            refine ⟨e, mem_envList.mpr ⟨by simpa using hl, fun k hk => ?_⟩, a, ?_, rfl⟩
            · simpa using hlt (k + 1) (by simpa using hk)
            · simpa using hlt 0 (by simp)

theorem var_facts : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ),
    ∃ hk : x.code < Γ.length, Γ.get ⟨x.code, hk⟩ = τ ∧
      ∀ env : List ℕ, x.sem.1 (elEnv Γ env) = el τ (env.getD x.code 0)
  | _ :: _, _, .vz => ⟨by simp [Var.code], rfl, fun env => rfl⟩
  | _ :: _, _, .vs x => by
      obtain ⟨hk, hty, hsem⟩ := var_facts x
      refine ⟨by simp [Var.code]; omega, by simpa [Var.code] using hty, fun env => ?_⟩
      have := hsem env.tail
      rw [getD_tail] at this
      exact this

/-! ## Traces -/

/-- Every type (and context type) occurring in a term satisfies `p`. -/
def AllTys (p : ℕ → Prop) : {Γ : Ctx} → {ρ : Ty} → Tm Γ ρ → Prop
  | Γ, ρ, .var _ => p ρ.code ∧ ∀ σ ∈ Γ, p σ.code
  | Γ, .arr σ' ρ, .lam M => (p (σ' ⇒ ρ).code ∧ ∀ σ ∈ Γ, p σ.code) ∧ AllTys p M
  | Γ, ρ, .app M N => (p ρ.code ∧ ∀ σ ∈ Γ, p σ.code) ∧ AllTys p M ∧ AllTys p N
  | Γ, .B, .tt => p Ty.B.code ∧ ∀ σ ∈ Γ, p σ.code
  | Γ, .B, .ff => p Ty.B.code ∧ ∀ σ ∈ Γ, p σ.code
  | Γ, .B, .bot => p Ty.B.code ∧ ∀ σ ∈ Γ, p σ.code
  | Γ, .B, .ite C M N => (p Ty.B.code ∧ ∀ σ ∈ Γ, p σ.code) ∧ AllTys p C ∧ AllTys p M ∧ AllTys p N

theorem AllTys.head {p : ℕ → Prop} : ∀ {Γ : Ctx} {ρ : Ty} {P : Tm Γ ρ}, AllTys p P →
    p ρ.code ∧ ∀ σ ∈ Γ, p σ.code
  | _, _, .var _, h => by simp only [AllTys] at h; exact h
  | _, .arr _ _, .lam _, h => h.1
  | _, _, .app _ _, h => by simp only [AllTys] at h; exact h.1
  | _, .B, .tt, h => h
  | _, .B, .ff, h => h
  | _, .B, .bot, h => h
  | _, .B, .ite _ _ _, h => h.1

/-- The entry recording the value of `P` in environment `env`. -/
noncomputable def entry (β : ℕ) {Γ : Ctx} {ρ : Ty} (P : Tm Γ ρ) (env : List ℕ) : Entry :=
  (Γ.map Ty.code, P.code, env, ρ.code, idx ρ (P.sem.1 (elEnv Γ env)), β)

/-- The entries of `P` and all its subterms, in every environment. -/
noncomputable def entriesOf (β : ℕ) : {Γ : Ctx} → {ρ : Ty} → Tm Γ ρ → List Entry
  | Γ, _, .var x => (envList Γ).map (entry β (.var x))
  | Γ, .arr _ _, .lam M => (envList Γ).map (entry β (.lam M)) ++ entriesOf β M
  | Γ, _, .app M N => (envList Γ).map (entry β (.app M N)) ++ entriesOf β M ++ entriesOf β N
  | Γ, .B, .tt => (envList Γ).map (entry β (.tt : Tm Γ .B))
  | Γ, .B, .ff => (envList Γ).map (entry β (.ff : Tm Γ .B))
  | Γ, .B, .bot => (envList Γ).map (entry β (.bot : Tm Γ .B))
  | Γ, .B, .ite C M N => (envList Γ).map (entry β (.ite C M N)) ++ entriesOf β C ++ entriesOf β M ++ entriesOf β N

theorem entry_mem_entriesOf (β : ℕ) {Γ : Ctx} {ρ : Ty} (P : Tm Γ ρ) {env : List ℕ}
    (henv : env ∈ envList Γ) : entry β P env ∈ entriesOf β P := by
  cases P <;> simp only [entriesOf, List.mem_append, List.mem_map] <;>
    first
    | exact Or.inl (Or.inl (Or.inl ⟨env, henv, rfl⟩))
    | exact Or.inl (Or.inl ⟨env, henv, rfl⟩)
    | exact Or.inl ⟨env, henv, rfl⟩
    | exact ⟨env, henv, rfl⟩


/-! ## Local checks of constructed entries -/

def valCode : Val → ℕ
  | .bot => 0
  | .tt => 1
  | .ff => 2

theorem idx_B (x : Val) : idx .B x = valCode x := by
  cases x
  · exact idx_getD .B (i := 0) (by simp [els])
  · exact idx_getD .B (i := 1) (by simp [els])
  · exact idx_getD .B (i := 2) (by simp [els])

theorem idx_B_ite (a b c : Val) :
    idx .B (Val.ite a b c) = ite (idx .B a) (idx .B b) (idx .B c) := by
  rw [idx_B, idx_B, idx_B, idx_B]
  cases a <;> cases b <;> cases c <;> rfl

theorem envList_len {Γ : Ctx} {env : List ℕ} (h : env ∈ envList Γ) :
    env.length = (Γ.map Ty.code).length := by
  simpa using (mem_envList.mp h).1

theorem envList_bound {K : ℕ} {Γ : Ctx} {env : List ℕ} (h : env ∈ envList Γ)
    (hK : ∀ σ ∈ Γ, σ.code ≤ K) :
    ∀ k < (Γ.map Ty.code).length, env.getD k 0 < size (tysK K) ((Γ.map Ty.code).getD k 0) := by
  intro k hk
  rw [List.length_map] at hk
  have hmem : Γ.get ⟨k, hk⟩ ∈ Γ := List.get_mem _ _
  have e1 : (Γ.map Ty.code).getD k 0 = (Γ.get ⟨k, hk⟩).code := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [e1, size_tysK (hK _ hmem), Ty.decode_code]
  exact (mem_envList.mp h).2 k hk

theorem val_bound {K : ℕ} {ρ : Ty} (hK : ρ.code ≤ K) (x : SieberBool ρ) :
    idx ρ x < size (tysK K) ρ.code := by
  rw [size_tysK hK, Ty.decode_code]; exact idx_lt ρ x

theorem level_ok {β : ℕ} {Γ : Ctx} {ρ : Ty} (h : β = 0 ∨ (ρ.code < β ∧ ∀ σ ∈ Γ, σ.code < β)) :
    β = 0 ∨ (ρ.code < β ∧ ∀ c ∈ Γ.map Ty.code, c < β) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right; refine ⟨h1, ?_⟩; simp only [List.mem_map]; rintro _ ⟨σ, hσ, rfl⟩; exact h2 σ hσ

theorem entries_sub {β : ℕ} {Γ : Ctx} {ρ : Ty} (P : Tm Γ ρ) {trace : List Entry}
    (h : ∀ e ∈ entriesOf β P, e ∈ trace) {env : List ℕ} (henv : env ∈ envList Γ) :
    entry β P env ∈ trace := h _ (entry_mem_entriesOf β P henv)

theorem tabs_getD_getD {K : ℕ} {σ ρ : Ty} (hK : (σ ⇒ ρ).code ≤ K) (x : SieberBool (σ ⇒ ρ))
    {a : ℕ} (ha : a < (els σ).length) :
    ((tabs (tysK K) (σ ⇒ ρ).code).getD (idx (σ ⇒ ρ) x) []).getD a 0 = idx ρ (x.1 (el σ a)) := by
  rw [tabs_tysK (by simp [Ty.code]) hK, Ty.decode_code]
  simp only [tablesOf]
  have e1 : (List.map (table σ ρ) (els (σ ⇒ ρ))).getD (idx (σ ⇒ ρ) x) [] = table σ ρ x := by
    rw [List.getD_eq_getElem _ _ (by simpa using idx_lt _ x), List.getElem_map]
    congr 1
    exact List.getElem_idxOf (idx_lt _ x)
  rw [e1]
  simp [table, List.getD_eq_getElem?_getD, ha]


theorem cons_envList {Γ : Ctx} {σ : Ty} {env : List ℕ} (henv : env ∈ envList Γ) {a : ℕ}
    (ha : a < (els σ).length) : (a :: env) ∈ envList (σ :: Γ) := by
  simp only [envList, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨env, henv, a, ha, rfl⟩

theorem sem_lam_apply {Γ : Ctx} {σ ρ : Ty} (M : Tm (σ :: Γ) ρ) (env : List ℕ) (a : ℕ) :
    ((Tm.lam M).sem.1 (elEnv Γ env)).1 (el σ a) = M.sem.1 (elEnv (σ :: Γ) (a :: env)) := by
  simp only [Tm.sem]; rfl

/-- Every constructed entry passes the local check. -/
theorem entries_ok {K β : ℕ} {trace : List Entry} : ∀ {Γ : Ctx} {ρ : Ty} (P : Tm Γ ρ),
    AllTys (· ≤ K) P → (β = 0 ∨ AllTys (· < β) P) → (∀ e ∈ entriesOf β P, e ∈ trace) →
    ∀ e ∈ entriesOf β P, entryOK (tysK K) trace e = true
  | Γ, ρ, .var x, hK, hβ, hsub, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, henv, rfl⟩ := he
      have hK' := hK.head
      have hβ' := level_ok (hβ.imp id AllTys.head)
      obtain ⟨hk, hty, hsem⟩ := var_facts x
      have hc : (Tm.var x : Tm Γ ρ).code % 7 = 0 := by simp [Tm.code]
      have hq : (Tm.var x : Tm Γ ρ).code / 7 = x.code := by simp [Tm.code]
      simp only [entry, entryOK, hc, hq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.all_eq_true, List.mem_range, Bool.or_eq_true]
      refine ⟨⟨⟨⟨envList_len henv, envList_bound henv hK'.2⟩, val_bound hK'.1 _⟩, hβ'⟩, ⟨?_, ?_⟩, ?_⟩
      · simpa using hk
      · simp [List.getD_eq_getElem?_getD, hk, ← hty]
      · simp only [Tm.sem]
        rw [hsem env]
        unfold el
        rw [idx_getD]
        have := (mem_envList.mp henv).2 x.code hk
        rwa [hty] at this
  | Γ, .arr σ ρ, .lam M, hK, hβ, hsub, e, he => by
      simp only [entriesOf, List.mem_append, List.mem_map] at he
      have hsubM : ∀ e ∈ entriesOf β M, e ∈ trace := fun e he => hsub e (by
        simp only [entriesOf, List.mem_append]; exact Or.inr he)
      rcases he with ⟨env, henv, rfl⟩ | he
      · have hK' := hK.head
        have hβ' := level_ok (hβ.imp id AllTys.head)
        have hc0 : (σ ⇒ ρ).code ≠ 0 := by simp [Ty.code]
        have hσK : σ.code ≤ K := le_trans (le_of_lt (by rw [← dom_code σ ρ]; exact dom_lt hc0)) hK'.1
        have hc : (Tm.lam M).code % 7 = 1 := by simp only [Tm.code]; omega
        have hq : (Tm.lam M).code / 7 = Nat.pair σ.code M.code := by simp only [Tm.code]; omega
        simp only [entry, entryOK, hc, hq, Nat.unpair_pair, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]
        refine ⟨⟨⟨⟨envList_len henv, envList_bound henv hK'.2⟩, val_bound hK'.1 _⟩, hβ'⟩,
          ⟨hc0, dom_code σ ρ⟩, fun a ha => ?_⟩
        rw [size_tysK hσK, Ty.decode_code] at ha
        apply List.any_eq_true.mpr
        refine ⟨entry β M (a :: env), entries_sub M hsubM (cons_envList henv ha), ?_⟩
        simp only [entry, beq_iff_eq, cod_code, List.map_cons]
        rw [tabs_getD_getD hK'.1 _ ha, sem_lam_apply]
      · exact entries_ok M hK.2 (hβ.imp id (fun h => h.2)) hsubM e he
  | Γ, ρ, .app M N, hK, hβ, hsub, e, he => by
      simp only [AllTys] at hK hβ
      simp only [entriesOf, List.mem_append, List.mem_map] at he
      have hsubM : ∀ e ∈ entriesOf β M, e ∈ trace := fun e he => hsub e (by
        simp only [entriesOf, List.mem_append]; exact Or.inl (Or.inr he))
      have hsubN : ∀ e ∈ entriesOf β N, e ∈ trace := fun e he => hsub e (by
        simp only [entriesOf, List.mem_append]; exact Or.inr he)
      rcases he with (⟨env, henv, rfl⟩ | he) | he
      · rename_i σ
        have hK' := hK.1
        have hβ' := level_ok (hβ.imp id (fun h => h.1))
        have hMK := hK.2.1.head.1
        have hc : (Tm.app M N).code % 7 = 2 := by simp only [Tm.code]; omega
        have hq : (Tm.app M N).code / 7 = Nat.pair σ.code (Nat.pair M.code N.code) := by
          simp only [Tm.code]; omega
        simp only [entry, entryOK, hc, hq, Nat.unpair_pair, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
        refine ⟨⟨⟨⟨envList_len henv, envList_bound henv hK'.2⟩, val_bound hK'.1 _⟩, hβ'⟩, ?_⟩
        apply List.any_eq_true.mpr
        refine ⟨entry β M env, entries_sub M hsubM henv, ?_⟩
        simp only [entry, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq, code_arr,
          true_and]
        apply List.any_eq_true.mpr
        refine ⟨entry β N env, entries_sub N hsubN henv, ?_⟩
        simp only [entry, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq, true_and]
        simp only [app]
        rw [← code_arr σ ρ, tabs_getD_getD hMK _ (idx_lt σ _)]
        simp only [el, getD_idx, Tm.sem]
      · exact entries_ok M hK.2.1 (hβ.imp id (fun h => h.2.1)) hsubM e he
      · exact entries_ok N hK.2.2 (hβ.imp id (fun h => h.2.2)) hsubN e he
  | Γ, .B, .tt, hK, hβ, hsub, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, henv, rfl⟩ := he
      simp only [entry, entryOK, Tm.code, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.all_eq_true, List.mem_range, Bool.or_eq_true]
      refine ⟨⟨⟨⟨envList_len henv, envList_bound henv hK.2⟩, val_bound hK.1 _⟩,
        level_ok (hβ.imp id id)⟩, ?_⟩
      simp [Tm.sem, constSem, idx_B, valCode, Ty.code]
  | Γ, .B, .ff, hK, hβ, hsub, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, henv, rfl⟩ := he
      simp only [entry, entryOK, Tm.code, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.all_eq_true, List.mem_range, Bool.or_eq_true]
      refine ⟨⟨⟨⟨envList_len henv, envList_bound henv hK.2⟩, val_bound hK.1 _⟩,
        level_ok (hβ.imp id id)⟩, ?_⟩
      simp [Tm.sem, constSem, idx_B, valCode, Ty.code]
  | Γ, .B, .bot, hK, hβ, hsub, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, henv, rfl⟩ := he
      simp only [entry, entryOK, Tm.code, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.all_eq_true, List.mem_range, Bool.or_eq_true]
      refine ⟨⟨⟨⟨envList_len henv, envList_bound henv hK.2⟩, val_bound hK.1 _⟩,
        level_ok (hβ.imp id id)⟩, ?_⟩
      simp [Tm.sem, constSem, idx_B, valCode, Ty.code]
  | Γ, .B, .ite C M N, hK, hβ, hsub, e, he => by
      simp only [entriesOf, List.mem_append, List.mem_map] at he
      have hsubC : ∀ e ∈ entriesOf β C, e ∈ trace := fun e he => hsub e (by
        simp only [entriesOf, List.mem_append]; exact Or.inl (Or.inl (Or.inr he)))
      have hsubM : ∀ e ∈ entriesOf β M, e ∈ trace := fun e he => hsub e (by
        simp only [entriesOf, List.mem_append]; exact Or.inl (Or.inr he))
      have hsubN : ∀ e ∈ entriesOf β N, e ∈ trace := fun e he => hsub e (by
        simp only [entriesOf, List.mem_append]; exact Or.inr he)
      rcases he with ((⟨env, henv, rfl⟩ | he) | he) | he
      · have hK' := hK.1
        have hβ' := level_ok (hβ.imp id (fun h => h.1))
        have hc : (Tm.ite C M N).code % 7 = 6 := by simp only [Tm.code]; omega
        have hq : (Tm.ite C M N).code / 7 = Nat.pair C.code (Nat.pair M.code N.code) := by
          simp only [Tm.code]; omega
        simp only [entry, entryOK, hc, hq, Nat.unpair_pair, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
        refine ⟨⟨⟨⟨envList_len henv, envList_bound henv hK'.2⟩, val_bound hK'.1 _⟩, hβ'⟩, ?_⟩
        simp only [Ty.code, true_and]
        apply List.any_eq_true.mpr
        refine ⟨entry β C env, entries_sub C hsubC henv, ?_⟩
        simp only [entry, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq, Ty.code,
          true_and]
        apply List.any_eq_true.mpr
        refine ⟨entry β M env, entries_sub M hsubM henv, ?_⟩
        simp only [entry, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq, Ty.code,
          true_and]
        apply List.any_eq_true.mpr
        refine ⟨entry β N env, entries_sub N hsubN henv, ?_⟩
        simp only [entry, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq, Ty.code,
          true_and]
        simp only [Tm.sem]
        exact idx_B_ite _ _ _
      · exact entries_ok C hK.2.1 (hβ.imp id (fun h => h.2.1)) hsubC e he
      · exact entries_ok M hK.2.2.1 (hβ.imp id (fun h => h.2.2.1)) hsubM e he
      · exact entries_ok N hK.2.2.2 (hβ.imp id (fun h => h.2.2.2)) hsubN e he


/-! ## Type bounds and the subformula property -/

theorem AllTys.mono {p q : ℕ → Prop} (hpq : ∀ n, p n → q n) :
    ∀ {Γ : Ctx} {ρ : Ty} {P : Tm Γ ρ}, AllTys p P → AllTys q P
  | _, _, .var _, h => by
      simp only [AllTys] at h ⊢; exact ⟨hpq _ h.1, fun σ hσ => hpq _ (h.2 σ hσ)⟩
  | _, .arr _ _, .lam _, h => ⟨⟨hpq _ h.1.1, fun σ hσ => hpq _ (h.1.2 σ hσ)⟩, AllTys.mono hpq h.2⟩
  | _, _, .app _ _, h => by
      simp only [AllTys] at h ⊢
      exact ⟨⟨hpq _ h.1.1, fun σ hσ => hpq _ (h.1.2 σ hσ)⟩, AllTys.mono hpq h.2.1, AllTys.mono hpq h.2.2⟩
  | _, .B, .tt, h => ⟨hpq _ h.1, fun σ hσ => hpq _ (h.2 σ hσ)⟩
  | _, .B, .ff, h => ⟨hpq _ h.1, fun σ hσ => hpq _ (h.2 σ hσ)⟩
  | _, .B, .bot, h => ⟨hpq _ h.1, fun σ hσ => hpq _ (h.2 σ hσ)⟩
  | _, .B, .ite _ _ _, h =>
      ⟨⟨hpq _ h.1.1, fun σ hσ => hpq _ (h.1.2 σ hσ)⟩, AllTys.mono hpq h.2.1,
        AllTys.mono hpq h.2.2.1, AllTys.mono hpq h.2.2.2⟩

/-- A predicate on type codes closed under taking components. -/
def Down (p : ℕ → Prop) : Prop := p 0 ∧ ∀ σ ρ : Ty, p (σ ⇒ ρ).code → p σ.code ∧ p ρ.code

theorem down_lt {c : ℕ} (hc : 0 < c) : Down (· < c) :=
  ⟨hc, fun σ ρ h => ⟨lt_trans (by rw [← dom_code σ ρ]; exact dom_lt (by simp [Ty.code])) h,
    lt_trans (by rw [← cod_code σ ρ]; exact cod_lt (by simp [Ty.code])) h⟩⟩

theorem down_le (K : ℕ) : Down (· ≤ K) :=
  ⟨Nat.zero_le _, fun σ ρ h => ⟨le_trans (le_of_lt (by rw [← dom_code σ ρ]; exact dom_lt (by simp [Ty.code]))) h,
    le_trans (le_of_lt (by rw [← cod_code σ ρ]; exact cod_lt (by simp [Ty.code]))) h⟩⟩

theorem var_type_mem : ∀ {Γ : Ctx} {τ : Ty}, Var Γ τ → τ ∈ Γ
  | _ :: _, _, .vz => List.mem_cons_self
  | _ :: _, _, .vs x => List.mem_cons_of_mem _ (var_type_mem x)

/-- **Subformula property**: in a normal form, every type involved is built from the
types of the context and (for non-neutral terms) the result type. -/
theorem Norm.allTys {p : ℕ → Prop} (hp : Down p) : ∀ {Γ : Ctx} {τ : Ty} {b : Bool} (n : Norm Γ τ b),
    (∀ σ ∈ Γ, p σ.code) → (b = true → p τ.code) → AllTys p n.embed ∧ p τ.code
  | _, _, _, .var x, hΓ, _ => by
      have := hΓ _ (var_type_mem x)
      simp only [Norm.embed, AllTys]; exact ⟨⟨this, hΓ⟩, this⟩
  | _, _, _, .app n m, hΓ, _ => by
      obtain ⟨hn, hty⟩ := Norm.allTys hp n hΓ (by simp)
      obtain ⟨hσ, hτ⟩ := hp.2 _ _ hty
      obtain ⟨hm, -⟩ := Norm.allTys hp m hΓ (fun _ => hσ)
      simp only [Norm.embed, AllTys]; exact ⟨⟨⟨hτ, hΓ⟩, hn, hm⟩, hτ⟩
  | _, _, _, .up n, hΓ, _ => by
      simp only [Norm.embed]; exact Norm.allTys hp n hΓ (by simp)
  | _, .arr σ ρ, _, .lam n, hΓ, hτ => by
      have hτ' := hτ rfl
      obtain ⟨hσ, hρ⟩ := hp.2 _ _ hτ'
      obtain ⟨hn, -⟩ := Norm.allTys hp n (by
        intro σ' hσ'
        rcases List.mem_cons.mp hσ' with rfl | hσ'
        · exact hσ
        · exact hΓ _ hσ') (fun _ => hρ)
      simp only [Norm.embed]; exact ⟨⟨⟨hτ', hΓ⟩, hn⟩, hτ'⟩
  | _, _, _, .tt, hΓ, _ => ⟨⟨hp.1, hΓ⟩, hp.1⟩
  | _, _, _, .ff, hΓ, _ => ⟨⟨hp.1, hΓ⟩, hp.1⟩
  | _, _, _, .bot, hΓ, _ => ⟨⟨hp.1, hΓ⟩, hp.1⟩
  | _, _, _, .ite c a b, hΓ, _ => by
      obtain ⟨hc, -⟩ := Norm.allTys hp c hΓ (fun _ => hp.1)
      obtain ⟨ha, -⟩ := Norm.allTys hp a hΓ (fun _ => hp.1)
      obtain ⟨hb, -⟩ := Norm.allTys hp b hΓ (fun _ => hp.1)
      exact ⟨⟨⟨hp.1, hΓ⟩, hc, ha, hb⟩, hp.1⟩

/-- The largest type code occurring in a term. -/
def tmax : {Γ : Ctx} → {ρ : Ty} → Tm Γ ρ → ℕ
  | Γ, ρ, .var _ => max ρ.code (Γ.map Ty.code).sum
  | Γ, .arr σ ρ, .lam M => max (max (σ ⇒ ρ).code (Γ.map Ty.code).sum) (tmax M)
  | Γ, ρ, .app M N => max (max ρ.code (Γ.map Ty.code).sum) (max (tmax M) (tmax N))
  | Γ, .B, .tt => (Γ.map Ty.code).sum
  | Γ, .B, .ff => (Γ.map Ty.code).sum
  | Γ, .B, .bot => (Γ.map Ty.code).sum
  | Γ, .B, .ite C M N => max (Γ.map Ty.code).sum (max (tmax C) (max (tmax M) (tmax N)))

theorem le_sum_of_mem {Γ : Ctx} {σ : Ty} (h : σ ∈ Γ) : σ.code ≤ (Γ.map Ty.code).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

theorem allTys_tmax : ∀ {Γ : Ctx} {ρ : Ty} (P : Tm Γ ρ), AllTys (· ≤ tmax P) P
  | _, _, .var _ => by
      simp only [AllTys, tmax]
      exact ⟨le_max_left _ _, fun σ hσ => le_trans (le_sum_of_mem hσ) (le_max_right _ _)⟩
  | _, .arr _ _, .lam M => by
      refine ⟨⟨by simp [tmax], fun σ hσ => by simp only [tmax]; exact le_trans (le_sum_of_mem hσ) (by omega)⟩, ?_⟩
      exact AllTys.mono (fun n h => le_trans h (by simp [tmax])) (allTys_tmax M)
  | _, _, .app M N => by
      simp only [AllTys]
      refine ⟨⟨by simp [tmax], fun σ hσ => by simp only [tmax]; exact le_trans (le_sum_of_mem hσ) (by omega)⟩,
        AllTys.mono (fun n h => le_trans h (by simp [tmax])) (allTys_tmax M),
        AllTys.mono (fun n h => le_trans h (by simp [tmax])) (allTys_tmax N)⟩
  | _, .B, .tt => ⟨by simp [Ty.code], fun σ hσ => by simp only [tmax]; exact le_sum_of_mem hσ⟩
  | _, .B, .ff => ⟨by simp [Ty.code], fun σ hσ => by simp only [tmax]; exact le_sum_of_mem hσ⟩
  | _, .B, .bot => ⟨by simp [Ty.code], fun σ hσ => by simp only [tmax]; exact le_sum_of_mem hσ⟩
  | _, .B, .ite C M N =>
      ⟨⟨by simp [Ty.code], fun σ hσ => by simp only [tmax]; exact le_trans (le_sum_of_mem hσ) (by omega)⟩,
        AllTys.mono (fun n h => le_trans h (by simp [tmax])) (allTys_tmax C),
        AllTys.mono (fun n h => le_trans h (by simp [tmax])) (allTys_tmax M),
        AllTys.mono (fun n h => le_trans h (by simp [tmax])) (allTys_tmax N)⟩


/-! ## Failing tests -/

/-- The order test `S²_{{0},{0,1}}`. -/
def ordD : List (List ℕ × List ℕ) := [([0], [0, 1])]

theorem toTest_ordD : toTest 2 ordD = {({0}, Finset.univ)} := by
  have h0 : toFin 2 [0] = {0} := by ext i; rw [mem_toFin (by simp)]; fin_cases i <;> decide
  have h01 : toFin 2 [0, 1] = Finset.univ := by ext i; rw [mem_toFin (by simp)]; fin_cases i <;> decide
  simp [toTest, ordD, h0, h01]

theorem holds_ord (g : Fin 2 → Val) : (toTest 2 ordD).holds g ↔ Val.le (g 0) (g 1) := by
  rw [toTest_ordD]
  simp only [Test.holds, Finset.mem_singleton, forall_eq, Finset.subset_univ, forall_const, Elem,
    Finset.mem_univ, true_implies, Val.le]
  constructor
  · rintro (⟨i, hi, hgi⟩ | hc)
    · subst hi; exact Or.inl hgi
    · exact Or.inr (hc 0 1)
  · rintro (h | h)
    · exact Or.inl ⟨0, rfl, h⟩
    · refine Or.inr fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [h]

/-- The lift of the order test is the order. -/
theorem rel_ord : ∀ (τ : Ty) (G : Fin 2 → SieberBool τ),
    (Model τ).rel 2 (toTest 2 ordD) G ↔ (Model τ).le (G 0) (G 1)
  | .B, G => holds_ord G
  | .arr σ ρ, G => by
      change (∀ g : Fin 2 → SieberBool σ, (Model σ).rel 2 (toTest 2 ordD) g →
        (Model ρ).rel 2 (toTest 2 ordD) (fun i => (G i).1 (g i))) ↔ ∀ a, (Model ρ).le ((G 0).1 a) ((G 1).1 a)
      constructor
      · intro h a
        have := h ![a, a] ((rel_ord σ _).mpr (Model.le_refl σ a))
        exact (rel_ord ρ _).mp this
      · intro h g hg
        apply (rel_ord ρ _).mpr
        exact Model.le_trans _ _ _ _ ((G 0).2.1 _ _ ((rel_ord σ g).mp hg)) (h (g 1))

theorem toFin_toList {w : ℕ} (A : Finset (Fin w)) : toFin w (A.toList.map Fin.val) = A := by
  ext i
  rw [mem_toFin (by simp)]
  simp only [List.mem_map, Finset.mem_toList]
  exact ⟨fun ⟨a, ha, h⟩ => Fin.ext h ▸ ha, fun h => ⟨i, h, rfl⟩⟩

/-- A model test as a list test. -/
noncomputable def testList {w : ℕ} (d : Test w) : List (List ℕ × List ℕ) :=
  d.toList.map fun p => (p.1.toList.map Fin.val, p.2.toList.map Fin.val)

theorem toTest_testList {w : ℕ} (d : Test w) : toTest w (testList d) = d := by
  ext p
  simp [toTest, testList, toFin_toList]

theorem testList_bound {w : ℕ} (d : Test w) :
    ∀ p ∈ testList d, (∀ i ∈ p.1, i < w) ∧ (∀ i ∈ p.2, i < w) := by
  intro p hp
  simp only [testList, List.mem_map] at hp
  obtain ⟨q, -, rfl⟩ := hp
  exact ⟨by simp, by simp⟩

/-- A function outside the carrier fails some test. -/
theorem exists_failure {σ ρ : Ty} (f : SieberBool σ → SieberBool ρ)
    (hf : ¬ ((∀ a b, (Model σ).le a b → (Model ρ).le (f a) (f b)) ∧
      ∀ w (d : Test w) (g : Fin w → SieberBool σ), (Model σ).rel w d g →
        (Model ρ).rel w d (fun i => f (g i)))) :
    ∃ (w : ℕ) (d : Test w) (G : Fin w → SieberBool σ),
      (Model σ).rel w d G ∧ ¬ (Model ρ).rel w d (fun i => f (G i)) := by
  by_contra hno
  push_neg at hno
  apply hf
  refine ⟨fun a b hab => ?_, hno⟩
  have := hno 2 (toTest 2 ordD) ![a, b] ((rel_ord σ _).mpr hab)
  exact (rel_ord ρ _).mp this


/-! ## Lift sets -/

open Classical in
/-- The lifted relations of a test at all types with code at most `K`. -/
noncomputable def liftsK (K w : ℕ) (d : Test w) : List Lift :=
  (List.range (K + 1)).map fun c' => (c', (tuples (size (tysK K) c') w).filter fun u =>
    decide ((Model (Ty.decode c')).rel w d (fun i => el _ (u.getD i 0))))

theorem hasLift_liftsK {K w : ℕ} {d : Test w} {c : ℕ} (hc : c ≤ K) : hasLift (liftsK K w d) c = true := by
  simp only [hasLift, liftsK, List.any_map, List.any_eq_true, List.mem_range, Function.comp_def,
    beq_iff_eq]
  exact ⟨c, by omega, rfl⟩

open Classical in
theorem liftSet_liftsK {K w : ℕ} {d : Test w} (τ : Ty) (hK : τ.code ≤ K) :
    liftSet (liftsK K w d) τ.code = (tuples (size (tysK K) τ.code) w).filter fun u =>
      decide ((Model τ).rel w d (fun i => el τ (u.getD i 0))) := by
  have hmem : ∀ e ∈ liftsK K w d, e.1 = τ.code → e = (τ.code, (tuples (size (tysK K) τ.code) w).filter
      fun u => decide ((Model (Ty.decode τ.code)).rel w d (fun i => el _ (u.getD i 0)))) := by
    intro e he hec
    simp only [liftsK, List.mem_map, List.mem_range] at he
    obtain ⟨c', -, rfl⟩ := he
    simp only at hec
    subst hec
    rfl
  unfold liftSet
  cases hf : (liftsK K w d).find? (fun e => e.1 == τ.code) with
  | none =>
      have := List.find?_eq_none.mp hf (τ.code, _) (by
        simp only [liftsK, List.mem_map, List.mem_range]; exact ⟨τ.code, by omega, rfl⟩)
      simp at this
  | some e =>
      have hec : e.1 = τ.code := by simpa using List.find?_some (p := fun e : Lift => e.1 == τ.code) hf
      rw [hmem e (List.mem_of_find?_eq_some hf) hec]
      show List.filter _ _ = List.filter _ _
      congr 1
      funext u
      rw [Ty.decode_code]

theorem el_lt_of_tuples {τ : Ty} {K w : ℕ} (hK : τ.code ≤ K) {u : List ℕ}
    (hu : u ∈ tuples (size (tysK K) τ.code) w) {i : ℕ} (hi : i < w) : u.getD i 0 < (els τ).length := by
  have := getD_lt_of_tuples hu hi
  rwa [size_tysK hK, Ty.decode_code] at this

theorem el_app {K : ℕ} {σ ρ : Ty} (hK : (σ ⇒ ρ).code ≤ K) {u h : ℕ} (hu : u < (els (σ ⇒ ρ)).length)
    (hh : h < (els σ).length) :
    el ρ (app (tysK K) (σ ⇒ ρ).code u h) = (el (σ ⇒ ρ) u).1 (el σ h) := by
  unfold app
  have hu' : u = idx (σ ⇒ ρ) (el (σ ⇒ ρ) u) := (idx_getD _ hu).symm
  conv_lhs => rw [hu']
  rw [tabs_getD_getD hK _ hh]
  unfold el
  rw [getD_idx]

open Classical in
/-- The checker's defining condition on these lift sets is relatedness. -/
theorem cond_iff {K w : ℕ} (d : Test w) (τ : Ty) (hK : τ.code ≤ K) {u : List ℕ}
    (hu : u ∈ tuples (size (tysK K) τ.code) w) :
    cond (tysK K) w (testList d) (liftsK K w d) τ.code u = true ↔
      (Model τ).rel w d (fun i => el τ (u.getD i 0)) := by
  cases τ with
  | B =>
      have hu3 : u ∈ tuples 3 w := by simpa [size, Ty.code] using hu
      simp only [cond, Ty.code, if_true]
      rw [holds_iff (testList_bound d) hu3, toTest_testList]
      have : gtuple w u = fun i : Fin w => (el .B (u.getD i 0) : Val) := by
        funext i
        simp only [gtuple, el]
        rw [els_B_getD (getD_lt_of_tuples hu3 i.2)]
      rw [this]
      rfl
  | arr σ ρ =>
      have hc0 : (σ ⇒ ρ).code ≠ 0 := by simp [Ty.code]
      have hσK : σ.code ≤ K := le_trans (le_of_lt (by rw [← dom_code σ ρ]; exact dom_lt hc0)) hK
      have hρK : ρ.code ≤ K := le_trans (le_of_lt (by rw [← cod_code σ ρ]; exact cod_lt hc0)) hK
      simp only [cond, hc0, if_false, dom_code, cod_code, liftSet_liftsK σ hσK, liftSet_liftsK ρ hρK,
        List.all_eq_true, List.mem_filter, decide_eq_true_eq, List.contains_iff_mem, and_imp]
      have happ : ∀ hh : List ℕ, hh ∈ tuples (size (tysK K) σ.code) w → ∀ i : Fin w,
          el ρ ((appTuple (tysK K) w (σ ⇒ ρ).code u hh).getD i 0) =
            (el (σ ⇒ ρ) (u.getD i 0)).1 (el σ (hh.getD i 0)) := fun hh hh' i => by
        rw [appTuple_getD i.2]
        exact el_app hK (el_lt_of_tuples hK hu i.2) (el_lt_of_tuples hσK hh' i.2)
      have happT : ∀ hh : List ℕ, hh ∈ tuples (size (tysK K) σ.code) w →
          appTuple (tysK K) w (σ ⇒ ρ).code u hh ∈ tuples (size (tysK K) ρ.code) w := by
        intro hh hh'
        refine mem_tuples.mpr ⟨by simp [appTuple], ?_⟩
        intro x hx
        simp only [appTuple, List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        rw [size_tysK hρK, Ty.decode_code]
        unfold app
        have hu' : u.getD i 0 = idx (σ ⇒ ρ) (el (σ ⇒ ρ) (u.getD i 0)) :=
          (idx_getD _ (el_lt_of_tuples hK hu hi)).symm
        rw [hu', tabs_getD_getD hK _ (el_lt_of_tuples hσK hh' hi)]
        exact idx_lt _ _
      constructor
      · intro h G hG
        have : ∀ i : Fin w, idx σ (G i) < size (tysK K) σ.code := fun i => by
          rw [size_tysK hσK, Ty.decode_code]; exact idx_lt _ _
        have hh := ofFn_tuples (fun i => idx σ (G i)) this
        have hrel : (Model σ).rel w d (fun i => el σ ((List.ofFn fun i => idx σ (G i)).getD i 0)) := by
          have : (fun i : Fin w => el σ ((List.ofFn fun i => idx σ (G i)).getD i 0)) = G := by
            funext i; rw [ofFn_getD]; exact getD_idx σ (G i)
          rw [this]; exact hG
        have hres := (h _ hh hrel).2
        have : (fun i : Fin w => el ρ ((appTuple (tysK K) w (σ ⇒ ρ).code u
            (List.ofFn fun i => idx σ (G i))).getD i 0)) =
            fun i : Fin w => (el (σ ⇒ ρ) (u.getD i 0)).1 (G i) := by
          funext i; rw [happ _ hh i, ofFn_getD]; unfold el; rw [getD_idx]
        rw [this] at hres
        exact hres
      · intro hrel hh hh' hrσ
        refine ⟨happT hh hh', ?_⟩
        have := hrel _ hrσ
        have e : (fun i : Fin w => el ρ ((appTuple (tysK K) w (σ ⇒ ρ).code u hh).getD i 0)) =
            fun i : Fin w => (el (σ ⇒ ρ) (u.getD i 0)).1 (el σ (hh.getD i 0)) := by
          funext i; exact happ hh hh' i
        rw [e]
        exact this


/-! ## Rejection witnesses -/

theorem negValid_of_spec {tys : List TyTab} {c : ℕ} {t : List ℕ} {w : ℕ}
    {d : List (List ℕ × List ℕ)} {g : List ℕ} {lifts : List Lift}
    (hs : NegSpec tys c t w d g lifts) : negValid tys (c, t, w, d, g, lifts) = true := by
  simp only [negValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq, List.contains_iff_mem, Bool.not_eq_true', Bool.eq_false_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hs.hd, hs.hdom⟩, hs.hcod⟩, hs.hclo⟩, hs.hsub⟩, ?_⟩, hs.hg⟩, hs.hgl⟩, ?_⟩
  · intro e he u hu
    have := hs.hex e he u hu
    cases hcu : cond tys w d lifts e.1 u
    · rw [hcu] at this
      have hnot : u ∉ e.2 := fun h => by simpa using this.mp h
      simp [hnot]
    · rw [hcu] at this
      have hin : u ∈ e.2 := this.mpr rfl
      simp [hin]
  · intro hmem; exact hs.hng (by simpa [List.contains_iff_mem] using hmem)

open Classical in
/-- Every candidate table outside the carrier has a valid rejection witness. -/
theorem neg_exists {K : ℕ} {σ ρ : Ty} (hK : (σ ⇒ ρ).code ≤ K) {t : List ℕ}
    (ht : t ∈ tuples (size (tysK K) (cod (σ ⇒ ρ).code)) (size (tysK K) (dom (σ ⇒ ρ).code)))
    (hnot : t ∉ tablesOf (σ ⇒ ρ)) :
    ∃ n : Neg, n.1 = (σ ⇒ ρ).code ∧ n.2.1 = t ∧ negValid (tysK K) n = true := by
  have hc0 : (σ ⇒ ρ).code ≠ 0 := by simp [Ty.code]
  have hσK : σ.code ≤ K := le_trans (le_of_lt (by rw [← dom_code σ ρ]; exact dom_lt hc0)) hK
  have hρK : ρ.code ≤ K := le_trans (le_of_lt (by rw [← cod_code σ ρ]; exact cod_lt hc0)) hK
  rw [dom_code, cod_code, size_tysK hσK, size_tysK hρK, Ty.decode_code, Ty.decode_code] at ht
  obtain ⟨htl, htlt⟩ := mem_tuples.mp ht
  have htget : ∀ a, t.getD a 0 < (els ρ).length := fun a => by
    rcases Nat.lt_or_ge a t.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact htlt _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ h]
      obtain ⟨y, hy⟩ : ∃ y, y ∈ els ρ := ⟨default, mem_els ρ default⟩
      exact List.length_pos_of_mem hy
  let f : SieberBool σ → SieberBool ρ := fun y => el ρ (t.getD (idx σ y) 0)
  have hf : ¬ ((∀ a b, (Model σ).le a b → (Model ρ).le (f a) (f b)) ∧
      ∀ w (d : Test w) (g : Fin w → SieberBool σ), (Model σ).rel w d g →
        (Model ρ).rel w d (fun i => f (g i))) := by
    rintro ⟨hmono, hpres⟩
    apply hnot
    let F : SieberBool (σ ⇒ ρ) := ⟨f, hmono, hpres⟩
    have htab : table σ ρ F = t := by
      apply list_eq_of_getD (by simp [table, htl])
      intro a ha
      simp only [table, List.length_map, List.length_range] at ha
      simp only [table, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha,
        Option.map_some, Option.getD_some]
      show idx ρ (el ρ (t.getD (idx σ (el σ a)) 0)) = t.getD a 0
      unfold el
      rw [idx_getD σ ha, idx_getD ρ (htget a)]
    rw [← htab]
    exact List.mem_map_of_mem (mem_els _ F)
  obtain ⟨w, d, G, hG, hnG⟩ := exists_failure f hf
  let g : List ℕ := List.ofFn fun i => idx σ (G i)
  have hg : g ∈ tuples (size (tysK K) σ.code) w := ofFn_tuples _ (fun i => by
    rw [size_tysK hσK, Ty.decode_code]; exact idx_lt _ _)
  refine ⟨((σ ⇒ ρ).code, t, w, testList d, g, liftsK K w d), rfl, rfl, negValid_of_spec ?_⟩
  refine ⟨testList_bound d, hasLift_liftsK (le_trans (le_of_lt (dom_lt hc0)) hK),
    hasLift_liftsK (le_trans (le_of_lt (cod_lt hc0)) hK), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [liftsK, List.mem_map, List.mem_range] at he
    obtain ⟨c', hc', rfl⟩ := he
    by_cases h0 : c' = 0
    · exact Or.inl h0
    · exact Or.inr ⟨hasLift_liftsK (show dom c' ≤ K by have := dom_lt h0; omega),
        hasLift_liftsK (show cod c' ≤ K by have := cod_lt h0; omega)⟩
  · intro e he u hu
    simp only [liftsK, List.mem_map, List.mem_range] at he
    obtain ⟨c', -, rfl⟩ := he
    exact (List.mem_filter.mp hu).1
  · intro e he u hu
    simp only [liftsK, List.mem_map, List.mem_range] at he
    obtain ⟨c', hc', rfl⟩ := he
    simp only [List.mem_filter, decide_eq_true_eq, hu, true_and]
    have hdc : (Ty.decode c').code ≤ K := by rw [Ty.code_decode]; omega
    have hu' : u ∈ tuples (size (tysK K) (Ty.decode c').code) w := by rwa [Ty.code_decode]
    have := cond_iff d (Ty.decode c') hdc hu'
    rw [Ty.code_decode] at this
    exact this.symm
  · rw [dom_code]; exact hg
  · rw [dom_code, liftSet_liftsK σ hσK]
    refine List.mem_filter.mpr ⟨hg, ?_⟩
    simp only [decide_eq_true_eq]
    have : (fun i : Fin w => el σ (g.getD i 0)) = G := by
      funext i; simp only [g]; rw [ofFn_getD]; unfold el; rw [getD_idx]
    rw [this]; exact hG
  · rw [cod_code, liftSet_liftsK ρ hρK]
    intro hmem
    have hr := List.mem_filter.mp hmem
    simp only [decide_eq_true_eq] at hr
    apply hnG
    have : (fun i : Fin w => el ρ ((g.map fun gi => t.getD gi 0).getD i 0)) = fun i => f (G i) := by
      funext i
      have hlen : i.1 < g.length := by simp [g]
      rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map,
        ← List.getD_eq_getElem g 0 hlen]
      simp only [g]; rw [ofFn_getD]
    rw [this] at hr
    exact hr.2


/-! ## The certificate -/

theorem lookup_unique {β : Type} {l : List (ℕ × List β)} {c : ℕ} {v : List β} (hmem : (c, v) ∈ l)
    (huniq : ∀ e ∈ l, e.1 = c → e = (c, v)) :
    ((l.find? (fun e => e.1 == c)).map Prod.snd).getD [] = v := by
  cases hf : l.find? (fun e => e.1 == c) with
  | none =>
      have := List.find?_eq_none.mp hf _ hmem
      simp at this
  | some e =>
      have he : e.1 = c := by simpa using List.find?_some (p := fun e : ℕ × List β => e.1 == c) hf
      rw [huniq e (List.mem_of_find?_eq_some hf) he]
      rfl

/-- The body of a normal form of arrow type. -/
def lamBody {Γ : Ctx} {σ ρ : Ty} : Norm Γ (σ ⇒ ρ) true → Norm (σ :: Γ) ρ true
  | .lam b => b

theorem lamBody_eq {Γ : Ctx} {σ ρ : Ty} : ∀ n : Norm Γ (σ ⇒ ρ) true, n = .lam (lamBody n)
  | .lam _ => rfl

section
variable (U : Universal)

/-- A normal form defining `x` (from universality and normalisation). -/
noncomputable def witTerm {τ : Ty} (x : SieberBool τ) : Norm [] τ true :=
  Classical.choose (Definable.nf (U τ x))

theorem witTerm_spec {τ : Ty} (x : SieberBool τ) : (witTerm U x).embed.den = x :=
  Classical.choose_spec (Definable.nf (U τ x))

noncomputable def witCodes : Ty → List ℕ
  | .B => []
  | .arr σ ρ => (els (σ ⇒ ρ)).map fun x => (witTerm U x).embed.code

noncomputable def witK (K : ℕ) : List Wit :=
  (List.range (K + 1)).filterMap fun c => if c = 0 then none else some (c, witCodes U (Ty.decode c))

noncomputable def witTraceTy (c : ℕ) : Ty → List Entry
  | .B => []
  | .arr σ ρ => (els (σ ⇒ ρ)).flatMap fun x => entriesOf c (lamBody (witTerm U x)).embed

noncomputable def witTrace (K : ℕ) : List Entry :=
  (List.range (K + 1)).flatMap fun c => witTraceTy U c (Ty.decode c)

end

open Classical in
noncomputable def negsK (K : ℕ) : List Neg :=
  (List.range (K + 1)).flatMap fun c => if c = 0 then [] else
    (tuples (size (tysK K) (cod c)) (size (tysK K) (dom c))).filterMap fun t =>
      if h : ∃ n : Neg, n.1 = c ∧ n.2.1 = t ∧ negValid (tysK K) n = true then some (Classical.choose h)
      else none

/-- The certificate for a pair of closed terms. -/
noncomputable def certK (U : Universal) (K : ℕ) {Γ Δ : Ctx} {τ ρ : Ty} (M : Tm Γ τ) (N : Tm Δ ρ) : Cert :=
  (tysK K, witK U K, entriesOf 0 M ++ entriesOf 0 N ++ witTrace U K, negsK K)

theorem witnesses_witK (U : Universal) {K c : ℕ} (hc0 : c ≠ 0) (hcK : c ≤ K) :
    witnesses (witK U K) c = witCodes U (Ty.decode c) := by
  apply lookup_unique
  · simp only [witK, List.mem_filterMap, List.mem_range]
    exact ⟨c, by omega, by simp [hc0]⟩
  · intro e he hec
    simp only [witK, List.mem_filterMap, List.mem_range] at he
    obtain ⟨c', -, hc'⟩ := he
    split_ifs at hc' with h
    cases hc'
    simp only at hec
    subst hec
    rfl

theorem mem_entriesOf {β : ℕ} : ∀ {Γ : Ctx} {ρ : Ty} (P : Tm Γ ρ) {e : Entry}, e ∈ entriesOf β P →
    ∃ (Γ' : Ctx) (ρ' : Ty) (Q : Tm Γ' ρ') (env : List ℕ), e = entry β Q env
  | _, _, .var x, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, -, rfl⟩ := he; exact ⟨_, _, _, env, rfl⟩
  | _, .arr _ _, .lam M, e, he => by
      simp only [entriesOf, List.mem_append, List.mem_map] at he
      rcases he with ⟨env, -, rfl⟩ | he
      · exact ⟨_, _, _, env, rfl⟩
      · exact mem_entriesOf M he
  | _, _, .app M N, e, he => by
      simp only [entriesOf, List.mem_append, List.mem_map] at he
      rcases he with (⟨env, -, rfl⟩ | he) | he
      · exact ⟨_, _, _, env, rfl⟩
      · exact mem_entriesOf M he
      · exact mem_entriesOf N he
  | _, .B, .tt, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, -, rfl⟩ := he; exact ⟨_, _, _, env, rfl⟩
  | _, .B, .ff, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, -, rfl⟩ := he; exact ⟨_, _, _, env, rfl⟩
  | _, .B, .bot, e, he => by
      simp only [entriesOf, List.mem_map] at he
      obtain ⟨env, -, rfl⟩ := he; exact ⟨_, _, _, env, rfl⟩
  | _, .B, .ite C M N, e, he => by
      simp only [entriesOf, List.mem_append, List.mem_map] at he
      rcases he with ((⟨env, -, rfl⟩ | he) | he) | he
      · exact ⟨_, _, _, env, rfl⟩
      · exact mem_entriesOf C he
      · exact mem_entriesOf M he
      · exact mem_entriesOf N he


/-! ## Validity of the certificate -/

theorem table_inj {σ ρ : Ty} {x y : SieberBool (σ ⇒ ρ)} (h : table σ ρ x = table σ ρ y) : x = y := by
  apply Model.arr_ext
  intro z
  have hz : z = el σ (idx σ z) := (getD_idx σ z).symm
  have ha := idx_lt σ z
  have := congrArg (fun l => l.getD (idx σ z) 0) h
  simp only [table, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha,
    Option.map_some, Option.getD_some] at this
  rw [hz]
  exact idx_inj ρ this

theorem table_getD {σ ρ : Ty} (x : SieberBool (σ ⇒ ρ)) {a : ℕ} (ha : a < (els σ).length) :
    (table σ ρ x).getD a 0 = idx ρ (x.1 (el σ a)) := by
  simp [table, List.getD_eq_getElem?_getD, ha]

theorem covered_exists {K c : ℕ} (hcK : c ≤ K) : c = 0 ∨ ∃ e ∈ tysK K, e.1 = c := by
  rcases covered_tysK hcK with h | h
  · exact Or.inl h
  · right; simpa [List.any_eq_true] using h

theorem witTrace_mem (U : Universal) {K : ℕ} {σ ρ : Ty} (hK : (σ ⇒ ρ).code ≤ K)
    (x : SieberBool (σ ⇒ ρ)) {e : Entry}
    (he : e ∈ entriesOf (σ ⇒ ρ).code (lamBody (witTerm U x)).embed) : e ∈ witTrace U K := by
  simp only [witTrace, List.mem_flatMap, List.mem_range]
  refine ⟨(σ ⇒ ρ).code, by omega, ?_⟩
  rw [Ty.decode_code]
  simp only [witTraceTy, List.mem_flatMap]
  exact ⟨x, mem_els _ x, he⟩

theorem carrier_ok (U : Universal) {K : ℕ} {Γ Δ : Ctx} {τ₁ τ₂ : Ty} (M : Tm Γ τ₁) (N : Tm Δ τ₂)
    {c : ℕ} (hc0 : c ≠ 0) (hcK : c ≤ K) :
    carrierOK (certK U K M N) (c, tablesOf (Ty.decode c)) = true := by
  cases hdc : Ty.decode c with
  | B => rw [← Ty.code_decode c, hdc] at hc0; exact absurd rfl hc0
  | arr σ ρ =>
  have hc : c = (σ ⇒ ρ).code := by rw [← hdc, Ty.code_decode]
  subst hc
  have hσK : σ.code ≤ K := le_trans (le_of_lt (by rw [← dom_code σ ρ]; exact dom_lt hc0)) hcK
  have hρK : ρ.code ≤ K := le_trans (le_of_lt (by rw [← cod_code σ ρ]; exact cod_lt hc0)) hcK
  simp only [carrierOK, carrierOK.hasTabs, certK, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
    beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range, List.contains_iff_mem,
    List.any_eq_true]
  have hlen : (tablesOf (σ ⇒ ρ)).length = (els (σ ⇒ ρ)).length := by simp [tablesOf]
  refine ⟨⟨⟨⟨⟨⟨⟨hc0, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact covered_exists (by rw [dom_code]; exact hσK)
  · exact covered_exists (by rw [cod_code]; exact hρK)
  · intro t ht
    simp only [tablesOf, List.mem_map] at ht
    obtain ⟨x, -, rfl⟩ := ht
    rw [dom_code, cod_code, size_tysK hσK, size_tysK hρK, Ty.decode_code, Ty.decode_code]
    refine ⟨by simp [table], fun y hy => ?_⟩
    simp only [table, List.mem_map] at hy
    obtain ⟨a, -, rfl⟩ := hy
    exact idx_lt _ _
  · intro i hi j hj
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      intro heq
      apply hij
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at heq
      simp only [tablesOf, List.getElem_map] at heq
      have := table_inj heq
      rw [hlen] at hi hj
      exact (List.Nodup.getElem_inj_iff (els_nodup _)).mp this
  · rw [witnesses_witK U hc0 hcK, Ty.decode_code]; simp [witCodes, tablesOf]
  · intro i hi
    rw [hlen] at hi
    rw [witnesses_witK U hc0 hcK, Ty.decode_code]
    set x := (els (σ ⇒ ρ))[i] with hx
    have ht : (tablesOf (σ ⇒ ρ)).getD i [] = table σ ρ x := by
      rw [List.getD_eq_getElem _ _ (by rwa [hlen])]; simp [tablesOf, hx]
    have hw : (witCodes U (σ ⇒ ρ)).getD i 0 = (witTerm U x).embed.code := by
      rw [List.getD_eq_getElem _ _ (by simpa [witCodes] using hi)]; simp [witCodes, hx]
    rw [ht, hw]
    have hn := lamBody_eq (witTerm U x)
    have hden := witTerm_spec U x
    set b := lamBody (witTerm U x)
    have hcode : (witTerm U x).embed.code = 7 * Nat.pair σ.code b.embed.code + 1 := by
      rw [hn]; rfl
    simp only [witOK, hcode, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    have hq : (7 * Nat.pair σ.code b.embed.code + 1) / 7 = Nat.pair σ.code b.embed.code := by omega
    rw [hq, Nat.unpair_pair]
    refine ⟨⟨by omega, (dom_code σ ρ).symm⟩, fun a ha => ?_⟩
    rw [size_tysK hσK, Ty.decode_code] at ha
    apply List.any_eq_true.mpr
    refine ⟨entry (σ ⇒ ρ).code b.embed [a], ?_, ?_⟩
    · simp only [List.mem_append]
      right
      exact witTrace_mem U hcK x (entry_mem_entriesOf _ _ (cons_envList (by simp [envList]) ha))
    · simp only [entry, beq_iff_eq, List.map_cons, List.map_nil, cod_code]
      rw [table_getD x ha]
      congr 2
      rw [← hden, hn]
      simp only [Norm.embed, Tm.den, Tm.sem]
      rfl
  · intro t ht
    by_cases hmem : t ∈ tablesOf (σ ⇒ ρ)
    · exact Or.inl hmem
    · right
      have hex := neg_exists hcK ht hmem
      refine ⟨Classical.choose hex, ?_, ?_⟩
      · simp only [negsK, List.mem_flatMap, List.mem_range]
        refine ⟨(σ ⇒ ρ).code, by omega, ?_⟩
        simp only [hc0, if_false, List.mem_filterMap]
        exact ⟨t, ht, by simp [hex]⟩
      · obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
        exact ⟨⟨h1, h2⟩, h3⟩


theorem certK_valid (U : Universal) {K : ℕ} {Γ Δ : Ctx} {τ₁ τ₂ : Ty} (M : Tm Γ τ₁) (N : Tm Δ τ₂)
    (hM : AllTys (· ≤ K) M) (hN : AllTys (· ≤ K) N) : valid (certK U K M N) = true := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro e he
    simp only [certK, tysK, List.mem_filterMap, List.mem_range] at he
    obtain ⟨c, hcK, hce⟩ := he
    split_ifs at hce with hc0
    cases hce
    exact carrier_ok U M N hc0 (by omega)
  · have hsub : ∀ {Γ' ρ'} (P : Tm Γ' ρ') (β : ℕ),
        (∀ e ∈ entriesOf β P, e ∈ (certK U K M N).2.2.1) → ∀ e ∈ entriesOf β P, e ∈ (certK U K M N).2.2.1 :=
      fun _ _ h => h
    intro e he
    simp only [certK, List.mem_append] at he ⊢
    rcases he with (he | he) | he
    · exact entries_ok M hM (Or.inl rfl) (fun e he => by simp [certK, he]) e he
    · exact entries_ok N hN (Or.inl rfl) (fun e he => by simp [certK, he]) e he
    · simp only [witTrace, List.mem_flatMap, List.mem_range] at he
      obtain ⟨c, hcK, he⟩ := he
      cases hdc : Ty.decode c with
      | B => rw [hdc] at he; simp [witTraceTy] at he
      | arr σ ρ =>
      rw [hdc] at he
      simp only [witTraceTy, List.mem_flatMap] at he
      obtain ⟨x, -, he⟩ := he
      have hc : c = (σ ⇒ ρ).code := by rw [← hdc, Ty.code_decode]
      subst hc
      have hc0 : (σ ⇒ ρ).code ≠ 0 := by simp [Ty.code]
      have hσK : σ.code ≤ K := le_trans (le_of_lt (by rw [← dom_code σ ρ]; exact dom_lt hc0)) (by omega)
      have hρK : ρ.code ≤ K := le_trans (le_of_lt (by rw [← cod_code σ ρ]; exact cod_lt hc0)) (by omega)
      have hσc : σ.code < (σ ⇒ ρ).code := by rw [← dom_code σ ρ]; exact dom_lt hc0
      have hρc : ρ.code < (σ ⇒ ρ).code := by rw [← cod_code σ ρ]; exact cod_lt hc0
      have hctxK : ∀ σ' ∈ [σ], σ'.code ≤ K := by simp [hσK]
      have hctxc : ∀ σ' ∈ [σ], σ'.code < (σ ⇒ ρ).code := by simp [hσc]
      have hKb := (Norm.allTys (down_le K) (lamBody (witTerm U x)) hctxK (fun _ => hρK)).1
      have hβb := (Norm.allTys (down_lt (Nat.pos_of_ne_zero hc0)) (lamBody (witTerm U x)) hctxc
        (fun _ => hρc)).1
      exact entries_ok _ hKb (Or.inr hβb)
        (fun e' he' => by simp only [List.mem_append]; exact Or.inr (witTrace_mem U (by omega) x he'))
        e he

/-- The entry for a closed term at level 0 records its type and denotation. -/
theorem closedValue_certK (U : Universal) {K : ℕ} {τ : Ty} (M N : Tm [] τ) (P : Tm [] τ)
    (hP : P = M ∨ P = N) :
    closedValue (certK U K M N).2.2.1 P.code = some (τ.code, idx τ P.den) := by
  have hmem : entry 0 P [] ∈ (certK U K M N).2.2.1 := by
    simp only [certK, List.mem_append]
    rcases hP with rfl | rfl
    · exact Or.inl (Or.inl (entry_mem_entriesOf 0 _ (by simp [envList])))
    · exact Or.inl (Or.inr (entry_mem_entriesOf 0 _ (by simp [envList])))
  have hall : ∀ e ∈ (certK U K M N).2.2.1, (e.1 == [] && e.2.1 == P.code && e.2.2.1 == [] &&
      e.2.2.2.2.2 == 0) = true → e.2.2.2.1 = τ.code ∧ e.2.2.2.2.1 = idx τ P.den := by
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    simp only [certK, List.mem_append] at he
    rcases he with (he | he) | he
    · obtain ⟨Γ', ρ', Q, env, rfl⟩ := mem_entriesOf M he
      simp only [entry] at h1 h2 h3 ⊢
      have hΓ : Γ' = [] := List.map_eq_nil_iff.mp h1
      subst hΓ h3
      obtain ⟨rfl, hQ⟩ := Tm.code_inj Q P h2
      rw [eq_of_heq hQ]
      exact ⟨rfl, rfl⟩
    · obtain ⟨Γ', ρ', Q, env, rfl⟩ := mem_entriesOf N he
      simp only [entry] at h1 h2 h3 ⊢
      have hΓ : Γ' = [] := List.map_eq_nil_iff.mp h1
      subst hΓ h3
      obtain ⟨rfl, hQ⟩ := Tm.code_inj Q P h2
      rw [eq_of_heq hQ]
      exact ⟨rfl, rfl⟩
    · exfalso
      simp only [witTrace, List.mem_flatMap, List.mem_range] at he
      obtain ⟨c, -, he⟩ := he
      cases hdc : Ty.decode c with
      | B => rw [hdc] at he; simp [witTraceTy] at he
      | arr σ ρ =>
      rw [hdc] at he
      simp only [witTraceTy, List.mem_flatMap] at he
      obtain ⟨x, -, he⟩ := he
      obtain ⟨Γ', ρ', Q, env, rfl⟩ := mem_entriesOf _ he
      simp only [entry] at h4
      have hc : c = (σ ⇒ ρ).code := by rw [← hdc, Ty.code_decode]
      rw [hc] at h4
      simp [Ty.code] at h4
  unfold closedValue
  cases hf : (certK U K M N).2.2.1.find? (fun e => e.1 == [] && e.2.1 == P.code && e.2.2.1 == [] &&
      e.2.2.2.2.2 == 0) with
  | none =>
      have := List.find?_eq_none.mp hf _ hmem
      simp [entry] at this
  | some e =>
      obtain ⟨h1, h2⟩ := hall e (List.mem_of_find?_eq_some hf)
        (List.find?_some (p := fun e : Entry => e.1 == [] && e.2.1 == P.code && e.2.2.1 == [] &&
          e.2.2.2.2.2 == 0) hf)
      simp [h1, h2]

/-- **Completeness**: under universality, every pair of closed terms of the same type
has a certificate, and its verdict is equality of denotations. -/
theorem complete (U : Universal) {τ : Ty} (M N : Tm [] τ) :
    ∃ cert : Cert, verdict M.code N.code cert = some (idx τ M.den == idx τ N.den) := by
  let K := max (tmax M) (tmax N)
  have hM : AllTys (· ≤ K) M := AllTys.mono (fun n h => le_trans h (le_max_left _ _)) (allTys_tmax M)
  have hN : AllTys (· ≤ K) N := AllTys.mono (fun n h => le_trans h (le_max_right _ _)) (allTys_tmax N)
  refine ⟨certK U K M N, ?_⟩
  unfold verdict
  rw [if_pos (certK_valid U M N hM hN), closedValue_certK U M N M (Or.inl rfl),
    closedValue_certK U M N N (Or.inr rfl)]
  simp

end Check
end OR.Sieber
