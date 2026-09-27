import OR.Definability

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

noncomputable section

namespace OR

/-- Intrinsically typed, single-hole contexts, including holes under binders. -/
inductive PCtx (Γ : Ctx) (τ : Ty) : Ctx → Ty → Type where
  | hole {Δ : Ctx} : Ren Γ Δ → PCtx Γ τ Δ τ
  | lam {Δ : Ctx} {σ υ : Ty} : PCtx Γ τ (σ :: Δ) υ → PCtx Γ τ Δ (σ ⇒ υ)
  | appL {Δ : Ctx} {σ υ : Ty} : PCtx Γ τ Δ (σ ⇒ υ) → Tm Δ σ → PCtx Γ τ Δ υ
  | appR {Δ : Ctx} {σ υ : Ty} : Tm Δ (σ ⇒ υ) → PCtx Γ τ Δ σ → PCtx Γ τ Δ υ
  | fix {Δ : Ctx} {υ : Ty} : PCtx Γ τ Δ (υ ⇒ υ) → PCtx Γ τ Δ υ
  | succ {Δ : Ctx} : PCtx Γ τ Δ .nat → PCtx Γ τ Δ .nat
  | pred {Δ : Ctx} : PCtx Γ τ Δ .nat → PCtx Γ τ Δ .nat
  | ifzC {Δ : Ctx} : PCtx Γ τ Δ .nat → Tm Δ .nat → Tm Δ .nat → PCtx Γ τ Δ .nat
  | ifzL {Δ : Ctx} : Tm Δ .nat → PCtx Γ τ Δ .nat → Tm Δ .nat → PCtx Γ τ Δ .nat
  | ifzR {Δ : Ctx} : Tm Δ .nat → Tm Δ .nat → PCtx Γ τ Δ .nat → PCtx Γ τ Δ .nat

namespace PCtx

variable {Γ Δ Θ Ξ : Ctx} {τ σ υ κ : Ty}

 def plug (C : PCtx Γ τ Δ υ) (M : Tm Γ τ) : Tm Δ υ :=
  match C with
  | .hole r => Tm.rename r M
  | .lam C => .lam (plug C M)
  | .appL C N => .app (plug C M) N
  | .appR N C => .app N (plug C M)
  | .fix C => .fix (plug C M)
  | .succ C => .succ (plug C M)
  | .pred C => .pred (plug C M)
  | .ifzC C N P => .ifz (plug C M) N P
  | .ifzL N C P => .ifz N (plug C M) P
  | .ifzR N P C => .ifz N P (plug C M)

 def rename (r : Ren Δ Θ) (C : PCtx Γ τ Δ υ) : PCtx Γ τ Θ υ :=
  match C with
  | .hole s => .hole (Ren.comp r s)
  | .lam C => .lam (rename (Ren.lift r) C)
  | .appL C N => .appL (rename r C) (Tm.rename r N)
  | .appR N C => .appR (Tm.rename r N) (rename r C)
  | .fix C => .fix (rename r C)
  | .succ C => .succ (rename r C)
  | .pred C => .pred (rename r C)
  | .ifzC C N P => .ifzC (rename r C) (Tm.rename r N) (Tm.rename r P)
  | .ifzL N C P => .ifzL (Tm.rename r N) (rename r C) (Tm.rename r P)
  | .ifzR N P C => .ifzR (Tm.rename r N) (Tm.rename r P) (rename r C)

 theorem plug_rename (C : PCtx Γ τ Δ υ) (r : Ren Δ Θ) (M : Tm Γ τ) :
    (rename r C).plug M = Tm.rename r (C.plug M) := by
  induction C generalizing Θ <;> simp_all [rename, plug, Tm.rename, Tm.rename_comp]

/-- Substitution of one single-hole context into another remains single-hole. -/
 def compose (C : PCtx Δ υ Θ κ) (E : PCtx Γ τ Δ υ) : PCtx Γ τ Θ κ :=
  match C with
  | .hole r => rename r E
  | .lam C => .lam (compose C E)
  | .appL C N => .appL (compose C E) N
  | .appR N C => .appR N (compose C E)
  | .fix C => .fix (compose C E)
  | .succ C => .succ (compose C E)
  | .pred C => .pred (compose C E)
  | .ifzC C N P => .ifzC (compose C E) N P
  | .ifzL N C P => .ifzL N (compose C E) P
  | .ifzR N P C => .ifzR N P (compose C E)

@[simp] theorem plug_compose (C : PCtx Δ υ Θ κ) (E : PCtx Γ τ Δ υ) (M : Tm Γ τ) :
    (compose C E).plug M = C.plug (E.plug M) := by
  induction C <;> simp_all [compose, plug, plug_rename]

/-- Every constructor of the full context grammar is semantically monotone. -/
 theorem denote_mono (C : PCtx Γ τ Δ υ) {M N : Tm Γ τ}
    (h : denote M ≤ denote N) : denote (C.plug M) ≤ denote (C.plug N) := by
  induction C with
  | hole r =>
      intro ρ
      simpa only [plug, denote_rename] using h (pull r ρ)
  | lam C ih =>
      intro ρ a
      exact ih (ρ, a)
  | appL C P ih =>
      intro ρ
      exact ih ρ (denote P ρ)
  | appR P C ih =>
      intro ρ
      exact (denote P ρ).mono (ih ρ)
  | fix C ih =>
      intro ρ
      exact (Hom.fixMap _).mono (ih ρ)
  | succ C ih =>
      intro ρ
      exact Ground.succ_mono (ih ρ)
  | pred C ih =>
      intro ρ
      exact Ground.pred_mono (ih ρ)
  | ifzC C P Q ih =>
      intro ρ
      exact Ground.ifz_mono ⟨ih ρ, le_rfl, le_rfl⟩
  | ifzL P C Q ih =>
      intro ρ
      exact Ground.ifz_mono ⟨le_rfl, ih ρ, le_rfl⟩
  | ifzR P Q C ih =>
      intro ρ
      exact Ground.ifz_mono ⟨le_rfl, le_rfl, ih ρ⟩

 def close : {Δ : Ctx} → {υ : Ty} → PCtx Γ τ Δ υ → PCtx Γ τ [] (CloseTy Δ υ)
  | [], _, C => C
  | _ :: Δ, _, C => close (Δ := Δ) (.lam C)

 theorem plug_close : ∀ (Δ : Ctx) {υ : Ty} (C : PCtx Γ τ Δ υ) (M : Tm Γ τ),
    (close C).plug M = Tm.close (C.plug M) := by
  intro Δ
  induction Δ with
  | nil => intro υ C M; rfl
  | cons σ Δ ih =>
      intro υ C M
      exact ih (.lam C) M

 def applyEnv : (Δ : Ctx) → {υ : Ty} → PCtx Γ τ [] (CloseTy Δ υ) → Sub Δ [] → PCtx Γ τ [] υ
  | [], _, C, _ => C
  | _ :: Δ, _, C, θ => .appL (applyEnv Δ C (fun x => θ (.vs x))) (θ .vz)

 theorem plug_applyEnv : ∀ (Δ : Ctx) {υ : Ty}
    (C : PCtx Γ τ [] (CloseTy Δ υ)) (θ : Sub Δ []) (M : Tm Γ τ),
    (applyEnv Δ C θ).plug M = Tm.applyEnv Δ (C.plug M) θ := by
  intro Δ
  induction Δ with
  | nil => intro υ C θ M; rfl
  | cons σ Δ ih =>
      intro υ C θ M
      simp only [applyEnv, plug, Tm.applyEnv, ih]

 def closing (θ : Sub Γ []) : PCtx Γ τ [] τ :=
  applyEnv Γ (close (.hole Ren.id : PCtx Γ τ Γ τ)) θ

 theorem denote_closing (θ : Sub Γ []) (M : Tm Γ τ) :
    denoteClosed ((closing (τ := τ) θ).plug M) = denote M (subenv θ PUnit.unit) := by
  unfold closing
  rw [plug_applyEnv, plug_close]
  simp only [plug, Tm.rename_id]
  simpa only [Tm.closed_empty] using denote_apply_close Γ M θ PUnit.unit

end PCtx

/-- A closed semantic order failure yields a concrete numeral-distinguishing PCF context. -/
 theorem closed_separator : ∀ (τ : Ty) (M N : Tm [] τ),
    ¬ denoteClosed M ≤ denoteClosed N →
      ∃ C : PCtx [] τ [] .nat, ∃ q : ℕ,
        denoteClosed (C.plug M) = .val q ∧ denoteClosed (C.plug N) ≠ .val q := by
  intro τ
  induction τ with
  | nat =>
      intro M N h
      cases hM : denoteClosed M with
      | bot =>
          exfalso
          apply h
          rw [hM]
          exact bot_le
      | val q =>
          have hN : denoteClosed N ≠ .val q := by
            intro he
            apply h
            rw [hM, he]
          refine ⟨.hole Ren.id, q, ?_, ?_⟩
          · simpa only [PCtx.plug, Tm.rename_id] using hM
          · simpa only [PCtx.plug, Tm.rename_id] using hN
  | arr σ τ ihσ ihτ =>
      intro M N h
      let f : D (σ ⇒ τ) := denoteClosed M
      let g : D (σ ⇒ τ) := denoteClosed N
      have hex : ∃ a : D σ, ¬ f a ≤ g a := by
        by_contra hh
        apply h
        intro a
        by_contra ha
        exact hh ⟨a, ha⟩
      obtain ⟨a, ha⟩ := hex
      have ha' : ¬ f (projectionChain σ a).sup ≤ g (projectionChain σ a).sup := by
        simpa only [projection_approximates] using ha
      obtain ⟨n, hn⟩ := (projectionChain σ a).failure_at_finite_stage f.val g.val ha'
      obtain ⟨A, hA⟩ := approximant_definable σ n a
      have happ : ¬ denoteClosed (.app M A) ≤ denoteClosed (.app N A) := by
        change ¬ f (denoteClosed A) ≤ g (denoteClosed A)
        rw [hA]
        exact hn
      obtain ⟨C, q, hleft, hright⟩ := ihτ (.app M A) (.app N A) happ
      let E : PCtx [] (σ ⇒ τ) [] τ := .appL (.hole Ren.id) A
      refine ⟨C.compose E, q, ?_, ?_⟩
      · simpa only [PCtx.plug_compose, E, PCtx.plug, Tm.rename_id] using hleft
      · simpa only [PCtx.plug_compose, E, PCtx.plug, Tm.rename_id] using hright

/-- The open-term separator explicitly closes the hole with a definable finite environment. -/
 theorem semantic_separator {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ)
    (h : ¬ denote M ≤ denote N) :
    ∃ C : PCtx Γ τ [] .nat, ∃ q : ℕ,
      denoteClosed (C.plug M) = .val q ∧ denoteClosed (C.plug N) ≠ .val q := by
  have hex : ∃ ρ : Env Γ, ¬ denote M ρ ≤ denote N ρ := by
    by_contra hh
    apply h
    intro ρ
    by_contra hρ
    exact hh ⟨ρ, hρ⟩
  obtain ⟨ρ, hρ⟩ := hex
  have hρ' : ¬ denote M (envProjectionChain Γ ρ).sup ≤ denote N (envProjectionChain Γ ρ).sup := by
    simpa only [envProjection_approximates] using hρ
  obtain ⟨n, hn⟩ := (envProjectionChain Γ ρ).failure_at_finite_stage (denote M).val (denote N).val hρ'
  obtain ⟨θ, hθ⟩ := finite_environment_definability n Γ (approximateEnv n ρ)
  let E : PCtx Γ τ [] τ := PCtx.closing θ
  have hclosed : ¬ denoteClosed (E.plug M) ≤ denoteClosed (E.plug N) := by
    change ¬ denoteClosed ((PCtx.closing θ).plug M) ≤ denoteClosed ((PCtx.closing θ).plug N)
    rw [PCtx.denote_closing, PCtx.denote_closing, hθ, include_approximateEnv]
    exact hn
  obtain ⟨C, q, hleft, hright⟩ := closed_separator τ (E.plug M) (E.plug N) hclosed
  exact ⟨C.compose E, q, by simpa only [PCtx.plug_compose] using hleft,
    by simpa only [PCtx.plug_compose] using hright⟩

 def ContextualDenLE {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) : Prop :=
  ∀ C : PCtx Γ τ [] .nat, denoteClosed (C.plug M) ≤ denoteClosed (C.plug N)

 def ContextualDenEq {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) : Prop :=
  ContextualDenLE M N ∧ ContextualDenLE N M

 theorem full_abstraction_den {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualDenLE M N ↔ denote M ≤ denote N := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨C, q, hleft, hright⟩ := semantic_separator M N hn
    apply hright
    have ho := h C
    rw [hleft] at ho
    exact (Flat.val_le_iff _ _).mp ho
  · intro h C
    exact C.denote_mono h PUnit.unit

 theorem full_abstraction_den_eq {Γ : Ctx} {τ : Ty} (M N : Tm Γ τ) :
    ContextualDenEq M N ↔ denote M = denote N := by
  constructor
  · rintro ⟨hMN, hNM⟩
    exact le_antisymm ((full_abstraction_den M N).mp hMN) ((full_abstraction_den N M).mp hNM)
  · intro h
    exact ⟨(full_abstraction_den M N).mpr h.le, (full_abstraction_den N M).mpr h.symm.le⟩

end OR
