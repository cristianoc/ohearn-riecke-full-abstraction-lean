import OR.Sieber.Normal

/-!
# The head-call lemma at `τ₀ = ((B ⇒ B) ⇒ B) ⇒ B`

Lemma 4, Corollary 5 and Theorem 6 of `HEADCALL.md`, in Sieber's model.

* `headCall`: a closed term `t : τ₀` either denotes a constant function, or has a
  definable `Ψ : τ₁ ⇒ (B ⇒ B)`, of the form `λF. λz. M`, with
  `⟦t⟧ F ≠ ⊥ → F (Ψ F) ≠ ⊥`, and `⟦λF. if F (λz. M) then G else G⟧ = ⟦t⟧` where `λF. G`
  is the normal form of `t`.
* `firstCall`: the corollary for a table `h` defined on a set `S` of arguments.
* `firstCall_compat`: the first-call compatibility test.

The term language has no fixed-point constant, so Lemma 1 of `HEADCALL.md` has
nothing to eliminate here.
-/

set_option autoImplicit false

namespace OR.Sieber

/-- `τ₁ = (B ⇒ B) ⇒ B`. -/
abbrev τ₁ : Ty := (.B ⇒ .B) ⇒ .B
/-- `τ₀ = τ₁ ⇒ B`. -/
abbrev τ₀ : Ty := τ₁ ⇒ .B

/-! ## Shape of normal forms in the context `F : τ₁` -/

/-- A neutral term with only `F : τ₁` free has type `τ₁` or `B`. -/
theorem Norm.neutral_ty : ∀ {Γ : Ctx} {τ : Ty} {b : Bool} (_ : Norm Γ τ b),
    Γ = [τ₁] → b = false → τ = τ₁ ∨ τ = .B
  | _, _, _, .var x, hΓ, _ => by
      subst hΓ
      cases x with
      | vz => exact Or.inl rfl
      | vs y => cases y
  | _, _, _, .app n _, hΓ, _ => by
      rcases Norm.neutral_ty n hΓ rfl with h | h
      · cases h; exact Or.inr rfl
      · cases h
  | _, _, _, .up _, _, h => by cases h
  | _, _, _, .lam _, _, h => by cases h
  | _, _, _, .tt, _, h => by cases h
  | _, _, _, .ff, _, h => by cases h
  | _, _, _, .bot, _, h => by cases h
  | _, _, _, .ite _ _ _, _, h => by cases h

/-- A neutral ground term with only `F : τ₁` free is a call `F (λz. M)`. -/
theorem Norm.neutral_B (n : Norm [τ₁] .B false) :
    ∃ m : Norm [.B, τ₁] .B true, n = .app (.var .vz) (.lam m) := by
  cases n with
  | var x =>
      cases x with
      | vs y => cases y
  | app n' m =>
      cases n' with
      | var x =>
          cases x with
          | vz => cases m with
            | lam m => exact ⟨m, rfl⟩
          | vs y => cases y
      | app n'' _ =>
          rcases Norm.neutral_ty n'' rfl rfl with h | h <;> cases h

/-- The bottom element of `τ₁`, the denotation of `λf. ⊥`. -/
def botτ₁ : SieberBool τ₁ := (Tm.lam .bot : Tm [] τ₁).den

/-- The environment `F : τ₁`. -/
def envF (F : SieberBool τ₁) : Env [τ₁] := (PUnit.unit, F)

theorem envF_surj (ρ : Env [τ₁]) : ρ = envF ρ.2 := rfl

/-- The function `F ↦ λz. ⟦M⟧[F, z]`, as an element of `τ₁ ⇒ (B ⇒ B)`. -/
def callArg (M : Tm [.B, τ₁] .B) : SieberBool (τ₁ ⇒ (.B ⇒ .B)) := (Tm.lam (Tm.lam M)).den

theorem callArg_apply (M : Tm [.B, τ₁] .B) (F : SieberBool τ₁) :
    (callArg M).1 F = (Tm.lam M).sem.1 (envF F) := rfl

/-- **(∗) of `HEADCALL.md`.** A normal ground term `G` in `F : τ₁` is constant in `F`,
or some call argument `λz. M` has `⟦G⟧ ≠ ⊥ → F (λz. ⟦M⟧) ≠ ⊥` for every `F`. -/
theorem Norm.headCall : ∀ (G : Norm [τ₁] .B true),
    (∀ F F', G.embed.sem.1 (envF F) = G.embed.sem.1 (envF F')) ∨
    ∃ M : Tm [.B, τ₁] .B, ∀ F, G.embed.sem.1 (envF F) ≠ .bot → F.1 ((callArg M).1 F) ≠ .bot
  | .up n => by
      obtain ⟨m, rfl⟩ := Norm.neutral_B n
      exact Or.inr ⟨m.embed, fun F h => h⟩
  | .tt => Or.inl fun _ _ => rfl
  | .ff => Or.inl fun _ _ => rfl
  | .bot => Or.inl fun _ _ => rfl
  | .ite c a b => by
      have hsem : ∀ F, (Norm.ite c a b).embed.sem.1 (envF F) =
          Val.ite (c.embed.sem.1 (envF F)) (a.embed.sem.1 (envF F)) (b.embed.sem.1 (envF F)) :=
        fun _ => rfl
      rcases Norm.headCall c with hc | ⟨M, hM⟩
      · have hc' : ∀ F, c.embed.sem.1 (envF F) = c.embed.sem.1 (envF botτ₁) := fun F => hc F botτ₁
        cases hv : c.embed.sem.1 (envF botτ₁) with
        | bot =>
            refine Or.inl fun F F' => ?_
            rw [hsem, hsem, hc' F, hc' F', hv]; rfl
        | tt =>
            rcases Norm.headCall a with ha | ⟨M, hM⟩
            · refine Or.inl fun F F' => ?_
              rw [hsem, hsem, hc' F, hc' F', hv]; exact ha F F'
            · refine Or.inr ⟨M, fun F h => hM F ?_⟩
              rw [hsem, hc' F, hv] at h; exact h
        | ff =>
            rcases Norm.headCall b with hb | ⟨M, hM⟩
            · refine Or.inl fun F F' => ?_
              rw [hsem, hsem, hc' F, hc' F', hv]; exact hb F F'
            · refine Or.inr ⟨M, fun F h => hM F ?_⟩
              rw [hsem, hc' F, hv] at h; exact h
      · refine Or.inr ⟨M, fun F h => hM F ?_⟩
        intro hcb
        rw [hsem, hcb] at h
        exact h rfl

/-! ## Lemma 4 -/

/-- The body of a normal form of arrow type. -/
def Norm.body {Γ : Ctx} {σ τ : Ty} : Norm Γ (σ ⇒ τ) true → Norm (σ :: Γ) τ true
  | .lam n => n

theorem Norm.eq_lam_body {Γ : Ctx} {σ τ : Ty} : ∀ n : Norm Γ (σ ⇒ τ) true, n = .lam n.body
  | .lam _ => rfl

/-- The body `G` of the normal form `λF. G` of a closed term of type `τ₀`. -/
def Tm.nfBody (t : Tm [] τ₀) : Tm [τ₁] .B := t.nf.body.embed

theorem Tm.den_eq_nfBody (t : Tm [] τ₀) (F : SieberBool τ₁) :
    t.den.1 F = t.nfBody.sem.1 (envF F) := by
  have h := Tm.nf_sound t PUnit.unit
  rw [Norm.eq_lam_body t.nf] at h
  show t.den.1 F = _
  rw [Tm.den, ← h]
  rfl

/-- `t* = λF. if F (λz. M) then G else G`. -/
def headCallTerm (G : Tm [τ₁] .B) (M : Tm [.B, τ₁] .B) : Tm [] τ₀ :=
  .lam (.ite (.app (.var .vz) (.lam M)) G G)

/-- **Lemma 4 (head-call lemma).** A closed `t : τ₀` with normal form `λF. G` either
denotes a constant function, or there is `M` with only `F : τ₁` and `z : B` free such
that, with `Ψ = ⟦λF. λz. M⟧` (definable, hence monotone, by construction):
1. `⟦t⟧ F ≠ ⊥ → F (Ψ F) ≠ ⊥` for every `F`;
2. `⟦λF. if F (λz. M) then G else G⟧ = ⟦t⟧`;
3. `Ψ F = ⟦λz. M⟧[F]`, and `Ψ` is monotone. -/
theorem headCall (t : Tm [] τ₀) :
    (∀ F F', t.den.1 F = t.den.1 F') ∨
    ∃ M : Tm [.B, τ₁] .B,
      (∀ F, t.den.1 F ≠ .bot → F.1 ((callArg M).1 F) ≠ .bot) ∧
      (headCallTerm t.nfBody M).den = t.den ∧
      (∀ F, (callArg M).1 F = (Tm.lam M).sem.1 (envF F)) ∧
      (∀ F F', (Model τ₁).le F F' →
        (Model (.B ⇒ .B)).le ((callArg M).1 F) ((callArg M).1 F')) := by
  rcases Norm.headCall t.nf.body with hc | ⟨M, hM⟩
  · refine Or.inl fun F F' => ?_
    rw [Tm.den_eq_nfBody, Tm.den_eq_nfBody]
    exact hc F F'
  · have h1 : ∀ F, t.den.1 F ≠ .bot → F.1 ((callArg M).1 F) ≠ .bot := fun F h =>
      hM F (by rw [Tm.den_eq_nfBody] at h; exact h)
    refine Or.inr ⟨M, h1, ?_, fun _ => rfl, fun F F' h => (callArg M).2.1 F F' h⟩
    apply Model.arr_ext
    intro F
    show Val.ite (F.1 ((callArg M).1 F)) (t.nfBody.sem.1 (envF F)) (t.nfBody.sem.1 (envF F)) =
      t.den.1 F
    rw [← Tm.den_eq_nfBody]
    cases hF : F.1 ((callArg M).1 F) with
    | bot =>
        by_contra hne
        exact h1 F (Ne.symm hne) hF
    | tt => rfl
    | ff => rfl

/-! ## Corollary 5 and Theorem 6 -/

/-- A table `h` on `τ₁` is definable on `S` when a closed term agrees with it on `S`. -/
def DefinableOn (S : Set (SieberBool τ₁)) (h : SieberBool τ₁ → Val) : Prop :=
  ∃ t : Tm [] τ₀, ∀ F ∈ S, t.den.1 F = h F

/-- **Corollary 5.** If `h` is definable on `S ∋ ⊥` and `h ⊥ = ⊥`, some definable
`Ψ : τ₁ ⇒ (B ⇒ B)` has `F (Ψ F) ≠ ⊥` on the support of `h` in `S`. -/
theorem firstCall {S : Set (SieberBool τ₁)} {h : SieberBool τ₁ → Val}
    (hbotS : botτ₁ ∈ S) (hbot : h botτ₁ = .bot) (hdef : DefinableOn S h) :
    ∃ Ψ : SieberBool (τ₁ ⇒ (.B ⇒ .B)), Definable Ψ ∧
      ∀ F ∈ S, h F ≠ .bot → F.1 (Ψ.1 F) ≠ .bot := by
  obtain ⟨t, ht⟩ := hdef
  rcases headCall t with hc | ⟨M, h1, -⟩
  · refine ⟨callArg .bot, ⟨_, rfl⟩, fun F hF hne => absurd ?_ hne⟩
    rw [← ht F hF, hc F botτ₁, ht _ hbotS, hbot]
  · exact ⟨callArg M, ⟨_, rfl⟩, fun F hF hne => h1 F (by rw [ht F hF]; exact hne)⟩

/-- Compatibility in `B ⇒ B`: a common upper bound. -/
def Compat (a b : SieberBool (.B ⇒ .B)) : Prop :=
  ∃ c, (Model (.B ⇒ .B)).le a c ∧ (Model (.B ⇒ .B)).le b c

/-- **Theorem 6 (first-call compatibility test).** Let `h ⊥ = ⊥` with `⊥ ∈ S`, let
`m i` be support points of `h` in `S`, and let `P` relate pairs with a common upper
bound. If no choice `a i` with `m i (a i) ≠ ⊥` is compatible along `P`, then `h` is not
definable on `S`. -/
theorem firstCall_compat {S : Set (SieberBool τ₁)} {h : SieberBool τ₁ → Val}
    (hbotS : botτ₁ ∈ S) (hbot : h botτ₁ = .bot)
    {ι : Type} (m : ι → SieberBool τ₁) (hmS : ∀ i, m i ∈ S) (hm : ∀ i, h (m i) ≠ .bot)
    (P : ι → ι → Prop)
    (hP : ∀ i j, P i j → ∃ u, (Model τ₁).le (m i) u ∧ (Model τ₁).le (m j) u)
    (hno : ¬ ∃ a : ι → SieberBool (.B ⇒ .B),
      (∀ i, (m i).1 (a i) ≠ .bot) ∧ ∀ i j, P i j → Compat (a i) (a j)) :
    ¬ DefinableOn S h := by
  intro hdef
  obtain ⟨Ψ, -, hΨ⟩ := firstCall hbotS hbot hdef
  refine hno ⟨fun i => Ψ.1 (m i), fun i => hΨ _ (hmS i) (hm i), fun i j hij => ?_⟩
  obtain ⟨u, hiu, hju⟩ := hP i j hij
  exact ⟨Ψ.1 u, Ψ.2.1 _ _ hiu, Ψ.2.1 _ _ hju⟩

end OR.Sieber
