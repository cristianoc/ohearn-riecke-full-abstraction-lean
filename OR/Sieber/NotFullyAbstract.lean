import OR.Adequacy
import OR.Sieber.Main
import OR.Sieber.Algebraic
import OR.Sieber.Reinterpret

/-!
# The ordinary Sieber model over `ℕ⊥` is not inequationally fully abstract

`SIEBER.md`, Section 4.  Assume Loader's theorem and two published results, stated
here as hypotheses:

* `NS.MilnerPlotkin`: Milner's theorem that in an order-extensional, ω-algebraic
  model of PCF, inequational full abstraction makes every compact element definable
  (R. Milner, *Fully abstract models of typed λ-calculi*, TCS 4, 1977), specialised
  to `D^N`.  Its premises are proved for `D^N` in `Algebraic` and are discharged below.
* `MullerGrade1`: Müller's Game Term Theorem at grade 1 (F. Müller, *On Berry's
  conjectures about the stable order in PCF*, LMCS 8(4), 2012, Theorem 4.12 with
  `M = N`, `i = j = 1`): a closed term `M` with `Ψ¹ M ≃ M` (a finite term of grade 1,
  Definition 3.1) is observationally equivalent to a game term of grade 1.

Then `D^N` is not inequationally fully abstract.  Otherwise every Boolean element `h`
would give the compact element `i h`, a term `M` denoting it, a game term `G` with
`⟦G⟧ = i h`, and finally `⟦Gᴮ⟧_B = h` (Lemma 11), so the Boolean Sieber model would be
universal, contradicting `sieber_not_universal`.
-/

set_option autoImplicit false

namespace OR.NS

/-- Inequational full abstraction of `D^N` for closed terms.  Full abstraction for
open terms implies this, so its negation is the stronger statement. -/
def InequationallyFullyAbstract : Prop :=
  ∀ (τ : OR.Ty) (M N : OR.Tm [] τ), ContextualOpLE M N ↔ denoteClosed M ≤ denoteClosed N

/-- Milner's compact-definability theorem, instantiated at `D^N`, with its
premises as explicit antecedents. -/
def MilnerPlotkin : Prop :=
  OrderExtensional → OmegaAlgebraic → LeastFixedPoints → InequationallyFullyAbstract →
    ∀ (τ : OR.Ty) (x : D τ), Compact x → ∃ M : OR.Tm [] τ, denoteClosed M = x

end OR.NS

namespace OR.Sieber

/-- Müller's Game Term Theorem at grade 1.  Grade-1 game terms (`λx⃗. m` with
`m ∈ {0, 1}`, `⊥`, and `λx⃗. case₁ (y M⃗) N₀ N₁`) are, up to `⊥^σ ≃ λx⃗. ⊥`, images
`embed G` of Boolean terms; allowing every Boolean term only weakens the hypothesis. -/
def MullerGrade1 : Prop :=
  ∀ (τ : Ty) (M : OR.Tm [] (natTy τ)),
    ContextualOpEq (.app (projectionTerm (natTy τ) 1) M) M →
      ∃ G : Tm [] τ, ContextualOpEq (embed G) M

/-- **Theorem.** Assuming Loader's theorem, Milner's compact-definability theorem and
Müller's Game Term Theorem, the ordinary Sieber model over `ℕ⊥` is not inequationally
fully abstract for PCF. -/
theorem natural_sieber_not_inequationally_fully_abstract (hL : Loader)
    (hMP : NS.MilnerPlotkin) (hMu : MullerGrade1) : ¬ NS.InequationallyFullyAbstract := by
  intro hFA
  obtain ⟨τ, h, hnd⟩ := sieber_not_universal hL
  apply hnd
  have hc : Compact ((tr τ).i h) := NS.level_compact (natTy τ) 1 _ (psi_i τ h)
  obtain ⟨M, hM⟩ :=
    hMP NS.orderExtensional NS.omegaAlgebraic NS.leastFixedPoints hFA _ _ hc
  have hPsi : NS.denoteClosed (.app (projectionTerm (natTy τ) 1) M) = NS.denoteClosed M := by
    change NS.psi (natTy τ) 1 (NS.denoteClosed M) = _
    rw [hM, psi_i]
  obtain ⟨G, hG⟩ := hMu τ M ⟨(hFA _ _ _).2 hPsi.le, (hFA _ _ _).2 hPsi.ge⟩
  have hGx : NS.denoteClosed (embed G) = (tr τ).i h :=
    le_antisymm (((hFA _ _ _).1 hG.1).trans hM.le) (hM.ge.trans ((hFA _ _ _).1 hG.2))
  exact ⟨G, den_of_embed G h hGx⟩

end OR.Sieber
