import OR.Sieber.Soundness

/-!
# Sieber's model is not universal

**Statement.** If observational equivalence of finitary PCF is undecidable
(Loader's theorem), then Sieber's model has an element that is not the
denotation of any closed term.

Everything in the statement is defined in `Syntax`, `Standard` and `Model`:
`Loader`, `SieberBool`, `Definable`.

It is proved as `sieber_not_universal` in `Main` (see `SIEBER.md` for the
argument): universality would make observational equivalence computable, since
both it and its negation would be witnessed by finite certificates accepted by a
primitive recursive checker.
-/

set_option autoImplicit false

namespace OR.Sieber

/-- Sieber's ordinary sequentiality relations do not give a universal model of
finitary PCF: some element is not the denotation of a closed term. (This is not
a statement about full abstraction; see `universal_fully_abstract` for the only
implication proved between the two.) -/
def SieberNotUniversal : Prop :=
  Loader → ∃ (τ : Ty) (f : SieberBool τ), ¬ Definable f

end OR.Sieber
