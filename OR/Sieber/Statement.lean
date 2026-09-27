import OR.Sieber.Soundness

/-!
# Sieber's relations do not suffice

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

/-- Sieber's ordinary sequentiality relations do not give a universal (hence,
fully abstract) model of finitary PCF. -/
def SieberNotUniversal : Prop :=
  Loader → ∃ (τ : Ty) (f : SieberBool τ), ¬ Definable f

end OR.Sieber
