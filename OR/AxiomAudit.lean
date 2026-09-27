import OR

/-!
Run only after the library builds:

    lake env lean OR/AxiomAudit.lean

The accompanying checker accepts only `propext`, `Classical.choice`, and
`Quot.sound`. This file does not assert in advance which axioms Lean will report.
-/

#print axioms OR.finite_interpolation
#print axioms OR.sequential_iff_primitive_closed
#print axioms OR.Hom.fixMap_unfold
#print axioms OR.Tm.subst_comp
#print axioms OR.denote_subst
#print axioms OR.projection_approximates
#print axioms OR.finite_level
#print axioms OR.strong_finite_definability
#print axioms OR.finite_definability
#print axioms OR.compact_iff_finite_level
#print axioms OR.semantic_separator
#print axioms OR.full_abstraction_den
#print axioms OR.fundamental
#print axioms OR.adequacy
#print axioms OR.full_abstraction_op
#print axioms OR.full_abstraction_op_eq
#print axioms OR.full_abstraction_termination
#print axioms OR.Examples.no_parallel_or
#print axioms OR.Sieber.Tm.code_inj
#print axioms OR.Sieber.Tm.obs_eq_den
#print axioms OR.Sieber.finite_car
#print axioms OR.Sieber.universal_fully_abstract
#print axioms OR.Sieber.Tm.nf_sound
#print axioms OR.Sieber.Check.verdict_sound
#print axioms OR.Sieber.Check.complete
#print axioms OR.Sieber.Check.verdict_prim
#print axioms OR.Sieber.sieber_not_universal
