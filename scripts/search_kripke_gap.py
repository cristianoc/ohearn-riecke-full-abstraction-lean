#!/usr/bin/env python3
"""Concrete-counterexample search: reduced form.

Key reduction from the actual O'Hearn--Riecke finite-world construction.

For a predicate h : D_sigma -> B in the ordinary Boolean Sieber model, consider
the empty Kripke world and its one-variable extension

    []  --->  [sigma].

At [sigma], use the canonical argument

    argument(x) = x

(the fresh variable; this is exactly the argument used in
strong_finite_definability).  Pulling the constant family h from [] to [sigma]
and applying it to this argument gives the ground map

    x |-> h(x).

The selected finite Kripke test has, at ground type, precisely the definable
maps from finite environments.  Hence the constant h fails this Kripke test
exactly when h is not PCF-definable.

Therefore a concrete separation needs no independent Kripke CSP:

  FIND h : D_sigma -> B such that
    (1) h belongs to the ordinary Sieber carrier (preserves every ordinary
        finite-arity sequentiality relation), and
    (2) h is not Boolean-PCF definable.

Then the explicit Kripke witness is automatically:
    world      = []
    extension  = [sigma]
    argument   = fresh variable x:sigma
    bad ground = x |-> h(x).

Sieber's low-order theorem means the first possible predicate has order >= 4
(with ground order 0).  Search predicate types in increasing syntax size/order.

Practical strategy
------------------
Do NOT enumerate all 3^|D_sigma| predicates.

Represent h by 3-valued variables h[a], one for each a in D_sigma.

Ordinary-carrier constraints:
  * monotonicity: a <= b ==> h[a] <= h[b];
  * relation preservation: for every arity w, test R, and R-related tuple
      (a_1,...,a_w) in D_sigma,
    require (h[a_1],...,h[a_w]) in R_B.

Definability exclusion:
  enumerate/characterise the definable predicates at sigma->B and add
  h != d for each definable d.  Prefer a finite semantic closure algorithm
  over raw term enumeration.

Use counterexample-guided generation:
  1. solve with monotonicity + currently known relation constraints;
  2. search for an ordinary sequentiality relation violated by the candidate;
  3. add that finite constraint and repeat;
  4. if no violation exists and h is outside the definable closure, we have
     the desired explicit counterexample.

The companion search_sieber_counterexample.py computes the lower carriers.
"""

def kripke_witness_description(sigma: str) -> str:
    return f"""Concrete Kripke witness for h : {sigma} -> B:
  source world:      []
  extended world:    [{sigma}]
  world morphism:    forget the fresh {sigma} variable
  related argument:  x |-> x
  resulting ground:  x |-> h(x)
  failure reason:    this ground map is not PCF-definable
"""

if __name__ == "__main__":
    print(kripke_witness_description("sigma"))
