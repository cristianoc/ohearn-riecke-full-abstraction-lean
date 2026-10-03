# GPU search for a concrete Sieber counterexample

Implementation specification for an agent running on an Apple-silicon MacBook Pro.

Use **MLX custom Metal kernels**. Python/MLX orchestrates; handwritten integer Metal kernels perform exhaustive checks. Do not port `scripts/search_sieber_counterexample.py` literally: it is experimental/stale and its Python nesting is exactly what this design removes.

## 1. Mathematical target

Flat Boolean domain: `BOT=0, TT=1, FF=2`, with BOT below TT and FF.

Reference carriers:
```
D0 = B                                      size 3
D1 = D_(B -> B)                            size 11
D2 = D_((B -> B) -> B)                    size 355
```
At D2 the ordinary-Sieber carrier coincides with PCF-definable elements. Reproducing 3/11/355 is the first regression gate.

Initial order-3 target:
```
tau0 = ((B -> B) -> B) -> B
h : D2 -> B
```
Universality is known through order 2 and fails somewhere at exact order 3. If tau0 is universal, widen order-3 types; do not move to order 4.

## 2. Tests and layouts

For arity w:
```
S^w_(A,B) = { g:w->B |
  (exists i in A, g[i]=BOT) or (g is constant on B) }
```
A test is a finite intersection. Canonicalize by its actual subset of B^w, as a bitset of 3^w bits.

Ordinary logical lifting:
```
(f_0,...,f_(w-1)) in R_(sigma->tau)
iff
for every (x_0,...,x_(w-1)) in R_sigma,
(f_0 x_0,...,f_(w-1) x_(w-1)) in R_tau.
```

Packed layouts:
```
D1 : uint8[11][3]
D2 : uint8[355][11]
h  : uint8[355]
```
For arity 3 use a uint32 ground-relation mask; index (a,b,c) by 9*a+3*b+c.
Precompute only the lift to D1:
```
rel1_w : uint16[nrel][w]
```
Never materialize R_D2.

## 3. CPU oracle

Implement deliberately slow reference functions:
```python
ground_member(R, values)
related_D1_tuple(R, indices)
related_D2_tuple(R, indices)
candidate_preserves(R, h)
```
Every GPU witness must pass:
```python
assert related_D2_tuple(R, witness_inputs)
assert not ground_member(R, tuple(h[i] for i in witness_inputs))
```
Differential-test CPU/GPU before large runs.

## 4. Arity-3 Metal kernel

Naive validated version: one logical thread per D2^3 tuple:
```
355^3 = 44,738,875
```
Decode:
```c
uint i = tid / (355u*355u);
uint j = (tid / 355u) % 355u;
uint k = tid % 355u;
```
First cheap check:
```c
uint out = 9*h[i] + 3*h[j] + h[k];
if (R_contains(out)) return;
```
Then scan rel1_3. For each (a,b,c):
```c
uint va=D2[11*i+a], vb=D2[11*j+b], vc=D2[11*k+c];
if (!R_contains(9*va+3*vb+vc)) return;
```
If the whole scan succeeds, atomically claim a result slot and write i,j,k. Threads return early if another witness was found.

### Output-bucket dispatch

After validation partition H0/H1/H2 by h output. For each forbidden output (u,v,z) not in R dispatch only H_u x H_v x H_z. This can shrink the grid drastically.

## 5. Batch candidates and CEGAR

Store:
```
H       : uint8[num_candidates][355]
alive   : atomic_uint[num_candidates]
witness : uint16[num_candidates][3]
```
Add candidate id as a grid dimension. Once a witness is found, mark it dead.

Maintain an ordered learned bank of tests:
1. generate and semantically deduplicate candidates;
2. check monotonicity on CPU;
3. run learned cheap tests;
4. run all distinct arity-3 tests;
5. push survivors to arity 4;
6. search for a higher-arity rejecting test;
7. retain useful rejecting relations permanently;
8. repeat.

Persist relation masks and certificates.

## 6. Arity 4 and higher

Never enumerate 355^4 = 15,882,306,625 tuples.

Split by forbidden output pattern (v0,v1,v2,v3), then meet-in-the-middle. Enumerate left pairs (i,j) in H_v0 x H_v1 and right pairs (k,l) in H_v2 x H_v3. Compute packed compatibility signatures induced by rel1_4 and join compatible halves. A first correct implementation may GPU-scan right-pair chunks for each left-pair block; optimize only afterward.

Invariant: never materialize D2^4 and never dispatch one thread per D2^4 tuple. For larger w use floor(w/2)+ceil(w/2).

## 7. Candidate language

Never enumerate 3^355 tables. Generate symbolic functionals:
```
BOT | TT | FF
eval(a)
if(c,t,e)
is_tt(x) | is_ff(x) | defined(x)
semi_and(x,y) | semi_or(x,y)
principal(pattern)
union(patterns...)
race(T_patterns,F_patterns...)
```
Evaluate each expression immediately to its 355-byte semantic table; hash bytes and retain one provenance node per distinct table.

Later extend to adaptive higher-order calls: PCF may call `F (lambda x. M[F,x])`, not only F(a) for fixed closed a.

## 8. Exact definability closure at tau0

Do NOT use the earlier fixed-query decision-tree test as an exact oracle.

For context `F : (B -> B) -> B`, mutually saturate typed semantic sets including:
```
Ground(F) : D2 -> B
Arg(F)    : D2 -> D1
```
Application contributes `apply(A)(F) = F(A(F))`.

Represent:
```
GroundTables : uint8[][355]
ArgTables    : uint8[][355][3]
```
GPU-batch composition/application; CPU maintains hash-consing, work queues and provenance DAGs. These sets illustrate the core dependency; implement all intermediate typed contexts required by the chosen normal-form theorem. Do not claim exact nondefinability until completeness of the saturation grammar is justified.

## 9. Systematic type widening

Known boundary:
```
ordinary-Sieber universality:
  all order <= 2 : YES
  some order 3   : NO
```
Start at `((B -> B) -> B) -> B`. If universal, widen order-3 schemas.

Loader guarantees a counterexample somewhere in:
```
T_|W0| -> U1 -> U2 -> U3 -> B^(2n+2) -> B
```
for some n. Treat this as a guaranteed endpoint, not the first type to instantiate.

For every tested type record carrier sizes, definable count, Sieber candidates, maximum arity, certificates, runtime and GPU model.

## 10. MLX/Metal notes

Use the current MLX custom Metal-kernel API (historically `mlx.core.fast.metal_kernel`). Keep Python control outside kernels. Start with 256 threads/threadgroup; benchmark 128/256/512.

* integers/bitsets only;
* contiguous row-major uint8 semantic tables;
* uint16 semantic indices;
* packed relation masks;
* allocate/reuse buffers outside CEGAR;
* minimize synchronization;
* cache one compiled kernel per arity/layout, not per candidate;
* batch work between synchronizations.

## 11. Validation gates

**A — carriers:** 3 / 11 / 355 exactly.

**B — differential testing:** thousands of random restricted CPU/GPU cases; GPU witnesses must verify on CPU, and no-witness answers on restricted grids must match CPU exhaustive search.

**C — historical witnesses:** hard-code exploratory CPU witnesses and require verification/rediscovery.

**D — final rerun:** different test order, fresh process, CPU certificate verification, preferably a second backend.

## 12. Milestones

**M1 — arity-3 falsifier:** CPU oracle, Metal kernel, 3/11/355, differential tests, benchmark one candidate against all arity-3 tests. Do not proceed until correct.

**M2 — batched falsification:** hash-consing, bucket dispatch, 1k–100k candidates, learned CEGAR ordering, candidates/second.

**M3 — arity 4:** exact small CPU oracle, chunked/meet-in-the-middle GPU algorithm, differential validation, certificates.

**M4 — exact PCF semantic closure:** typed saturation, provenance DAG producing syntax, completeness justification, exact comparison against Sieber candidates.

**M5 — widen types:** if tau0 is universal, move through an explicitly documented increasing order-3 family toward Loader's schema.

## 13. What counts as success

A computational counterexample needs both:
1. a semantic h with a mathematical/all-arity reason that it preserves every ordinary Sieber relation (finite arity checking is evidence, not proof);
2. an exact proof that h is not PCF-definable.

The GPU is a discovery engine. Prefer a compact symbolic functional plus certificates/patterns from which an all-arity proof can be extracted, not an unexplained 355-entry table.

## 14. First report from the GPU agent

Before optimizing, implement M1 and report:
```
Mac model / chip / GPU cores / RAM
MLX version
Metal compile time
time for all arity-3 tests for one candidate
effective logical triples/second
CPU/GPU differential-test count
all regression counts
```
Only then decide whether the bottleneck is relation scanning, dispatch overhead, candidate batching or semantic generation.
