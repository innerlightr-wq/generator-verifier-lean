# Generator-Verifier Lean — Current Formal Status

## Milestone 1
Algebraic operating-region core established: deterministic capacity
matching, the capacity-margin factorization, the continuous feasible-region
theorem, the exact critical-size equivalence, deterministic throughput
maximization at capacity matching, and the finite-agent (`k_min`/`k_max`)
analogue.

## Milestone 2
Effective-independence / correlated-error core established: the exact
discrete-vs-continuous threshold separation, and the correlated-error
objective's optimizer (unconstrained, constrained to `[0,1]`, interior/
boundary characterization, exact `1/N` scaling).

## Headline results

Continuous feasibility (`FeasibleRegion.lean`, `hN hg hv hτ : 0 < N,g,v,τ`):
```
(∃ p, FeasibleContinuous p N g v T_min τ) ↔ N ≥ Ncrit g v T_min τ
```

Discrete-vs-continuous separation (`FiniteAgents.lean`, `hg hv : 0 < g,v`):
```
⌈Ncrit g v T_min τ⌉ ≤ NminDiscrete g v T_min τ
```

Exact witness (`discrete_threshold_differs_from_ceil_continuous_example`):
```
g = 2
v = 1
T_min = 3
τ = 1

Ncrit = 11/2
ceil(Ncrit) = 6
NminDiscrete = 7        (7 ≠ 6)
```

Correlated-error optimizer (`EffectiveIndependence.lean`):
```
p0 = (sigmaEta2 - sigmaI2) / (2 * N * sigmaC2)

J(p) = J(p0) + sigmaC2 * (p - p0)^2      -- objective_sub_eq_sq, hN : N ≠ 0, hC : sigmaC2 ≠ 0

N * p0 = (sigmaEta2 - sigmaI2) / (2 * sigmaC2)   -- N_mul_unconstrainedOptimum, hN : N ≠ 0, hC : sigmaC2 ≠ 0

p0(N) → 0 as N → ∞     -- unconstrainedOptimum_tendsto_zero, hC : sigmaC2 ≠ 0
```
(the unconstrained/constrained minimization theorems themselves,
`objective_minimized_at_unconstrainedOptimum` and
`objective_constrainedOptimum_le`, additionally require `hN : 0 < N` and
`hC : 0 < sigmaC2`, matching the paper's stated requirement for the
interior-optimizer formula.)

## Epistemic boundary

Lean verifies exact consequences of the stated mathematical models. It does
not establish that the queueing or correlated-error models accurately
describe deployed multi-agent AI systems.

## Next recommended milestone

M/M/c algebraic operating-region extension, with Erlang-C treated as
EXTERNAL MODEL INPUT unless independently formalized.
