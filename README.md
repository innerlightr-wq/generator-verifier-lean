# generator-verifier-lean

A machine-checked formalization, in Lean 4 with mathlib, of the exact
algebraic operating-region structure from:

> Elias De Jesús. *System-Specific Operating Regions in Multi-Agent
> Generator-Verifier Systems: Capacity Matching, Queueing Margins, and
> Effective Independence.*

**Zenodo:** https://doi.org/10.5281/zenodo.22342517

**A note on the name.** Here "generator" and "verifier" are **agent roles in a
capacity model**, not a producer-and-checker trust architecture. `N` agents are
split into a fraction `p` that *generates* work at rate `g` each and a fraction
`1-p` that *verifies* it at rate `v` each; `p` is the design variable and
`p_c = v/(g+v)` is the split at which the two aggregate rates balance. Nothing
here produces a candidate artifact, emits a certificate, or checks one: there is
no untrusted producer, no certificate format, and no checker. Readers arriving from
formal methods should note in particular that this is **not** an instance of the
LCF architecture or of certifying computation — the pattern in which a large
untrusted search emits a witness that a small trusted checker validates
([Gordon–Milner–Wadsworth 1979][lcf]; [McConnell–Mehlhorn–Näher–Schweitzer
2011][certalg]). That architecture is classical and is not what this development
implements. The only trust boundary present is the ordinary one for a Lean
formalization: the kernel, mathlib, and the definitions below. See
[`docs/TRUST_BOUNDARY.md`](docs/TRUST_BOUNDARY.md).

**Scope of this first milestone.** This is not a formalization of M/M/1
queueing theory. It formalizes the exact real-algebra skeleton of the
paper's operating-region argument: capacity matching, the capacity-margin
identity, the continuous operating bounds, the critical-system-size
feasibility theorem, deterministic throughput maximization, and the
finite-agent (integer generator-count) analogue of the feasibility theorem.

No `sorry`, no `admit`, no custom `axiom` anywhere in the development.

## Central results

```lean
theorem continuous_feasibility_iff_N_ge_Ncrit {N g v T_min τ : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) :
    lowerBound N g T_min ≤ upperBound N g v τ ↔ N ≥ Ncrit g v T_min τ

theorem finite_feasibility_iff_N_ge_NminDiscrete
    {g v T_min τ : ℝ} (hg : 0 < g) (hv : 0 < v) (_hτ : 0 < τ) (N : ℤ) :
    (∃ k : ℤ, kMin g T_min ≤ k ∧ k ≤ kMax (N : ℝ) g v τ) ↔ N ≥ NminDiscrete g v T_min τ
```

Sufficient total system size is exactly equivalent to a nonempty operating
region, continuously and (for integer agent counts) discretely.

## Epistemic discipline

This is the single most important thing to read before quoting a result
from this repository.

### FORMALLY VERIFIED

Lean's kernel checks these from the stated real/order-algebra assumptions
alone -- no probability, no stochastic process, anywhere in the proof.

- Deterministic capacity matching: `capacity_matching`, `capacity_matching_value`,
  `capacityFraction_pos`, `capacityFraction_lt_one` (`Capacity.lean`).
- Capacity-margin factorization and its sign trichotomy:
  `capacity_margin_factorization`, `margin_pos_iff_lt_capacityFraction`,
  `margin_eq_zero_iff_eq_capacityFraction`, `margin_neg_iff_gt_capacityFraction`
  (`Capacity.lean`).
- Deterministic throughput maximization at `p_c` on `[0,1]`:
  `throughput_le_capacityFraction` (`Capacity.lean`).
- The continuous operating bounds and their justifying algebraic
  equivalences: `lam_ge_Tmin_iff_ge_lowerBound`,
  `margin_ge_inv_tau_iff_le_upperBound` (`FeasibleRegion.lean`).
- The continuous critical-size feasibility theorem:
  `continuous_feasibility_iff_N_ge_Ncrit`,
  `feasibleContinuous_exists_iff_N_ge_Ncrit`, and the elementary
  interval-nonemptiness fact underlying it, `exists_mem_Icc_iff_le`
  (`FeasibleRegion.lean`).
- The finite-agent (integer generator-count) bounds and feasibility
  theorem: `kMin_le_iff`, `le_kMax_iff`, `exists_feasible_k_iff`,
  `finite_feasibility_iff_N_ge_NminDiscrete` (`FiniteAgents.lean`).
- `upperBound_lt_capacityFraction` (`MainTheorem.lean`): the
  throughput-maximizing fraction `p_c` is never itself latency-feasible.

**Milestone 2 additions:**

- The exact discrete/continuous threshold separation: the general fact
  `⌈N_crit⌉ ≤ N_min^discrete` (`ceil_Ncrit_le_NminDiscrete`), and a concrete
  exact witness that this can be a strict inequality,
  `discrete_threshold_differs_from_ceil_continuous_example`
  (`FiniteAgents.lean`).
- The correlated-error / effective-independence objective `J(p)` and its
  exact completing-the-square identity: `objective_sub_eq_sq`,
  `objective_minimized_at_unconstrainedOptimum` (unconstrained minimizer),
  `objective_constrainedOptimum_le` (minimizer on `[0,1]`),
  `constrainedOptimum_nonneg`, `constrainedOptimum_le_one`,
  `unconstrainedOptimum_pos_iff`, `unconstrainedOptimum_lt_one_iff`,
  `unconstrainedOptimum_interior_iff` (interior-vs-boundary
  characterization), `N_mul_unconstrainedOptimum` (exact `1/N` scaling
  identity), and `unconstrainedOptimum_tendsto_zero` (the asymptotic
  `p0 → 0` as `N → ∞`, via mathlib's `tendsto_inv_atTop_zero`)
  (`EffectiveIndependence.lean`). All proved by completing the square and
  elementary order algebra -- no calculus, no convexity machinery.

### EXTERNAL MODEL INPUT

Not formalized here, and not pretended to be. Where the paper's algebra
depends on one of these, the Lean development takes the paper's *resulting
closed-form quantity* as a definition and proves the algebra around it,
rather than deriving the quantity itself.

- The M/M/1 interpretation of `M(p) > 0` as queue stability (requires
  `λ < μ`, which is exactly `margin_pos_iff_lt_capacityFraction`'s
  conclusion under the paper's own reading -- the *reading* is external,
  the algebra is not).
- The relation `W = 1/(μ-λ)` for mean queueing latency. `upperBound` is
  *defined* as the real number this relation produces once combined with
  `W ≤ τ_max`; what is proved is the purely algebraic fact
  `N(g+v)(p_c-p) ≥ 1/τ ↔ p ≤ upperBound` (`margin_ge_inv_tau_iff_le_upperBound`).
  `W = 1/(μ-λ)` itself is never stated or used as a theorem.
- Any other classical queueing or probabilistic fact (stationary
  distributions, Little's law, etc.) -- none is invoked anywhere below.
- The correlated-error objective `J(p)` itself (Milestone 2) is a
  **modeling assumption from the paper**, taken as a definition. Lean
  verifies the optimizer and scaling laws *of that stated quadratic model*;
  it does not validate that `J(p)` is a complete or empirically correct
  model of real multi-agent AI failure, that nominal headcount equals
  effective independence, or that correlated verifier failures in deployed
  systems obey this exact objective. The accurate phrasing is: **Lean
  verifies the optimizer and scaling laws of the correlated-error model**,
  not "Lean proves effective independence in AI systems."

### OPEN / FUTURE

Explicitly out of scope for this milestone (see the paper's later
sections):

- M/M/1 stochastic process construction, stationary queue-length
  distribution, a proof of `W = 1/(μ-λ)`, Little's law from first
  principles.
- Erlang-C / M/M/c, Halfin-Whitt heavy-traffic limits.
- Graph propagation kernels, spectral-gap results.
- Adaptive role allocation.
- Real LLM-agent experiments; real correlated-verifier calibration
  (fitting `σ_c^2, σ_i^2, σ_η^2` to actual deployed multi-agent systems).
- A formal proof (or counterexample construction) that
  `N_min^discrete ≠ ⌈N_crit⌉` in general -- **resolved for Milestone 2**:
  the one-sided inequality `⌈N_crit⌉ ≤ N_min^discrete` is proved to hold
  always, and a concrete exact parameter witness
  (`discrete_threshold_differs_from_ceil_continuous_example`) shows it can
  be strict. What remains open is only a *second* witness showing the two
  quantities can also coincide exactly (not attempted, not needed to
  establish non-equality in general).

**This repository does not verify the safety of multi-agent AI systems.**
It verifies exact statements inside the stated deterministic/algebraic
model. Reading those statements as facts about real deployed systems
requires the EXTERNAL MODEL INPUT items above to actually hold.

## Prior art

The mathematics formalized here is classical; what is machine-checked is the
exact algebra, not the underlying ideas. Full provenance is in
[`docs/NOVELTY_AND_PROVENANCE.md`](docs/NOVELTY_AND_PROVENANCE.md), the
conceptual ancestry in
[`docs/ARCHITECTURE_ANCESTRY.md`](docs/ARCHITECTURE_ANCESTRY.md), and verified
bibliographic records in [`references.bib`](references.bib). The load-bearing
attributions:

**Capacity matching.** `p_c = v/(g+v)` maximizing `min(pNg,(1-p)Nv)` is the
classical two-stage line-balancing optimum: equalize the stage rates. The
formalization adds a kernel-checked statement, not the result.

**The critical system size.** `N_crit` answers a long-studied question — how
many servers does a system need to hold a service level — and answers it in the
deterministic first-order case, by solving a linear inequality in `N`. The
stochastic form, including the `sqrt(load)` correction this development
deliberately omits, is [Halfin–Whitt 1981][hw] and
[Borst–Mandelbaum–Reiman 2004][bmr]. M/M/1 stability and `W = 1/(mu-lambda)`,
both listed under EXTERNAL MODEL INPUT above, are standard (Kleinrock,
*Queueing Systems, Volume 1: Theory*, Wiley, 1975; no DOI assigned).

**Effective independence.** The structure of `J(p)` is the classical
correlated-average variance form: the correlated term `p^2 sigma_c^2` carries no
factor of `1/N` while the independent terms do, so the variance cannot be driven
to zero by adding agents and the optimal generator fraction decays as `1/N`.
This is the design effect and effective sample size (Kish, *Survey Sampling*,
Wiley, 1965; no DOI assigned), the intraclass-correlation decomposition
([Shrout–Fleiss 1979][sf]), the Condorcet
jury theorem with correlated votes ([Ladha 1992][ladha]), and the
bias–variance–covariance decomposition of ensembles
([Ueda–Nakano 1996][un]) — the last of which is a machine-learning result three
decades older than the current multi-agent literature. What is verified here is
the optimizer and the scaling laws *of the paper's stated quadratic*.

**Discrete thresholds.** The one result with no clean single ancestor is
`ceil_Ncrit_le_NminDiscrete` together with its explicit strict witness: rounding
the continuous threshold up is not in general sufficient once agent counts are
integers. This is the integer-staffing phenomenon, stated exactly.

**Platform.** Lean 4 ([de Moura–Ullrich 2021][lean4]) and mathlib
([The mathlib Community 2020][mathlib]).

**Terminology.** "Generator–verifier" is already standard usage in the
formal-AI literature for a producer paired with a proof-assistant checker
(e.g. [LeanDojo][leandojo]); the sense used here is the capacity-model one
described at the top of this file.

[lcf]: https://doi.org/10.1007/3-540-09724-4
[certalg]: https://doi.org/10.1016/j.cosrev.2010.09.009
[hw]: https://doi.org/10.1287/opre.29.3.567
[bmr]: https://doi.org/10.1287/opre.1030.0081
[sf]: https://doi.org/10.1037/0033-2909.86.2.420
[ladha]: https://doi.org/10.2307/2111584
[un]: https://doi.org/10.1109/ICNN.1996.548872
[lean4]: https://doi.org/10.1007/978-3-030-79876-5_37
[mathlib]: https://doi.org/10.1145/3372885.3373824
[leandojo]: https://doi.org/10.52202/075280-0944

## Layout

```
GeneratorVerifier/
    Basic.lean              -- placeholder module
    Capacity.lean            -- Phases 1, 2, 5: rates, capacity matching, margin, throughput max
    FeasibleRegion.lean       -- Phases 3, 4: p_-, p_+, N_crit, continuous feasibility
    FiniteAgents.lean         -- Phases 6, 7: k_min, k_max, N_min^discrete, discrete feasibility,
                                 discrete/continuous threshold separation (Milestone 2)
    MainTheorem.lean          -- capstone restatements + one bonus corollary
    EffectiveIndependence.lean -- Milestone 2: correlated-error objective and its optimizer
GeneratorVerifier.lean        -- top-level import
```

## Environment

```
leanprover/lean4:v4.33.1
mathlib pinned to v4.33.1
```

Build with:

```bash
lake update
lake build
```
