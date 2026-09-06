import GeneratorVerifier.FeasibleRegion
import GeneratorVerifier.FiniteAgents

/-!  =====================  MAIN THEOREM  =====================

Assembles the headline results of this first milestone. Everything below is
proved in `Capacity.lean`, `FeasibleRegion.lean`, and `FiniteAgents.lean`;
this file states the capstone facts together and adds one cheap corollary
that falls directly out of `upperBound_eq_capacityFraction_sub`.

**The repository's central mechanism, in one sentence:** sufficient total
system size (`N ≥ N_crit` continuously, `N ≥ N_min^discrete` for integer
agent counts) is *exactly* equivalent to a nonempty operating region -- and
the throughput-maximizing fraction `p_c` is *never* inside that region,
since it saturates the latency margin to zero. -/

namespace GeneratorVerifier

noncomputable section

/-- **HEADLINE (continuous).** Restated from `FeasibleRegion.lean` for
visibility: sufficient system size iff a nonempty continuous operating
interval. -/
theorem headline_continuous {N g v T_min τ : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) :
    (∃ p, FeasibleContinuous p N g v T_min τ) ↔ N ≥ Ncrit g v T_min τ :=
  feasibleContinuous_exists_iff_N_ge_Ncrit hN hg hv hτ

/-- **HEADLINE (discrete).** Restated from `FiniteAgents.lean`: for an
integer population `N`, sufficient system size iff a feasible integer
generator count exists. -/
theorem headline_discrete {g v T_min τ : ℝ}
    (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) (N : ℤ) :
    (∃ k : ℤ, kMin g T_min ≤ k ∧ k ≤ kMax (N : ℝ) g v τ) ↔ N ≥ NminDiscrete g v T_min τ :=
  finite_feasibility_iff_N_ge_NminDiscrete hg hv hτ N

/-- **Bonus corollary, formally verified.** The throughput-maximizing
fraction `p_c` is never itself in the latency-feasible region: it saturates
the capacity margin to exactly zero, one full `1/(Nτ(g+v))` above the upper
operating bound. A structural tension the paper's operating-region picture
depends on, not an assumption. -/
theorem upperBound_lt_capacityFraction {N g v τ : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) :
    upperBound N g v τ < capacityFraction g v := by
  rw [upperBound_eq_capacityFraction_sub]
  have : (0:ℝ) < 1 / (N * τ * (g + v)) := by positivity
  linarith

end
end GeneratorVerifier
