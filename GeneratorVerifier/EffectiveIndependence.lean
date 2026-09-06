import Mathlib

/-!  =====================  EFFECTIVE INDEPENDENCE (Milestone 2, Phases 3-7)  =====================

Formalizes the correlated-error / effective-independence optimizer from the
paper's "Effective Independence" section:

    J(p) = p^2 σ_c^2 + [p σ_i^2 + (1-p) σ_η^2] / N

This is pure real quadratic algebra throughout: `objective` is minimized via
completing the square, never via calculus, exactly as requested. See
`README.md` for the FORMALLY VERIFIED / EXTERNAL MODEL INPUT split -- in
particular, nothing here claims that `J(p)` is a validated model of real
correlated verifier failure, only that the stated quadratic is minimized
where claimed. -/

namespace GeneratorVerifier

noncomputable section

/-!  =====================  Phase 3: the correlated-error objective  ===================== -/

/-- `J(p) = p^2 σ_c^2 + [p σ_i^2 + (1-p) σ_η^2] / N`. -/
def objective (p sigmaC2 sigmaI2 sigmaEta2 N : ℝ) : ℝ :=
  p^2 * sigmaC2 + (p * sigmaI2 + (1 - p) * sigmaEta2) / N

/-!  =====================  Phase 4: unconstrained optimizer  ===================== -/

/-- The unconstrained stationary point,
`p0 = (σ_η^2 - σ_i^2) / (2 N σ_c^2)`. -/
def unconstrainedOptimum (sigmaC2 sigmaI2 sigmaEta2 N : ℝ) : ℝ :=
  (sigmaEta2 - sigmaI2) / (2 * N * sigmaC2)

/-- **Completing-the-square identity.** Exact, no approximation. -/
theorem objective_sub_eq_sq {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : N ≠ 0) (hC : sigmaC2 ≠ 0)
    (p : ℝ) :
    objective p sigmaC2 sigmaI2 sigmaEta2 N -
        objective (unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N) sigmaC2 sigmaI2 sigmaEta2 N
      = sigmaC2 * (p - unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N) ^ 2 := by
  unfold objective unconstrainedOptimum
  field_simp
  ring

/-- Restated as an unconditional expansion, convenient for the case-split
argument in Phase 5. -/
theorem objective_eq_optimum_add_sq
    {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : N ≠ 0) (hC : sigmaC2 ≠ 0) (p : ℝ) :
    objective p sigmaC2 sigmaI2 sigmaEta2 N
      = objective (unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N) sigmaC2 sigmaI2 sigmaEta2 N
        + sigmaC2 * (p - unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N) ^ 2 := by
  have := objective_sub_eq_sq (sigmaC2 := sigmaC2) (sigmaI2 := sigmaI2) (sigmaEta2 := sigmaEta2)
    (N := N) hN hC p
  linarith

/-- **FORMALLY VERIFIED (Phase 4 headline).** `p0` minimizes `J` over all
reals -- pure quadratic algebra, no calculus. -/
theorem objective_minimized_at_unconstrainedOptimum
    {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : 0 < N) (hC : 0 < sigmaC2) (p : ℝ) :
    objective (unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N) sigmaC2 sigmaI2 sigmaEta2 N
      ≤ objective p sigmaC2 sigmaI2 sigmaEta2 N := by
  have hident := objective_sub_eq_sq (sigmaC2 := sigmaC2) (sigmaI2 := sigmaI2)
    (sigmaEta2 := sigmaEta2) (N := N) (ne_of_gt hN) (ne_of_gt hC) p
  nlinarith [mul_nonneg hC.le (sq_nonneg (p - unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N))]

/-!  =====================  Phase 5: constrained optimizer on [0,1]  ===================== -/

/-- Mathlib has no dedicated `clamp`; `min 1 (max 0 p0)` is the cleanest
representation using its standard `min`/`max` API. -/
def constrainedOptimum (sigmaC2 sigmaI2 sigmaEta2 N : ℝ) : ℝ :=
  min 1 (max 0 (unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N))

theorem constrainedOptimum_nonneg (sigmaC2 sigmaI2 sigmaEta2 N : ℝ) :
    0 ≤ constrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N :=
  le_min (by norm_num) (le_max_left _ _)

theorem constrainedOptimum_le_one (sigmaC2 sigmaI2 sigmaEta2 N : ℝ) :
    constrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N ≤ 1 :=
  min_le_left _ _

/-- **FORMALLY VERIFIED (Phase 5 headline).** The `[0,1]`-clamped optimizer
minimizes `J` over the physical domain `[0,1]`. Proved by the three cases
the paper describes (`p0 < 0`, `0 ≤ p0 ≤ 1`, `p0 > 1`), each an elementary
quadratic-distance comparison -- no convexity machinery, no calculus. -/
theorem objective_constrainedOptimum_le
    {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : 0 < N) (hC : 0 < sigmaC2)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    objective (constrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N) sigmaC2 sigmaI2 sigmaEta2 N
      ≤ objective p sigmaC2 sigmaI2 sigmaEta2 N := by
  set p0 := unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N with hp0def
  have hexp : ∀ q : ℝ, objective q sigmaC2 sigmaI2 sigmaEta2 N
      = objective p0 sigmaC2 sigmaI2 sigmaEta2 N + sigmaC2 * (q - p0) ^ 2 :=
    fun q => objective_eq_optimum_add_sq (ne_of_gt hN) (ne_of_gt hC) q
  rcases le_total p0 0 with hc1 | hc1
  · -- p0 ≤ 0: constrainedOptimum = 0
    have heq : constrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N = 0 := by
      unfold constrainedOptimum
      rw [max_eq_left hc1, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    rw [heq, hexp 0, hexp p]
    have hdist : (0 - p0) ^ 2 ≤ (p - p0) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hdist hC.le]
  · rcases le_total p0 1 with hc2 | hc2
    · -- 0 ≤ p0 ≤ 1: constrainedOptimum = p0
      have heq : constrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N = p0 := by
        unfold constrainedOptimum
        rw [max_eq_right hc1, min_eq_right hc2]
      rw [heq]
      exact objective_minimized_at_unconstrainedOptimum hN hC p
    · -- p0 ≥ 1: constrainedOptimum = 1
      have heq : constrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N = 1 := by
        unfold constrainedOptimum
        rw [max_eq_right hc1, min_eq_left hc2]
      rw [heq, hexp 1, hexp p]
      have hdist : (1 - p0) ^ 2 ≤ (p - p0) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hdist hC.le]

/-!  =====================  Phase 6: interior/boundary characterization  ===================== -/

/-- **FORMALLY VERIFIED.** `p0 > 0 ↔ σ_η^2 > σ_i^2`. -/
theorem unconstrainedOptimum_pos_iff
    {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : 0 < N) (hC : 0 < sigmaC2) :
    0 < unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N ↔ sigmaEta2 > sigmaI2 := by
  unfold unconstrainedOptimum
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * N * sigmaC2)]
  constructor <;> intro h <;> linarith

/-- **FORMALLY VERIFIED.** `p0 < 1 ↔ σ_η^2 - σ_i^2 < 2Nσ_c^2`. -/
theorem unconstrainedOptimum_lt_one_iff
    {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : 0 < N) (hC : 0 < sigmaC2) :
    unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N < 1
      ↔ sigmaEta2 - sigmaI2 < 2 * N * sigmaC2 := by
  unfold unconstrainedOptimum
  rw [div_lt_one (by positivity : (0:ℝ) < 2 * N * sigmaC2)]

/-- **FORMALLY VERIFIED.** The optimizer is genuinely interior exactly when
both variance conditions hold -- a clean characterization of when the
correlated-error optimum is not saturated at a boundary. -/
theorem unconstrainedOptimum_interior_iff
    {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : 0 < N) (hC : 0 < sigmaC2) :
    (0 < unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N
      ∧ unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N < 1)
      ↔ (sigmaEta2 > sigmaI2 ∧ sigmaEta2 - sigmaI2 < 2 * N * sigmaC2) := by
  rw [unconstrainedOptimum_pos_iff hN hC, unconstrainedOptimum_lt_one_iff hN hC]

/-!  =====================  Phase 7: exact 1/N scaling  ===================== -/

/-- **FORMALLY VERIFIED.** `N * p0` is exactly independent of `N` -- the
exact identity behind the paper's `p0 = O(1/N)` claim, with no
Big-O infrastructure needed. -/
theorem N_mul_unconstrainedOptimum
    {sigmaC2 sigmaI2 sigmaEta2 N : ℝ} (hN : N ≠ 0) (hC : sigmaC2 ≠ 0) :
    N * unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N
      = (sigmaEta2 - sigmaI2) / (2 * sigmaC2) := by
  unfold unconstrainedOptimum
  field_simp

/-- **FORMALLY VERIFIED.** `p0(N) → 0` as `N → ∞`, for fixed variances with
`σ_c^2 ≠ 0`. Direct from `tendsto_inv_atTop_zero`, requiring no new
asymptotic infrastructure beyond what mathlib already provides. -/
theorem unconstrainedOptimum_tendsto_zero {sigmaC2 sigmaI2 sigmaEta2 : ℝ} (hC : sigmaC2 ≠ 0) :
    Filter.Tendsto (fun N : ℝ => unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N)
      Filter.atTop (nhds 0) := by
  have heq : ∀ N : ℝ, unconstrainedOptimum sigmaC2 sigmaI2 sigmaEta2 N
      = ((sigmaEta2 - sigmaI2) / (2 * sigmaC2)) * N⁻¹ := by
    intro N; unfold unconstrainedOptimum; field_simp
  simp_rw [heq]
  have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ((sigmaEta2 - sigmaI2) / (2 * sigmaC2))
  simpa using h

end
end GeneratorVerifier
