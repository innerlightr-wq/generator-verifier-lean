import GeneratorVerifier.Capacity

/-!  =====================  FEASIBLE REGION (Phases 3, 4)  =====================

Formalizes the continuous operating-region bounds `p_-`, `p_+` and the
critical-system-size feasibility theorem.

**Epistemic point, stated once here rather than repeated on every theorem.**
The manuscript obtains `p_-` from a minimum-throughput constraint `T ≥ T_min`
directly (pure algebra), and obtains `p_+` from a maximum-mean-latency
constraint `W ≤ τ_max` via the M/M/1 relation `W = 1/(μ-λ)`. **That relation
is NOT formalized or assumed in this repository.** Instead, `upperBound` is
*defined* as the exact real number the manuscript's algebra produces once
`W = 1/(μ-λ)` and `W ≤ τ_max` are combined, and what is proved here is the
purely algebraic fact that `p ≤ upperBound ↔ N(g+v)(p_c-p) ≥ 1/τ`. Reading
`N(g+v)(p_c-p) ≥ 1/τ` as "mean latency is at most `τ`" is an EXTERNAL MODEL
INPUT, supplied by the paper, not re-derived here. -/

namespace GeneratorVerifier

noncomputable section

/-!  =====================  Phase 3: continuous operating bounds  ===================== -/

/-- `p_- = T_min/(Ng)`, the fraction below which throughput falls short of
`T_min`. -/
def lowerBound (N g T_min : ℝ) : ℝ := T_min / (N * g)

/-- `p_+ = v/(g+v) - 1/(Nτ(g+v)) = p_c - 1/(Nτ(g+v))`, the fraction above
which the algebraic latency proxy `N(g+v)(p_c-p)` drops below `1/τ`. -/
def upperBound (N g v τ : ℝ) : ℝ := v / (g + v) - 1 / (N * τ * (g + v))

theorem upperBound_eq_capacityFraction_sub {N g v τ : ℝ} :
    upperBound N g v τ = capacityFraction g v - 1 / (N * τ * (g + v)) := by
  unfold upperBound capacityFraction
  ring

/-- **FORMALLY VERIFIED, pure algebra.** Justifies `lowerBound`: the raw
minimum-throughput constraint `λ(p) ≥ T_min` holds exactly when
`p ≥ lowerBound N g T_min`. -/
theorem lam_ge_Tmin_iff_ge_lowerBound {p N g T_min : ℝ} (hN : 0 < N) (hg : 0 < g) :
    lam p N g ≥ T_min ↔ p ≥ lowerBound N g T_min := by
  unfold lam lowerBound
  have hNg : (0:ℝ) < N * g := by positivity
  rw [ge_iff_le, ge_iff_le, div_le_iff₀ hNg]
  constructor <;> intro h <;> nlinarith

/-- **FORMALLY VERIFIED, pure algebra.** Justifies `upperBound`: the raw
algebraic latency-margin constraint `N(g+v)(p_c-p) ≥ 1/τ` holds exactly when
`p ≤ upperBound N g v τ`. No claim is made that `N(g+v)(p_c-p)` equals
`1/W` for the manuscript's `W` -- that identification is an EXTERNAL MODEL
INPUT (see the module doc-comment). -/
theorem margin_ge_inv_tau_iff_le_upperBound {p N g v τ : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) :
    N * (g + v) * (capacityFraction g v - p) ≥ 1 / τ ↔ p ≤ upperBound N g v τ := by
  have hgv : (0:ℝ) < g + v := by linarith
  have hNgv : (0:ℝ) < N * (g + v) := by positivity
  have hident : N * (g + v) * (capacityFraction g v - p) - 1 / τ
      = N * (g + v) * (upperBound N g v τ - p) := by
    unfold upperBound capacityFraction
    field_simp
    ring
  constructor
  · intro h
    have h2 : 0 ≤ N * (g + v) * (upperBound N g v τ - p) := by rw [← hident]; linarith
    by_contra hcon
    push_neg at hcon
    have hneg : upperBound N g v τ - p < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg hNgv hneg]
  · intro h
    have h2 : 0 ≤ N * (g + v) * (upperBound N g v τ - p) :=
      mul_nonneg hNgv.le (by linarith)
    have h3 : 0 ≤ N * (g + v) * (capacityFraction g v - p) - 1/τ := by rw [hident]; exact h2
    linarith

/-- **Elementary real-order fact** underlying the feasible-point-existence
theorem below: a closed interval `[a,b]` is nonempty iff `a ≤ b`. Stated
directly for the two named bounds, requiring no further hypotheses on
`N,g,v,τ` beyond what already appears in `a` and `b` themselves. -/
theorem exists_mem_Icc_iff_le {a b : ℝ} : (∃ p : ℝ, a ≤ p ∧ p ≤ b) ↔ a ≤ b := by
  constructor
  · rintro ⟨p, h1, h2⟩; exact le_trans h1 h2
  · intro h; exact ⟨a, le_refl a, h⟩

/-- The continuous feasibility predicate: the interval `[p_-, p_+]` is the
set of `p` satisfying both hard constraints. -/
def FeasibleContinuous (p N g v T_min τ : ℝ) : Prop :=
  lowerBound N g T_min ≤ p ∧ p ≤ upperBound N g v τ

/-!  =====================  Phase 4: exact feasibility condition  ===================== -/

/-- The continuous critical system size,
`N_crit = (T_min(g+v)/g + 1/τ)/v`. -/
def Ncrit (g v T_min τ : ℝ) : ℝ := (T_min * (g + v) / g + 1 / τ) / v

/-- Key identity: the feasibility gap `p_+ - p_-` is exactly
`(N - N_crit) * v / (N(g+v))` -- a positive constant multiple of `N - N_crit`.
This is what makes the feasibility theorem below a one-line sign argument
rather than a case-by-case inequality chase. -/
theorem upperBound_sub_lowerBound_eq {N g v T_min τ : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) :
    upperBound N g v τ - lowerBound N g T_min
      = (N - Ncrit g v T_min τ) * v / (N * (g + v)) := by
  have hgv : (0:ℝ) < g + v := by linarith
  unfold upperBound lowerBound Ncrit
  field_simp
  ring

/-- **HEADLINE THEOREM (Phase 4).** For `N, g, v, τ > 0`, the continuous
operating interval `[p_-, p_+]` is nonempty exactly when the system is at
least the critical size: sufficient total system size ↔ nonempty operating
interval. No boundary subtlety arises: `upperBound = lowerBound` exactly at
`N = N_crit` (both sides of the `≤`/`≥` are non-strict, matching the
manuscript). -/
theorem continuous_feasibility_iff_N_ge_Ncrit {N g v T_min τ : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) :
    lowerBound N g T_min ≤ upperBound N g v τ ↔ N ≥ Ncrit g v T_min τ := by
  have hident := upperBound_sub_lowerBound_eq (N := N) (g := g) (v := v) (T_min := T_min) (τ := τ)
    hN hg hv hτ
  have hgv : (0:ℝ) < g + v := by linarith
  have hNgv : (0:ℝ) < N * (g + v) := by positivity
  constructor
  · intro h
    have h2 : 0 ≤ (N - Ncrit g v T_min τ) * v / (N * (g + v)) := by
      rw [← hident]; linarith
    by_contra hcon
    push_neg at hcon
    have hneg : N - Ncrit g v T_min τ < 0 := by linarith
    have hlt : (N - Ncrit g v T_min τ) * v / (N * (g + v)) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hv) hNgv
    linarith
  · intro h
    have hge : 0 ≤ N - Ncrit g v T_min τ := by linarith
    have h2 : 0 ≤ (N - Ncrit g v T_min τ) * v / (N * (g + v)) :=
      div_nonneg (mul_nonneg hge hv.le) hNgv.le
    have h3 : 0 ≤ upperBound N g v τ - lowerBound N g T_min := by rw [hident]; exact h2
    linarith

/-- Restated as feasibility of the predicate, for direct use. -/
theorem feasibleContinuous_exists_iff_N_ge_Ncrit {N g v T_min τ : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) (hτ : 0 < τ) :
    (∃ p, FeasibleContinuous p N g v T_min τ) ↔ N ≥ Ncrit g v T_min τ := by
  rw [← continuous_feasibility_iff_N_ge_Ncrit hN hg hv hτ]
  constructor
  · rintro ⟨p, hp1, hp2⟩; linarith
  · intro h; exact ⟨lowerBound N g T_min, le_refl _, h⟩

end
end GeneratorVerifier
