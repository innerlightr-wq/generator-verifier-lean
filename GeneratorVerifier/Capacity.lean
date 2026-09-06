import Mathlib

/-!  =====================  CAPACITY (Phases 1, 2, 5)  =====================

Formalizes the deterministic aggregate-rate model of

  "System-Specific Operating Regions in Multi-Agent Generator-Verifier
   Systems: Capacity Matching, Queueing Margins, and Effective Independence."

`N` agents are split into a fraction `p` doing generation (rate `g` each)
and `1-p` doing verification (rate `v` each). This file is pure real
algebra/order theory: `N, p, g, v` are arbitrary reals throughout, and no
stochastic-process fact (M/M/1 stability, queueing formulas) is assumed or
used anywhere below. See `README.md` for the FORMALLY VERIFIED / EXTERNAL
MODEL INPUT split. -/

namespace GeneratorVerifier

noncomputable section

/-!  =====================  Phase 1: basic model definitions  ===================== -/

/-- Deterministic aggregate generation (arrival) rate `λ(p) = pNg`. -/
def lam (p N g : ℝ) : ℝ := p * N * g

/-- Deterministic aggregate verification (service) rate `μ(p) = (1-p)Nv`. -/
def mu (p N v : ℝ) : ℝ := (1 - p) * N * v

/-- Deterministic throughput `T(p) = min(λ(p), μ(p))`. -/
def throughput (p N g v : ℝ) : ℝ := min (lam p N g) (mu p N v)

/-- The capacity-matching fraction `p_c = v/(g+v)`. -/
def capacityFraction (g v : ℝ) : ℝ := v / (g + v)

theorem capacityFraction_pos {g v : ℝ} (hg : 0 < g) (hv : 0 < v) :
    0 < capacityFraction g v := by
  unfold capacityFraction
  have : 0 < g + v := by linarith
  positivity

theorem capacityFraction_lt_one {g v : ℝ} (hg : 0 < g) (hv : 0 < v) :
    capacityFraction g v < 1 := by
  unfold capacityFraction
  rw [div_lt_one (by linarith)]
  linarith

theorem capacityFraction_mem_Ioo {g v : ℝ} (hg : 0 < g) (hv : 0 < v) :
    0 < capacityFraction g v ∧ capacityFraction g v < 1 :=
  ⟨capacityFraction_pos hg hv, capacityFraction_lt_one hg hv⟩

/-- Capacity matching: at `p_c`, arrival and service rates coincide. -/
theorem capacity_matching {N g v : ℝ} (hg : 0 < g) (hv : 0 < v) :
    lam (capacityFraction g v) N g = mu (capacityFraction g v) N v := by
  unfold lam mu capacityFraction
  have hne : (g + v : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The common value at capacity matching is `Ngv/(g+v)`. -/
theorem capacity_matching_value {N g v : ℝ} (hg : 0 < g) (hv : 0 < v) :
    lam (capacityFraction g v) N g = N * g * v / (g + v) := by
  unfold lam capacityFraction
  have hne : (g + v : ℝ) ≠ 0 := by positivity
  field_simp

/-- Throughput at capacity matching: since the two branches of the `min`
agree there (`capacity_matching`), the `min` collapses directly. -/
theorem throughput_at_capacityFraction {N g v : ℝ} (hg : 0 < g) (hv : 0 < v) :
    throughput (capacityFraction g v) N g v = N * g * v / (g + v) := by
  unfold throughput
  have heq := capacity_matching (N := N) hg hv
  rw [heq, min_self, ← heq]
  exact capacity_matching_value hg hv

/-!  =====================  Phase 2: exact capacity-margin identity  ===================== -/

/-- The capacity margin `M(p) = μ(p) - λ(p)`. -/
def margin (p N g v : ℝ) : ℝ := mu p N v - lam p N g

/-- **Structural identity of the paper.** `M(p)` factors exactly as
`N(g+v)(p_c - p)`. Pure algebra, needing only `g+v ≠ 0` (always true in the
physical model, where `g,v>0`) -- at `g+v=0` the identity genuinely fails,
since `capacityFraction` is then `v/0 = 0` by Lean's division convention
while `margin` need not vanish. -/
theorem capacity_margin_factorization (p N g v : ℝ) (hgv : g + v ≠ 0) :
    margin p N g v = N * (g + v) * (capacityFraction g v - p) := by
  unfold margin mu lam capacityFraction
  field_simp
  ring

/-- **FORMALLY VERIFIED.** `M(p) > 0 ↔ p < p_c`. This is pure order algebra;
the queueing interpretation "`M(p)>0` means the M/M/1 queue is stable" is an
EXTERNAL MODEL INPUT, not claimed here -- see `README.md`. -/
theorem margin_pos_iff_lt_capacityFraction
    {p N g v : ℝ} (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) :
    margin p N g v > 0 ↔ p < capacityFraction g v := by
  rw [capacity_margin_factorization p N g v (by positivity)]
  have hNgv : 0 < N * (g + v) := by positivity
  constructor
  · intro h
    nlinarith [mul_pos_iff.mp h]
  · intro h
    have : 0 < capacityFraction g v - p := by linarith
    exact mul_pos hNgv this

theorem margin_eq_zero_iff_eq_capacityFraction
    {p N g v : ℝ} (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) :
    margin p N g v = 0 ↔ p = capacityFraction g v := by
  rw [capacity_margin_factorization p N g v (by positivity)]
  have hNgv : (N * (g + v) : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hNgv
    · linarith
  · intro h; rw [h]; ring

theorem margin_neg_iff_gt_capacityFraction
    {p N g v : ℝ} (hN : 0 < N) (hg : 0 < g) (hv : 0 < v) :
    margin p N g v < 0 ↔ p > capacityFraction g v := by
  rw [capacity_margin_factorization p N g v (by positivity)]
  have hNgv : 0 < N * (g + v) := by positivity
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg hNgv.le (by linarith : (0:ℝ) ≤ capacityFraction g v - p)]
  · intro h
    have : capacityFraction g v - p < 0 := by linarith
    have := mul_neg_of_pos_of_neg hNgv this
    linarith

/-!  =====================  Phase 5: throughput maximization  ===================== -/

/-- **FORMALLY VERIFIED.** Deterministic throughput on the physical domain
`0 ≤ p ≤ 1` is maximized at `p = p_c`. Elementary order algebra: on
`p ≤ p_c`, `T(p) = λ(p) ≤ λ(p_c)`; on `p ≥ p_c`, `T(p) = μ(p) ≤ μ(p_c)`; the
two agree at `p_c` by `capacity_matching`. -/
theorem throughput_le_capacityFraction {p N g v : ℝ}
    (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (hN : 0 ≤ N) (hg : 0 < g) (hv : 0 < v) :
    throughput p N g v ≤ throughput (capacityFraction g v) N g v := by
  rw [throughput_at_capacityFraction hg hv]
  unfold throughput
  rcases le_total p (capacityFraction g v) with hle | hge
  · have hlam : lam p N g ≤ N * g * v / (g + v) := by
      have h1 : lam p N g ≤ lam (capacityFraction g v) N g := by
        unfold lam
        have : 0 ≤ N * g := by positivity
        nlinarith
      rwa [capacity_matching_value hg hv] at h1
    exact le_trans (min_le_left _ _) hlam
  · have hmu : mu p N v ≤ N * g * v / (g + v) := by
      have h1 : mu p N v ≤ mu (capacityFraction g v) N v := by
        unfold mu
        have : 0 ≤ N * v := by positivity
        nlinarith
      rw [← capacity_matching hg hv] at h1
      rwa [capacity_matching_value hg hv] at h1
    exact le_trans (min_le_right _ _) hmu

end
end GeneratorVerifier
