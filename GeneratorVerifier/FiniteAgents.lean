import GeneratorVerifier.FeasibleRegion

/-!  =====================  FINITE AGENTS (Phases 6, 7)  =====================

**Phase 6 audit, reported here rather than only in prose.** Mathlib provides
two ceiling/floor families:

* `Nat.ceil`/`Nat.floor` (`⌈·⌉₊`/`⌊·⌋₊`, into `ℕ`): the clean order lemmas
  (`Nat.le_floor_iff`, `Nat.ceil_le`) need a side condition `0 ≤ a` on the
  real argument, since `ℕ` cannot represent a negative floor.
* `Int.ceil`/`Int.floor` (`⌈·⌉`/`⌊·⌋`, into `ℤ`): `Int.le_floor : z ≤ ⌊a⌋ ↔
  (z:ℝ) ≤ a` and `Int.ceil_le : ⌈a⌉ ≤ z ↔ a ≤ z` hold **unconditionally**,
  with no positivity side condition, because `ℤ` can represent a negative
  value if the real expression ever were negative.

Since `k_max`'s defining expression `(Nv - 1/τ)/(g+v)` involves a subtraction
that is only nonnegative under a further hypothesis (not assumed here), using
`Int.floor`/`Int.ceil` (agent counts as `ℤ`) avoids threading an extra
nonnegativity hypothesis through every lemma just to satisfy `Nat.floor`'s
API, and avoids `ℕ` truncated subtraction entirely. This is the cleanest
representation and is what is used below. Physical nonnegativity of `k_min`,
`k_max` (when it holds) is a separate, easy consequence of `T_min ≥ 0` etc.,
not needed for the order characterizations themselves. -/

namespace GeneratorVerifier

noncomputable section

/-!  =====================  Phase 6: discrete generator-count bounds  ===================== -/

/-- `k_min = ⌈T_min/g⌉`, the minimum number of generator agents needed to
reach `T_min` throughput on their own. -/
def kMin (g T_min : ℝ) : ℤ := ⌈T_min / g⌉

/-- `k_max = ⌊(Nv - 1/τ)/(g+v)⌋`, the maximum number of generator agents
compatible with the latency margin. -/
def kMax (N g v τ : ℝ) : ℤ := ⌊(N * v - 1 / τ) / (g + v)⌋

/-- **FORMALLY VERIFIED.** `k_min ≤ k ↔ T_min ≤ k*g`, the exact
coercion-correct order characterization of `k_min`. -/
theorem kMin_le_iff {g T_min : ℝ} (hg : 0 < g) (k : ℤ) :
    kMin g T_min ≤ k ↔ T_min ≤ (k : ℝ) * g := by
  unfold kMin
  rw [Int.ceil_le, div_le_iff₀ hg]

/-- **FORMALLY VERIFIED.** `k ≤ k_max ↔ k*(g+v) ≤ Nv - 1/τ`, the exact
coercion-correct order characterization of `k_max`. -/
theorem le_kMax_iff {N g v τ : ℝ} (hg : 0 < g) (hv : 0 < v) (k : ℤ) :
    k ≤ kMax N g v τ ↔ (k : ℝ) * (g + v) ≤ N * v - 1 / τ := by
  unfold kMax
  have hgv : (0:ℝ) < g + v := by linarith
  rw [Int.le_floor, le_div_iff₀ hgv]

/-- **HEADLINE THEOREM (Phase 6).** A feasible integer number of generator
agents exists exactly when `k_min ≤ k_max` -- immediate once both bounds are
in `ℤ` and related by a common order, needing no further algebra. -/
theorem exists_feasible_k_iff {g v N T_min τ : ℝ} :
    (∃ k : ℤ, kMin g T_min ≤ k ∧ k ≤ kMax N g v τ) ↔ kMin g T_min ≤ kMax N g v τ := by
  constructor
  · rintro ⟨k, h1, h2⟩; exact le_trans h1 h2
  · intro h; exact ⟨kMin g T_min, le_rfl, h⟩

/-!  =====================  Phase 7: exact discrete minimum population  =====================

Only attempted because Phase 6 above is clean (no coercion difficulty beyond
one cast, no case split, both order characterizations proved directly). -/

/-- The exact discrete minimum population,
`N_min^discrete = ⌈((g+v)*k_min + 1/τ)/v⌉`. Kept as its own definition,
distinct from the continuous `Ncrit` in `FeasibleRegion.lean` -- see the
remark below. -/
def NminDiscrete (g v T_min τ : ℝ) : ℤ :=
  ⌈((g + v) * (kMin g T_min : ℝ) + 1 / τ) / v⌉

/-- **HEADLINE THEOREM (Phase 7).** For an integer population `N`, a feasible
integer generator count exists exactly when `N ≥ N_min^discrete` -- exact,
not a numerical approximation. Chains `exists_feasible_k_iff` with
`Int.le_floor` (unfolding `kMax`) and `Int.ceil_le` (unfolding
`NminDiscrete`), the same order lemmas used in Phase 6. -/
theorem finite_feasibility_iff_N_ge_NminDiscrete
    {g v T_min τ : ℝ} (hg : 0 < g) (hv : 0 < v) (_hτ : 0 < τ) (N : ℤ) :
    (∃ k : ℤ, kMin g T_min ≤ k ∧ k ≤ kMax (N : ℝ) g v τ) ↔ N ≥ NminDiscrete g v T_min τ := by
  rw [exists_feasible_k_iff]
  unfold NminDiscrete kMax
  rw [ge_iff_le, Int.ceil_le, Int.le_floor,
      le_div_iff₀ (show (0:ℝ) < g + v by linarith), div_le_iff₀ hv]
  constructor <;> intro h <;> linarith

/-!  =====================  Milestone 2, Phase 2: discrete vs. continuous  =====================

`N_min^discrete` need not equal `⌈N_crit⌉` in general -- but the mathematics
was checked carefully first (per instruction, not assumed): the one-sided
inequality `N_min^discrete ≥ ⌈N_crit⌉` **is** always true, proved below, and
a concrete parameter choice exhibits it as a *strict* inequality. -/

/-- **FORMALLY VERIFIED, general.** `N_min^discrete ≥ ⌈N_crit⌉` always,
because `k_min` can only round `T_min/g` *up* before the rest of the
discrete formula is evaluated, and `Int.ceil` is monotone. -/
theorem ceil_Ncrit_le_NminDiscrete {g v T_min τ : ℝ} (hg : 0 < g) (hv : 0 < v) :
    ⌈Ncrit g v T_min τ⌉ ≤ NminDiscrete g v T_min τ := by
  have hgv : (0:ℝ) < g + v := by linarith
  have hkmin : T_min / g ≤ (kMin g T_min : ℝ) := Int.le_ceil _
  have harg : Ncrit g v T_min τ ≤ ((g + v) * (kMin g T_min : ℝ) + 1 / τ) / v := by
    unfold Ncrit
    have heq : T_min * (g + v) / g = (g + v) * (T_min / g) := by ring
    rw [heq]
    gcongr
  unfold NminDiscrete
  exact Int.ceil_mono harg

/-- **FORMALLY VERIFIED, exact witness.** At `g=2, v=1, T_min=3, τ=1`:
`T_min/g = 3/2` is not an integer, so `k_min = ⌈3/2⌉ = 2` rounds strictly
upward before the discrete formula is evaluated. `N_crit = 11/2`, so
`⌈N_crit⌉ = 6`; but `N_min^discrete` folds in the already-rounded `k_min`,
giving `⌈(3*2+1)/1⌉ = ⌈7⌉ = 7 ≠ 6`. The mismatch comes entirely from `k_min`
absorbing the rounding *inside* the discrete formula, one algebraic step
before `N_min^discrete`'s own outer ceiling, versus `N_crit` never rounding
until the very end. -/
theorem discrete_threshold_differs_from_ceil_continuous_example :
    NminDiscrete 2 1 3 1 ≠ ⌈Ncrit 2 1 3 1⌉ := by
  have hkmin : kMin 2 3 = 2 := by
    unfold kMin
    rw [Int.ceil_eq_iff]
    norm_num
  have hNmin : NminDiscrete 2 1 3 1 = 7 := by
    unfold NminDiscrete
    rw [hkmin, Int.ceil_eq_iff]
    norm_num
  have hNcrit : (⌈Ncrit 2 1 3 1⌉ : ℤ) = 6 := by
    unfold Ncrit
    rw [Int.ceil_eq_iff]
    norm_num
  rw [hNmin, hNcrit]
  decide

end
end GeneratorVerifier
