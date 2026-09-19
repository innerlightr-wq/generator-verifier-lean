# Novelty and provenance audit

**Date** 2026-09-18 · **State audited** `2ed30c1` (= `origin/main`), no tags ·
**Bibliography** [`references.bib`](../references.bib), 16 entries ·
**Deposit** `DeJesus2026gv` = `10.5281/zenodo.22342517` (concept `10.5281/zenodo.22342516`), the paper
this repository formalizes

## 0. The audit brief's premise does not match this repository

The brief asked what this repository adds beyond

> untrusted producer → certificate → small trusted checker → kernel-verified result

**It adds nothing to that architecture, because it is not an instance of it.** In this development
"generator" and "verifier" are **agent roles in a capacity model** — agents producing work at rate `g`
and agents consuming it at rate `v`, with `p` the fraction assigned to generation. There is no
candidate artifact, no certificate, no checker, and no untrusted component.

Evidence, from a repository-wide search: **zero** occurrences of `certificate`, `trusted`, `untrusted`,
`checker`, `TCB`, `sound`, `adversarial`, `hallucination`, `model-agnostic` or `LCF`. `kernel` occurs
twice (Lean's kernel; graph propagation kernels in future work) and `witness` five times, always meaning
an explicit *parameter witness* for a strict inequality.

Consequently the brief's steps on adversarial generators, certificate corruption, generator replacement,
parser trust, Boolean reflection, specification gaming and model-agnosticism have **no object in this
repository**. They are not reported as passed or failed; they are reported as inapplicable, and
[`TRUST_BOUNDARY.md`](TRUST_BOUNDARY.md) says what the trust situation actually is.

The repository does not make the claim the brief assumed. Its README is careful and accurate throughout.
The mismatch is in the name, and in what a reader arriving from formal methods will expect from it.

## 1. Claim inventory

| # | Claim | Where | Class |
|---|---|---|---|
| C1 | `p_c = v/(g+v)` balances generation and verification rates | `Capacity.lean` | formal theorem (elementary) |
| C2 | the common value at balance is `Ngv/(g+v)` | `Capacity.lean` | formal theorem |
| C3 | margin factorization `M(p) = N(g+v)(p_c - p)` and its sign trichotomy | `Capacity.lean` | formal theorem |
| C4 | throughput is maximized at `p_c` on `[0,1]` | `Capacity.lean` | formal theorem |
| C5 | `lambda(p) >= T_min ↔ p >= lowerBound` | `FeasibleRegion.lean` | formal theorem |
| C6 | `N(g+v)(p_c - p) >= 1/tau ↔ p <= upperBound` | `FeasibleRegion.lean` | formal theorem |
| C7 | `p_+ - p_- = (N - N_crit)·v/(N(g+v))` | `FeasibleRegion.lean` | formal theorem (the key identity) |
| C8 | **continuous feasibility ↔ `N >= N_crit`** | `FeasibleRegion.lean` | formal theorem (headline) |
| C9 | integer analogues `kMin`, `kMax`, and **feasibility ↔ `N >= N_min^discrete`** | `FiniteAgents.lean` | formal theorem (headline) |
| C10 | `⌈N_crit⌉ <= N_min^discrete`, with an explicit strict witness | `FiniteAgents.lean` | formal theorem (sharpest result) |
| C11 | `upperBound < p_c`: the throughput-maximizing split is never latency-feasible | `MainTheorem.lean` | formal theorem |
| C12 | `J(p)` optimizer by completing the square; `[0,1]`-constrained version | `EffectiveIndependence.lean` | formal theorem |
| C13 | `N·p0` is independent of `N`; `p0 → 0` as `N → ∞` | `EffectiveIndependence.lean` | formal theorem |
| C14 | no `sorry`, no `admit`, no custom `axiom` | README | trust claim (**verified**) |
| C15 | the M/M/1 reading, `W = 1/(mu-lambda)`, and `J(p)` itself are external model input | README | scoping claim (**accurate**) |
| C16 | "This repository does not verify the safety of multi-agent AI systems" | README | scoping claim (**accurate and important**) |

**No novelty claim appears anywhere in the repository.** The README makes none, and explicitly disclaims
the stronger readings. That is unusual and worth recording.

## 2. Independent verification

Everything below was recomputed in this audit without using the repository's proofs.

* **Build.** `lake build` on Lean 4.33.1 with mathlib pinned to `v4.33.1`: **8713 jobs, exit 0**,
  8 warnings, all style-linter (docstring placement; one deprecated `push_neg`).
* **Axioms.** All eight principal theorems — `continuous_feasibility_iff_N_ge_Ncrit`,
  `finite_feasibility_iff_N_ge_NminDiscrete`, `ceil_Ncrit_le_NminDiscrete`,
  `discrete_threshold_differs_from_ceil_continuous_example`,
  `objective_minimized_at_unconstrainedOptimum`, `unconstrainedOptimum_tendsto_zero`,
  `throughput_le_capacityFraction`, `upperBound_lt_capacityFraction` — depend on exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no custom `axiom`, no `unsafe`, no
  `native_decide`, no `@[implemented_by]`. **C14 is verified.**
* **The key identity (C7).** Confirmed symbolically: `p_+ - p_- = (N - N_crit)·v/(N(g+v))` exactly.
  Since the factor is positive, C8 is the sign of a positive multiple of `N - N_crit` — a one-line
  argument, exactly as the file's own docstring says.
* **Capacity matching (C1, C2).** `lam(p_c) - mu(p_c) = 0` and the common value is `Ngv/(g+v)`.
* **The objective (C12, C13).** `dJ/dp = 0` at `p0 = (sigma_eta^2 - sigma_i^2)/(2 N sigma_c^2)`;
  `J(p) - J(p0) = sigma_c^2 (p - p0)^2`; `N·p0 = (sigma_eta^2 - sigma_i^2)/(2 sigma_c^2)`, independent
  of `N`.

**Software hygiene.** No duplicate or shadow implementations: one definition of each function, one
module per topic, `GeneratorVerifier.lean` a plain import list, no path hacks, no generated code, no data
files. `Basic.lean` is a one-line `def hello := "world"` placeholder — a `lake new` leftover, harmless,
and imported by the top-level module. There is **no test suite**, and nothing to test: the content is
theorems, and the kernel is the test.

## 3. What the formalized results actually are

Honest assessment, which the README largely shares.

**C1–C8, C11 are elementary real algebra.** C8, the continuous headline, is solving a linear inequality
in `N`: the feasibility gap is a positive multiple of `N - N_crit`, so the equivalence is a sign check.
C1 is the classical two-stage line-balancing optimum (equalize stage rates). C4 follows from the
factorization. C11 is an inequality between two explicit expressions. None of this is hard, and the
files say so — "a one-line sign argument rather than a case-by-case inequality chase".

**C9 and C10 are the sharpest content.** The discrete analogue involves `Int.ceil`/`Int.floor`
manipulation rather than pure real algebra, and C10 — `⌈N_crit⌉ ≤ N_min^discrete` always, with an exact
parameter point where it is strict — is a genuine, if small, observation: **rounding the continuous
threshold up is not in general sufficient when agent counts are integers.** That is the integer-staffing
phenomenon, and having it pinned down exactly with a witness is the most useful formal output here.

**C12–C13 are the classical correlated-average structure.** Verified: the `sigma_c^2` term carries no
factor of `1/N` while the other two do, which is exactly `rho + (1-rho)/N`. So effective independence
saturates and the optimal generator fraction decays as `1/N`. Completing the square is routine; the
structure is `Kish1965`, `ShroutFleiss1979`, `Ladha1992` and `UedaNakano1996`.

## 4. Soundness, completeness, and semantic adequacy

**Soundness / completeness.** These words do not apply: there is no verifier to be sound or complete.
The repository uses neither term (one occurrence of "complete", in prose about a model being complete).
No correction needed.

**Semantic adequacy is the entire exposure, and it is disclosed.** `upperBound` is *defined* as the
number `W = 1/(mu - lambda)` produces under `W <= tau_max`; that relation is never proved. `J(p)` is
*defined* as the paper's quadratic; its empirical validity is explicitly not claimed. The theorems are
exactly true of the model and say nothing about a deployed system. The README states this in three
places, including the sentence "This repository does not verify the safety of multi-agent AI systems".
**Recommendation: preserve that sentence verbatim in every future version.**

## 5. Claim-strength audit

Repository-wide sweep for `new`, `novel`, `first`, `trusted`, `verified`, `guaranteed`, `safe`, `sound`,
`complete`, `formally verified`, `independent`, `model-agnostic`, `AI-proof`, `hallucination-proof`.

| Wording | Where | Verdict |
|---|---|---|
| `hallucination-proof`, `AI-proof`, `model-agnostic`, `guaranteed`, `safe` | — | **absent**. Nothing to remove |
| "FORMALLY VERIFIED" headers | README, per result | **SAFE** — each is scoped to the stated algebra, and the axiom audit confirms it |
| "No `sorry`, no `admit`, no custom `axiom` anywhere" | README | **SAFE** — verified |
| "machine-checked formalization ... of the exact algebraic operating-region structure" | README | **SAFE** — "algebraic skeleton" is the accurate description and the README uses it |
| "This is not a formalization of M/M/1 queueing theory" | README | **SAFE** and load-bearing |
| "effective independence" as a section name | `EffectiveIndependence.lean` | **NEEDS QUALIFICATION** (already given) — the README's own correction, that Lean "verifies the optimizer and scaling laws of the correlated-error model", is the right phrasing and should lead rather than follow |
| `generator`, `verifier` in the project name | throughout | **NEEDS QUALIFICATION** — see §0. A one-line gloss at first use would prevent a formal-methods reader from expecting a producer/checker architecture |
| "no probability, no stochastic process anywhere in the proof" | README | **SAFE** — confirmed; `Mathlib` is imported wholesale but no probabilistic lemma is used |

The claim-strength position is, unusually, **already correct**. The only recommended additions are a
gloss on the project name and one missing citation layer (§6).

## 6. What is missing: the prior-art layer

The repository has **no bibliography at all** — no `references.bib`, no `CITATION.cff`, and the README
cites nothing but its own Zenodo deposit. A reader cannot see that:

* `p_c = v/(g+v)` is two-stage line balancing;
* `N_crit` is the deterministic case of a staffing threshold (`HalfinWhitt1981`, `BorstEtAl2004`);
* `J(p)`'s saturation is the design effect and effective sample size (`Kish1965`, `ShroutFleiss1979`),
  the Condorcet jury theorem with correlated votes (`Ladha1992`), and the
  bias–variance–covariance decomposition of ensembles (`UedaNakano1996`);
* the integer-threshold phenomenon of C10 is the discrete-staffing question.

`references.bib` now supplies these, together with the Lean platform citations and a small canon of the
producer/checker literature included **specifically to document that this repository is not an instance
of it** (`GordonMilnerWadsworth1979`, `McConnellEtAl2011`, `Necula1997`, `PnueliEtAl1998`,
`WetzlerEtAl2014`, `LeanDojo2023`).

## 7. Novelty classification

| Claim | Closest prior art | Standard concept | Repo contribution | Classification | Confidence |
|---|---|---|---|---|---|
| C1, C2, C4 capacity matching | textbook OR line balancing | equalize stage rates | Lean-checked statement | `CLASSICAL` | high |
| C3 margin factorization | — | algebraic rearrangement | Lean-checked | `KNOWN / REPARAMETERIZED` | high |
| C5–C8 continuous feasibility | `HalfinWhitt1981`, `BorstEtAl2004` | staffing threshold | deterministic first-order case, Lean-checked | `KNOWN / REPARAMETERIZED` | high |
| C9 discrete feasibility | integer staffing | ceiling/floor thresholds | Lean-checked exact equivalence | `FORMALIZATION CONTRIBUTION` | med-high |
| **C10 `⌈N_crit⌉ ≤ N_min^discrete`, strict witness** | integer staffing | discrete-vs-continuous gap | **exact statement plus explicit witness** | `FORMALIZATION CONTRIBUTION` — the sharpest item | med-high |
| C11 `upperBound < p_c` | — | elementary inequality | Lean-checked | `KNOWN / REPARAMETERIZED` | high |
| C12, C13 `J(p)` optimizer and `1/N` scaling | `Kish1965`, `ShroutFleiss1979`, `Ladha1992`, `UedaNakano1996` | design effect / effective sample size / bias–variance–covariance | Lean-checked optimizer of the paper's specific quadratic | `CLASSICAL` structure, `FORMALIZATION CONTRIBUTION` for the Lean proof | high |
| the epistemic split in the README | — | — | a per-result FORMALLY VERIFIED / EXTERNAL MODEL INPUT / OPEN ledger | `AI-ERA APPLICATION` (methodological) | med |
| the producer/checker architecture | LCF, certifying algorithms, DRAT, PCC | certifying computation | **none — not implemented** | `CLASSICAL TRUST ARCHITECTURE`, not instantiated here | high |

## 8. Publication classification: **B / D**

`B — new Lean formalization of a classical architecture` is the accurate description of the formal
content: a careful, axiom-clean formalization of an elementary capacity model, whose one distinctive
result is the discrete/continuous threshold separation with a witness.

The `D` component — `major novelty reduction` — applies to the framing rather than the mathematics. If
the work is presented as a contribution to generator–verifier *architectures* or to multi-agent AI
*safety*, that framing does not survive: the architecture is classical and uninstantiated here, and the
correlated-error result is the design effect. The README already refuses both readings, which is why
this is a framing risk rather than a defect.

Not `E`: nothing is mathematically wrong. Not `A` or `C` for the architecture question, because there is
no architecture to assess.

**Strongest surviving contribution.** Two things, both modest and both real: the exact
discrete-versus-continuous staffing threshold with an explicit strict witness, and the per-result
epistemic ledger separating what Lean checked from what the model assumes. **No Zenodo record was
updated and no manuscript was modified.**
