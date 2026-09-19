# Architecture ancestry

The audit brief asked for the chain

> LCF trusted kernel → proof certificates → certifying algorithms → solver + checker →
> translation validation → modern formal theorem-proving agents → this repository.

That chain is real, and it is the correct ancestry **for a producer/checker trust architecture**. This
repository is not on it. The honest ancestry runs somewhere else entirely, and both are given below so
that a reader can see exactly which one applies.

## The chain that does NOT lead here

Each step is a genuine ancestor of the *next*, and none is an ancestor of this repository.

| Step | What it established | Inherited by the next step | Present here? |
|---|---|---|---|
| **LCF** (`GordonMilnerWadsworth1979`) | large untrusted automation may only produce theorems through a small trusted kernel | the kernel discipline | only in the trivial sense that this is a Lean project |
| **de Bruijn criterion / independently checkable proof objects** | a proof should be an object a small program can re-check | proof objects as artifacts | no proof object is produced or consumed |
| **Proof certificates** (`WetzlerEtAl2014` for DRAT) | a fast complex search may emit a trace that a simple checker replays | separation of search from checking | no trace, no replay |
| **Certifying algorithms** (`McConnellEtAl2011`) | each output carries a witness; correctness of the *output* replaces correctness of the *algorithm* | the witness/checker contract | no witness, no checker |
| **Translation validation** (`PnueliEtAl1998`) | validate *this run* rather than verify the transformer | per-instance validation | nothing is validated per instance |
| **Proof-carrying code** (`Necula1997`) | the consumer checks a proof shipped with the artifact | consumer-side checking | nothing is shipped or checked |
| **Formal-AI agents** (`LeanDojo2023`) | an LLM proposes proof steps; the proof assistant accepts or rejects | kernel acceptance as the reward and the guarantee | no model, no proposal, no acceptance loop |

**Conclusion.** The trust relationship the brief asks about — untrusted producer, small trusted
checker, producer bugs cannot yield false theorems — already exists, fully, in LCF, in certifying
algorithms, in DRAT checking and in proof-carrying code. It is thoroughly classical. And this
repository is not an instance of it, so it neither competes with that literature nor adds to it.

## The chain that does lead here

What the repository formalizes is a **capacity/staffing model with a correlated-error term**. Its
ancestry is operations research and statistics.

| Step | What it established | What this repository inherits | What changes |
|---|---|---|---|
| **Two-stage line balancing** (textbook OR) | throughput of a two-stage pipeline is maximized by equalizing stage rates | `capacityFraction g v = v/(g+v)` and `throughput_le_capacityFraction` — verified here to be exactly the balance point | nothing mathematically; it is now Lean-checked |
| **M/M/1 stability and mean wait** (`Kleinrock1975`) | `lambda < mu` for stability; `W = 1/(mu - lambda)` | the *reading* of `margin > 0` as stability, and the definition of `upperBound` | **deliberately not formalized** — the README lists both as external model input |
| **Staffing thresholds / square-root staffing** (`HalfinWhitt1981`, `BorstEtAl2004`) | how many servers are needed to hold a service level, with a `sqrt(load)` correction | the question, and the deterministic first-order answer `N_crit` | the stochastic correction is dropped; `N_crit` solves a linear inequality |
| **Integer server counts** | server counts are integers, so the real-valued threshold must be rounded — and rounding up the continuous threshold is not always enough | `kMin`, `kMax`, `NminDiscrete`, and `ceil_Ncrit_le_NminDiscrete` with a strict witness | this is the sharpest thing in the repository: the inequality `⌈N_crit⌉ ≤ N_min^discrete` is proved always, and shown to be strict at an explicit parameter point |
| **Design effect / effective sample size** (`Kish1965`, `ShroutFleiss1979`) | correlated observations do not average down as `1/N`; effective independence saturates at `1/rho` | the structure of `J(p)`: the `sigma_c^2` term carries no `1/N` | the correlated term is weighted by `p^2` because `p` is the generator fraction |
| **Condorcet with correlated votes** (`Ladha1992`) | correlation caps the benefit of more voters | the same saturation, in decision-theoretic dress | — |
| **Bias–variance–covariance for ensembles** (`UedaNakano1996`) | an ensemble's error retains a covariance term as membership grows | the same algebra, in the repository's own application domain | — |
| **Lean 4 + mathlib** (`MouraUllrich2021`, `Mathlib2020`) | kernel-checked real and order algebra, `Int.ceil`/`Int.floor` API, `tendsto_inv_atTop_zero` | the entire proof platform | the formalization itself |

## Where the repository sits

It is a **Lean formalization of the algebraic skeleton of a capacity model**, with two pieces that are
slightly more than routine: the exact discrete/continuous threshold separation, and a kernel-checked
optimizer for the correlated-error quadratic. Its ancestry is Halfin–Whitt and Kish, not Milner and
Necula.

The name is the problem, not the mathematics. "Generator–verifier" in the AI literature
(`LeanDojo2023` and its successors) means a producer paired with a checker; here it means two kinds of
worker in a queue. A reader arriving from formal methods will expect the first and find the second.
