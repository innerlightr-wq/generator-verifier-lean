# Trust boundary

**There is no generator-to-verifier trust boundary in this repository.** That is the first thing this
document has to say, because the repository's name invites the opposite assumption.

## What the words mean here

In this development, "generator" and "verifier" are **agent roles in a capacity model**, not a producer
and a checker:

* `lam p N g = p * N * g` — the aggregate rate at which `p·N` *generator agents* produce work;
* `mu p N v = (1 - p) * N * v` — the aggregate rate at which `(1-p)·N` *verifier agents* consume it;
* `p` — the fraction of a population of `N` agents assigned to generation;
* `capacityFraction g v = v / (g + v)` — the `p` at which the two rates balance.

No candidate artifact is produced. No certificate is emitted, parsed, or checked. No component is
treated as untrusted. Searching the whole repository returns **zero** occurrences of `certificate`,
`trusted`, `untrusted`, `checker`, `TCB`, `sound`, `adversarial`, `hallucination` or `model-agnostic`.
The two occurrences of `kernel` are Lean's own kernel and a mention of graph propagation kernels in
future work; the five occurrences of `witness` all refer to an explicit *parameter witness* for a
strict inequality, not to a proof witness.

## What is actually trusted

The trust story is the ordinary one for a Lean formalization, and the repository states it accurately.

| Component | Trusted? | If it is wrong | Checked by | Formal guarantee |
|---|---|---|---|---|
| Lean 4.33.1 kernel | **yes** | every theorem below is void | nothing inside the repository | none — foundational |
| mathlib at the pinned revision | **yes** | proofs depending on the affected lemmas break | Lean kernel on rebuild | kernel-checked |
| the 14 definitions in `GeneratorVerifier/` (`lam`, `mu`, `throughput`, `capacityFraction`, `margin`, `lowerBound`, `upperBound`, `Ncrit`, `kMin`, `kMax`, `NminDiscrete`, `objective`, `unconstrainedOptimum`, `constrainedOptimum`) | **yes — semantically** | the theorems remain true but say nothing about the intended system | **nothing** | none; this is the real exposure |
| the theorem statements | checked | — | Lean kernel | `[propext, Classical.choice, Quot.sound]` only |
| the paper's queueing interpretation (`M(p) > 0` as stability, `W = 1/(mu - lambda)`) | **external, not formalized** | the algebra stands; its reading as latency does not | nothing | none, and the README says so |
| the correlated-error model `J(p)` | **external, taken as a definition** | the optimizer is still the optimizer of `J`; `J` may not describe real systems | nothing | none, and the README says so |
| any LLM, script or generator | **absent** | — | — | — |

## The three trust claims, kept apart

**Logical soundness.** All eight principal theorems were re-checked in this audit with `#print axioms`
and depend on exactly `[propext, Classical.choice, Quot.sound]` — the three standard Lean axioms. No
`sorryAx`, no custom `axiom`, no `unsafe`, no `native_decide`, no `@[implemented_by]`. `lake build`
completes with 8713 jobs and 8 style-linter warnings (docstring placement, a deprecated `push_neg`).
**This claim is verified.**

**Implementation reliability.** Nothing is transported into Lean from outside: there is no parser, no
serialization, no generated source, no data file. The only implementation risk is the usual one —
that a definition says something other than what was meant. **Nothing to check, because nothing
crosses a boundary.**

**Semantic adequacy.** This is where the whole exposure sits, and the README is unusually candid about
it. `upperBound` is *defined* as the number the relation `W = 1/(mu - lambda)` produces once combined
with `W <= tau_max`; that relation is never stated or proved. `J(p)` is *defined* as the paper's
quadratic; that it models real correlated failure among agents is not claimed. So every theorem is
exactly true, and every theorem is about the model rather than about a deployed system. The README's
own sentence — "This repository does not verify the safety of multi-agent AI systems" — is the correct
summary and should be preserved verbatim in any future version.

## What would have to change for the name to fit

If an LLM or search procedure ever emitted a candidate operating point `(N, p)` and a Lean-side
function decided its feasibility, then the architecture would become an instance of
**certifying computation** (`McConnellEtAl2011`), the Boolean-reflection pattern
`verify x = true ↔ Specification x` would be the theorem to prove, and the classical ancestry in this
bibliography would start to apply. None of that exists today, and this audit does not recommend
retrofitting the vocabulary onto a capacity model.
