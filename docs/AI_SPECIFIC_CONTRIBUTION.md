# What is specific to AI or LLM generators here

**Short answer: nothing in the formalized mathematics, and one thing in the motivation.**

The brief asked what changes when the generator is an LLM — probabilistic producer, deterministic
verifier, model independence, replaceable generator, auditable artifact, kernel-defined trust boundary.
Those are real and interesting properties of *certifying architectures*. None of them is a property of
this repository, because this repository has no producer, no artifact and no checker. See
[`TRUST_BOUNDARY.md`](TRUST_BOUNDARY.md).

## What the AI content actually is

The repository formalizes a model whose *intended application* is multi-agent LLM systems: a population
of `N` agents split between generating candidate outputs and verifying them, where verification capacity
can bottleneck the system and where verifier errors may be correlated. That is a sensible thing to model
and it is where the AI relevance lives — in the interpretation of `g`, `v`, `N` and the variance
parameters, not in the algebra.

Two model-level points are worth stating because they are genuinely about AI systems:

1. **Verification capacity is a first-class constraint.** The capacity-matching result says throughput
   is maximized at `p_c = v/(g+v)`, and `upperBound_lt_capacityFraction` says the
   throughput-maximizing split is *never itself latency-feasible* — you must run strictly below the
   balance point to meet a latency bound. In a deployment where "add more generator agents" is the
   obvious lever, that is a useful thing to have pinned down exactly. The observation is elementary but
   not vacuous.
2. **Correlated verifier failure caps the benefit of scale.** `J(p)`'s correlated term carries no
   factor of `1/N`, so no amount of additional agents drives it to zero, and the optimal generator
   fraction decays like `1/N`. Applied to LLM agents drawn from the same model — or the same family,
   or the same training data — this is the right warning to make quantitative.

## Why neither is an AI-specific contribution

Both are classical, and both predate the LLM literature by decades. Point 1 is two-stage line balancing
plus a staffing threshold (`HalfinWhitt1981`, `BorstEtAl2004`). Point 2 is the design effect and
effective sample size (`Kish1965`), the intraclass-correlation decomposition (`ShroutFleiss1979`), the
Condorcet jury theorem with correlated votes (`Ladha1992`), and the bias–variance–covariance
decomposition of ensembles (`UedaNakano1996`) — the last of which is already a machine-learning result.
Verified in this audit: `J(p)`'s structure is exactly the classical `rho + (1-rho)/N` form.

So the AI-era element is the **application and the framing**, not the mathematics. That is a legitimate
contribution to claim, and it is much weaker than "a formal result about multi-agent AI systems". The
README already draws this line correctly and at length; the audit's recommendation is to keep it.

## The claims that would be AI-specific, and are absent

For the record, because the brief asks: *model-agnostic verification*, *generator/verifier decoupling*,
*replaceable generators*, *auditable certificates*, *kernel acceptance as a reward signal*, and
*probabilistic generator with deterministic verifier* are all absent from this repository. None appears
in the source, and none is claimed. Were they added, the relevant prior art would be
`McConnellEtAl2011` and the formal-AI systems literature (`LeanDojo2023` and its successors), and the
audit's judgement is that the generator–verifier framing is **already standard terminology in that
literature** — so claiming it would require a specific technical delta, not the name.

## One thing the repository does have that is worth naming

The README's **FORMALLY VERIFIED / EXTERNAL MODEL INPUT / OPEN** split is, in this auditor's view, the
most transferable thing in the repository. It states, per result, exactly which parts Lean checked and
which parts are the paper's modeling assumptions taken as definitions — including the explicit
sentence that Lean "verifies the optimizer and scaling laws of the correlated-error model", not
"proves effective independence in AI systems". That discipline is what keeps a formalization of a
*model* from being read as a verification of a *system*, and it is rarer than it should be in work that
mixes formal methods with AI claims. It is a methodological contribution, not a mathematical one, and
it should be described that way.
