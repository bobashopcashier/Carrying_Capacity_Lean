# Lean formalization of carrying-capacity mean-field models

**Status: partial formalization, with checked proofs and an explicit boundary.**
This project formalizes definitions and proof components from both
[DeWitt, Evans, Hiesmayr, and Hummel (2024)](https://arxiv.org/html/2307.06010v2)
and Kenny Xie's *Mean-Field Limits for Multitype Birth–Death Systems with
Unbounded Moment Feedback*
([manuscript source](https://github.com/bobashopcashier/Carrying_Capacity_fixed/blob/c7688113e4a92910b6403fdd8ecb14fb0f3ce6a9/new.tex)). It does **not** yet
prove either paper's full stochastic existence, mean-field limit, or
propagation-of-chaos theorem. Those conclusions are neither axioms nor hidden
fields of a structure in this project.

This repository contains only the Lean verification. The paper is maintained
separately in [Carrying_Capacity_fixed](https://github.com/bobashopcashier/Carrying_Capacity_fixed).
The source snapshot is manuscript commit `c768811`; its `new.pdf` is identical
to the PDF supplied for formalization.

## Build and check

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
python3 scripts/check_proofs.py
```

`lean-toolchain` pins Lean **4.19.0**, and `lake-manifest.json` locks mathlib and
its dependencies. Mathlib is pinned to release `v4.19.0`, commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. A compatible older release is used
deliberately so these proofs have a reproducible environment.

If the compiled cache helper cannot start on macOS, the equivalent interpreted
command is:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
```

Open this folder in a Lean-enabled editor. Import `CarryingCapacity` to use all
modules. The proof audit checks the declarations for unsupported axioms and
rejects proof placeholders. The permitted foundational axioms are Lean's
`propext`, `Classical.choice`, and `Quot.sound`; these are not assumptions about
the stochastic processes.

The complete build passed without warnings, and the exhaustive audit checked
**741 theorem declarations and 997 safe declarations across 28 modules**.
These counts include private helpers and compiler-generated declarations;
they are not counts of distinct results from the papers. Separate negative
checks confirmed that the audit rejects
custom project axioms and both public and private placeholder proofs.

## What is formalized

| File | Checked content | Boundary |
|---|---|---|
| [MomentGeometry](CarryingCapacity/MomentGeometry.lean) | Discrete κ scales; genuine adapted state metric; weight and ℓ¹ bounds; finite moment and Lyapunov sublevels | Does not prove probability-space completeness or Wasserstein–Orlicz results |
| [Transport](CarryingCapacity/Transport.lean) | Actual probability laws with integrable κ weight; actual marginal couplings; finite coupling costs; infimum transport cost, symmetry and zero self-distance; `\|Mκ(μ)−Mκ(ν)\| ≤ Wκ(μ,ν)` and consequent moment convergence | The metric, completeness, and empirical LLN results are supplied by the modules below; general optimal-plan existence remains separate |
| [TransportMetric](CarryingCapacity/TransportMetric.lean) | Actual disintegration-based gluing; triangle inequality; separation by measurable events; a genuine `MetricSpace`; Lipschitz moment map | Does not assert existence of an optimal coupling for every pair of laws |
| [TransportCompleteness](CarryingCapacity/TransportCompleteness.lean) | Infinite simultaneous coupling through Ionescu–Tulcea; constructed finite-moment limit law; transport tail estimate; genuine `CompleteSpace` instance | Time-dependent invariant flow spaces and nonlinear contraction remain separate |
| [EmpiricalMeasure](CarryingCapacity/EmpiricalMeasure.lean) | Genuine finite empirical probability laws; exact integral identities; paired and permuted transport couplings; single-update estimate; generator bridge | Exact optimal matching is a separate result |
| [EmpiricalMatching](CarryingCapacity/EmpiricalMatching.lean) | Splits arbitrary couplings across repeated particle labels; Birkhoff decomposition; exact attained permutation optimum; measurable optimal matching preserving the empirical law | Randomized exchangeable initialization is supplied by `ExchangeableMatching` |
| [FiniteTransport](CarryingCapacity/FiniteTransport.lean) | Explicit common-mass coupling; transport bounded by diameter times total variation on a common finite support; atomic convergence implies transport convergence | Both laws must be concentrated on the same finite set |
| [EmpiricalLLN](CarryingCapacity/EmpiricalLLN.lean) | Full almost-sure Wκ convergence of empirical laws from measurable pairwise independent samples with a common finite-moment law; scalar, tail, and truncated strong laws | A fixed-law sampling theorem; uniform convergence of stochastic paths remains separate |
| [EmpiricalMeanError](CarryingCapacity/EmpiricalMeanError.lean) | Derived empirical Lyapunov expectations and uniform integrability; expected Wκ error tends to zero; error ≤2Mκ; time-integrated convergence under a uniform Lyapunov bound | The time theorem assumes jointly measurable samples and a continuous law curve; it does not construct the nonlinear process |
| [ExchangeableMatching](CarryingCapacity/ExchangeableMatching.lean) | Independent uniform common permutation of optimally matched arrays; exact preservation of both full vector laws; joint exchangeability; optimal cost and expectation identities; iid comparison specialization | Expected-error convergence is connected through explicit empirical-error hypotheses; process coupling remains separate |
| [Symmetrization](CarryingCapacity/Symmetrization.lean), [EmpiricalGenerator](CarryingCapacity/EmpiricalGenerator.lean) | Permutation equivariance; empirical equality iff relabeling; actual exchangeable symmetrization kernel; deterministic empirical state under that kernel; well-defined quotient generator and intertwining identity | Does not prove process exchangeability, the Markov mapping theorem, or Feller generation |
| [LyapunovTails](CarryingCapacity/LyapunovTails.lean) | Superlinear Lyapunov control gives uniform moment tails; genuine uniform integrability of empirical transport errors; in-probability initialization upgrades to expected-error convergence | Uses a common probability space and genuine integrability; does not supply the initial in-probability convergence assumption |
| [Framework](CarryingCapacity/Framework.lean) | Multitype birth/death/mutation maps; invalid-jump convention; generator linearity; distinct original TV and extended moment assumptions | Assumption structures record hypotheses; they are not the main theorems |
| [RateControl](CarryingCapacity/RateControl.lean) | Every admissible jump has adapted length at least one; total rate is bounded by weighted activity; actual finite-configuration Lyapunov sublevels are finite | Gives deterministic finiteness needed for freezing, without constructing the driving random measures |
| [FiniteGenerator](CarryingCapacity/FiniteGenerator.lean) | Single-particle update identity; exact generator identity for empirical averages; averaged Lyapunov drift | Does not apply Dynkin's formula or construct a process |
| [Freezing](CarryingCapacity/Freezing.lean) | Finite-proposal recursion; one-jump enlargement; retaining the exit jump; permanent freezing; unique compatible patch; finite-horizon agreement; exit-tail bounds imply almost-sure exhaustion and patching | Requires the exit bounds and compatibility; does not derive them from a Poisson SDE or prove adaptedness of the patch |
| [CountableJumpProcess](CarryingCapacity/CountableJumpProcess.lean) | Actual product exponential waiting times; independence; positive waits and strictly increasing arrivals tending to infinity almost surely; measurable locally finite arrival counting measure | One-time count laws are supplied below; independent increments remain open |
| [FrozenProcess](CarryingCapacity/FrozenProcess.lean) | Actual independent uniform marks; measurable thinning paths from a deterministic initial state; finite-range confinement; a.s. right continuity, left limits, and permanent freezing | Does not yet establish adaptedness, the compensator, or common-noise compatibility across cutoff clock rates |
| [PoissonClockLaw](CarryingCapacity/PoissonClockLaw.lean) | Exponential survival and conditional memorylessness; residual-life law; exact zero-proposal probability for the constructed count | These partial clock laws are not a proof of the full Poisson-process characterization |
| [PoissonIncrements](CarryingCapacity/PoissonIncrements.lean) | Shifted-clock law and head/tail independence; nonatomic arrivals; renewal recurrence; exact Poisson law of the actual count at every nonnegative time | Despite the module name, stationary independent increments are not yet proved |
| [MarkedNoise](CarryingCapacity/MarkedNoise.lean) | One actual counting-measure family for every cutoff, built from independent unit strips; measurable noise; simultaneous local finiteness and absence of coincident arrival times | The full PRM law, chronological frozen paths on this space, adaptedness, and compensation remain open |
| [FrozenCompatibility](CarryingCapacity/FrozenCompatibility.lean) | Nested frozen recursions agree through their actual first exit, including the exit jump; exit indices are monotone; stopped continuous-time paths agree under a common locally finite clock | Uses the same proposal sequence and decoder; compatibility across different cutoff event lists and stopping-time properties remain open |
| [ThinningKernel](CarryingCapacity/ThinningKernel.lean) | Exact accepted-label probabilities; mean one-proposal increment; clock-rate normalization equals the frozen generator; finite active sets admit positive rate bounds | One-step expectation identities do not replace continuous-time compensation |
| [Models](CarryingCapacity/Models.lean) | Scalar birth–death generator identities through cubic order; full three-term positive-increment coupling bounds; activity growth; cubic Lyapunov domination, drift and superlinearity; integrals of generator identities | Scalar model only; integrated identities are not time derivatives of stochastic expectations |
| [ModelTransport](CarryingCapacity/ModelTransport.lean) | Actual generalized moments control arbitrary nonnegative Lipschitz mortality; quadratic-feedback coupling and activity estimates follow from transport | Uses the concrete cubic Lyapunov choice, rather than every real exponent greater than two |
| [QuadraticModel](CarryingCapacity/QuadraticModel.lean) | Instantiates the actual single-type rates in `Framework`; proves `MomentCouplingBound` and `MomentActivityBound`; constructs `LyapunovControl` with `Ψ(x)=1+x³` for arbitrary nonnegative Lipschitz mortality | Checks the dynamic hypotheses of Proposition 7.7; initialization and the stochastic limit corollary remain outside this result |
| [LimitArguments](CarryingCapacity/LimitArguments.lean) | Successive population-then-cutoff limit; reciprocal cutoff specialization; three-region scalar criterion; counterexample to uncontrolled diagonal limits | Assumes the required estimates and tail limits, rather than asserting their stochastic derivation |

The [paper map](docs/PAPER_MAP.md) identifies source statements and outstanding
proof dependencies. Some modules support both papers; others concern only
the extension. In particular, the original mean-field theorem allows weakly
convergent deterministic empirical initial laws without the extension's
uniform Lyapunov bound. It cannot be recovered merely by specializing κ to
the identity in a theorem that assumes those stronger moments. The original
boundary rule also suppresses births when the corresponding type is absent.

## Reading the central statements

The notation in the paper corresponds to:

| Paper | Lean |
|---|---|
| `E = ℕ₀ᴰ` | `State D` |
| `κ` with normalized discrete increments | `MomentScale` |
| `Kκ(x)` | `momentWeight κ x` |
| `ρκ(x,y)` | `adaptedDistance κ x y` |
| `Mκ(μ) = E[Kκ(X)]` | `moment μ` |
| `Wκ(μ,ν)` | `wasserstein μ ν` |
| `T_h x` | `Jump.advance h x` |
| `Vᴺ(z) = N⁻¹ Σᵢ Ψ(zᵢ)` | `FiniteGenerator.empiricalMean Ψ z` |
| Consistent stopped paths | `Freezing.ExitFamily` |

For example, `moment_difference_le_wasserstein` is proved by transporting
both moments to a coupling measure, bounding the integral of their absolute
difference by the integral of the adapted distance, and then taking the
infimum over all couplings. Nonemptiness of that set comes from an explicitly
constructed product coupling. Integrability is proved before the integral
inequalities are used.

`Freezing.ae_existsUnique_patch_of_exit_bounds` is a conditional but genuine
measure-theoretic result: reciprocal exit-probability bounds, monotone exit
times, and compatibility yield an almost-sure unique patch. It does not take
non-explosion as a hypothesis. The random frozen paths are now constructed
from exponential clocks and uniform marks. The common marked noise has been
constructed separately, with simultaneous local finiteness and distinct event
times. Connecting its cutoff event lists to compatible continuous-time frozen
paths, establishing independent increments and compensation, and deriving exit
bounds from the model's Lyapunov drift remain outstanding.

`EmpiricalLLN.wasserstein_strongLaw` proves the full empirical transport strong
law using finite-state common-mass couplings and vanishing moment tails.
`EmpiricalMeanError` upgrades this to expected and time-integrated error
convergence under the manuscript's Lyapunov assumptions.
`ExchangeableMatching.exists_exchangeable_optimal_iid_coupling` constructs the
actual paired law while preserving both full vector marginals. It uses a fresh
uniform permutation of the matched pair array to obtain joint exchangeability.

The quadratic coupling calculation includes the shared-jump contribution.
For a nonlinear κ, even a simultaneous birth can increase the distance;
controlling only unmatched jumps would miss this term.

## Remaining work for complete paper formalizations

1. Independent Poisson increments and the full marked PRM law; continuous-time
   frozen paths on the common noise; adaptedness, compensation, Dynkin's formula,
   and Lyapunov exit estimates.
2. For the original theorem: Feller generation, the Markov empirical process,
   Yule domination, tightness, and convergence under its weaker initial data.
3. For the extension: the invariant space of time-dependent moment laws,
   deterministic-environment forward uniqueness, and the nonlinear fixed point.
   The underlying moment-law metric space is now proved complete.
4. Assemble the initialization coupling from the proved empirical-error limits,
   then derive localized process coupling, time-grid estimates, and path-space
   propagation of chaos.

The Lean kernel checks the formal statements and proofs. Matching them to a
paper remains a mathematical review task, which is why the source map and
these scope distinctions are part of the deliverable.
