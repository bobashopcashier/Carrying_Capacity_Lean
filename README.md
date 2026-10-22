# Carrying_Capacity_Lean

A Lean 4 formalization of

> Steven N. Evans, Kenny Xie, *Mean-Field Limits for Multitype Birth–Death Systems with
> Unbounded Moment Feedback*
> ([manuscript source](https://github.com/bobashopcashier/Carrying_Capacity_fixed/blob/c7688113e4a92910b6403fdd8ecb14fb0f3ce6a9/new.tex),
> commit `c768811`).

Every numbered lemma, proposition, theorem, and corollary of the manuscript has
a Lean proof. The proofs use only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and contain no `sorry`. The combined theorem statements and quantitative refinements are listed below.

This repository holds only the Lean code. The paper lives in
[Carrying_Capacity_fixed](https://github.com/bobashopcashier/Carrying_Capacity_fixed).
Result numbers below follow commit `c768811`. The AMS-formatted edition has the
same numbering and mathematics.

## Main results

All names are in the `CarryingCapacity` namespace. The paper's hypotheses
appear as:

| Paper | Lean |
|---|---|
| Assumption 2.2 (synchronous coupling) | `MomentCouplingBound κ q` |
| Assumption 2.3 (weighted activity) | `MomentActivityBound κ q` |
| Assumption 2.5 (Lyapunov control) | `LyapunovControl κ q`, a structure carrying Ψ and an explicit admissible drift constant |
| Assumption 2.6 (initialization) | explicit hypotheses on the initial configurations: exchangeability, the uniform bound on `E Π₀ᴺ(Ψ)`, and `Wκ(Π₀ᴺ, ν) → 0` in probability |
| ν ∈ Pκ(E) with ν(Ψ) < ∞ | `ν : MomentLaw κ D` and `Integrable control.function ν.measure` |

### Theorem 2.7

[`MainTheorem.main_theorem`](CarryingCapacity/MainTheorem.lean) proves all four
parts together in `MainTheorem.Conclusions`, on the supplied probability space.
The underlying declarations remain available separately:

| Part | Lean |
|---|---|
| (1) Unique non-explosive strong solution of the finite system | `PrescribedConfigurationProcess.process`, `.ae_counting_identity`, `.ae_finite_activity`, `.ae_unique_of_coordinate_equations` |
| (2) Unique nonlinear flow v | `NonlinearForwardUniqueness.existsUnique_interval_solution` |
| (3) `sup_{t≤T} Wκ(Πᴺ_t, v_t) → 0` and `sup_{t≤T} \|Mκ(Πᴺ_t) − Mκ(v_t)\| → 0` in probability; `Πᴺ ⇒ v` in the Skorokhod J1 topology | `PrescribedPopulationLimits.measure_runningError_gt_tendsto_zero`, `.measure_runningMomentError_gt_tendsto_zero`, `PrescribedPathLimits.empiricalPathLaws_tendsto` |
| (4) Path-space propagation of chaos | `PrescribedPathLimits.focalPathLaws_tendsto` |

### By section

| Section | Results | Main declarations |
|---|---|---|
| 2 | Wκ is a complete metric; (2.4); Remark 2.1 (Wₚ comparison) | `momentLawCompleteSpace`, `moment_difference_le_wasserstein`, `PowerWasserstein.distance_rpow_le_wasserstein`, `PowerWasserstein.wasserstein_le_distance`, `PowerWasserstein.topology_eq` |
| 3 | Lemmas 3.1–3.2, Props 3.3–3.4 (including the martingale problem and exchangeability), Lemma 3.5, Cor 3.6 | `PrescribedConfigurationFrozenEquation.ae_unique_of_coordinate_equations`, `PrescribedConfigurationCompatibility.ae_stopped_compatibility`, `PrescribedConfigurationLocalization.exit_probability_le`, `PrescribedConfigurationMartingale.generator_martingale`, `PrescribedConfigurationExchangeability.supplied_exchangeable`, `PrescribedConfigurationEstimates.weightedActivity_le_before_exit`, `PrescribedConfigurationUniformEstimates.sup_runningLyapunov_probability_le` |
| 4 | Lemma 4.1, Prop 4.2, Thm 4.3, Cor 4.4 | `PrescribedRandomEnvironmentComparison.expected_stoppedDistance_le_couplingActivity`, `PrescribedDeterministicEnvironment.law_unique`, `NonlinearForwardUniqueness.existsUnique_interval_solution`, `PrescribedNonlinearProcess.process_map`, `PrescribedNonlinearFiniteHorizon.ae_unique_on_horizon`, `PrescribedNonlinearExit.measure_runningLyapunov_ge_le` |
| 5 | Lemmas 5.1–5.2, Prop 5.3, Thm 5.4 | `InitialCoupling.exists_initial_coupling`, `NonlinearParticleEmpirical.beta_tendsto_zero`, `PopulationCouplingExit.pairExit_probability_le_uniform`, `PopulationStoppedGronwall.nonlinear_expectedCost_le_factor`, `PopulationFocalApproximation.exists_full_synchronous_approximation` |
| 6 | Lemma 6.1, Prop 6.2, Thm 6.3, Cor 6.4 | `NonlinearVariationBounds.integral_variationReal_le`, `NonlinearVariationBounds.wasserstein_environment_le`, `NonlinearEmpiricalUniform.measure_runningError_gt_tendsto_zero`, `PopulationEmpiricalLimit.measure_runningError_gt_tendsto_zero`, `PopulationSkorokhodLimit.canonical_laws_tendsto`, `PopulationPathChaos.canonical_laws_tendsto`, `PopulationFixedTimeChaos.canonical_laws_tendsto` |
| 7, linear model | Prop 7.3, Cor 7.4, Prop 7.5 | `LinearCarryingCapacityHypotheses.dynamic_assumptions`, `LinearCarryingCapacityApplication.transport_limit`, `.vectorMean_limit`, `.focal_path_laws_tendsto`, `LinearMeanUniqueness.exists_solution_unique_on_nonnegative` |
| 7, quadratic model | Prop 7.7, Cor 7.8 | `QuadraticRealLyapunov.dynamic_assumptions`, `QuadraticFeedbackApplication.transport_limit`, `.secondMoment_limit`, `.focal_path_laws_tendsto`, `QuadraticMeanEquation.firstMean_equation` |

[docs/PAPER_MAP.md](docs/PAPER_MAP.md) maps every result in detail.

## Two probability settings

Most results are proved in two settings.

- **Canonical.** The repository builds its own driving noise on a product space
  with the initial data: one Poisson random measure on ℝ₊ × ℝ₊ with intensity
  `ds du` per particle and jump type, all independent. Its full Poisson law is
  proved (`MarkedFullPoissonLaw.countingMeasure_arrays_map`). Modules:
  `MarkedNoise`, `CommonInitialNoise`, `Configuration*`, `Population*`.
- **Prescribed** (`Prescribed*` modules). Any probability space carrying the
  initial configuration and Poisson random measures. The measures are specified
  by their law (`PoissonObservationLaw.HasDisjointLaws`) and their independence
  from the initial data. Processes are adapted to the completed right-continuous
  filtration (`UsualFiltration.filtration`). This is the paper's setting; the
  transfer from the canonical setting is proved, not assumed.

## Quantitative and supplied-space statements

- [`ModelCorollaries.corollary_7_4` and `.corollary_7_8`](CarryingCapacity/ModelCorollaries.lean)
  assemble the model conclusions on supplied independent Poisson measures.
  The quadratic corollary also states convergence of the empirical second moment.
- `LyapunovControl.drift` retains the supplied admissible constant as data.
  [`ExplicitLyapunovConstant`](CarryingCapacity/ExplicitLyapunovConstant.lean)
  proves the envelope (4.6)/(4.10) for any such constant, including for a nonlinear
  law originally constructed with a different admissible constant.
- [`PrescribedConfigurationExit.firstExit_probability_le`](CarryingCapacity/PrescribedConfigurationExit.lean)
  states (3.18) for the actual event `{τ_R ≤ T}` on the supplied space. The exit
  is AE measurable and agrees with the crossing event almost surely.
- [`PowerWassersteinUniform.measure_runningError_gt_tendsto_zero`](CarryingCapacity/PowerWassersteinUniform.lean)
  states Remark 2.8's uniform ordinary Wₚ convergence in probability for every
  real p > 1, with the supremum over time inside the probability.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
python3 scripts/check_proofs.py
python3 scripts/test_audit.py --expected-counts 4632 6096 354
```

`check_proofs.py` runs `lake build` and the axiom audit. Expected output:

```
Source policy passed for 354 modules.
Proof audit passed: 4632 theorems, 6096 safe declarations, 354 modules. Permitted axioms: propext, Classical.choice, Quot.sound.
All audit tests passed in …s; temporary fixtures removed.
```

The counts include auxiliary and compiler-generated declarations.

The toolchain is pinned: `lean-toolchain` selects Lean 4.19.0, and
`lake-manifest.json` locks Mathlib `v4.19.0`
(`c44e0c8ee63ca166450922a373c7409c5d26b00b`).

On recent macOS the compiled cache helper may fail to start (a `dyld` error).
Use the interpreted helper instead:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
```

### What the checks enforce

- `scripts/check_proofs.py` rejects `sorry`, `admit`, `axiom`, `unsafe`,
  `native_decide`, `implemented_by`, `extern`, and `debug.skipKernelTC` in
  source code. It also requires `CarryingCapacity.lean` to import every module.
- `Audit.lean` walks every compiled project declaration and fails if any depends
  on an axiom other than `propext`, `Classical.choice`, or `Quot.sound`.
- `scripts/test_audit.py` confirms that the audit rejects planted axioms and
  placeholder proofs.

CI runs all three on every push to `main` and every pull request
(`.github/workflows/lean.yml`), with the expected declaration counts pinned.

## Reading the Lean

| Paper | Lean |
|---|---|
| `E = ℕ₀ᴰ` | `State D` |
| κ with κ(0) = 0 and unit increments | `MomentScale` |
| `Kκ(x)` | `momentWeight κ x` |
| `ρκ(x, y)` | `adaptedDistance κ x y` |
| `Pκ(E)` | `MomentLaw κ D` |
| `Mκ(μ)` | `moment μ` |
| `Wκ(μ, ν)` | `wasserstein μ ν` |
| jump directions `H`, map `T_h` | `Jump D`, `Jump.advance` |
| rates `q_h(x, μ)`, generator `L_μ` | `Rates`, `Rates.generator` |
| `Cκ` (2.11), `Aκ` (2.13) | `couplingActivity`, `weightedActivity` |
| `Vᴺ(z) = N⁻¹ Σᵢ Ψ(zᵢ)` | `FiniteGenerator.empiricalMean Ψ z` |
| `D([0, T], S)` with the J1 metric | `SkorokhodJ1.Path`, `SkorokhodJ1.j1EDist` |

Results about a sequence of populations index the size as `n + 1`, so N ≥ 1.

## Layout

All modules live in `CarryingCapacity/`. Module names group by prefix:

| Prefix | Content |
|---|---|
| `MomentGeometry`, `Transport*`, `PowerWasserstein*`, `Empirical*` | State space, κ-moments, Wκ and Wₚ, empirical measures |
| `Framework`, `RateControl` | Jumps, rates, generators, assumption structures |
| `Marked*`, `Poisson*` | Construction and law of the Poisson noise |
| `Frozen*`, `Configuration*`, `Global*`, `TimeDependent*` | Frozen and global finite systems (§3) |
| `DeterministicEnvironment*`, `Nonlinear*`, `BieleckiFlowSpace` | Nonlinear process and fixed point (§4) |
| `Synchronous*`, `RandomEnvironment*`, `Population*` | Couplings (§4–5) |
| `Skorokhod*`, `CanonicalSkorokhodPaths` | J1 path space (§6) |
| `Prescribed*`, `Usual*` | Prescribed probability spaces and the usual filtration |
| `Linear*`, `Quadratic*`, `Models` | Section 7 models |
| `OriginalParticleSystem` | The DeWitt et al. finite system (below) |

## Relation to DeWitt et al. (2024)

The manuscript extends
[DeWitt, Evans, Hiesmayr, and Hummel (2024)](https://arxiv.org/html/2307.06010v2).
`OriginalParticleSystem` proves non-explosion and pathwise uniqueness of their
finite system under their own Assumption 2.1. Their Feller semigroup, Markov
empirical process, and mean-field theorem are not formalized; completing that
paper is not a goal of this repository.
