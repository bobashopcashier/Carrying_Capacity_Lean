# Lean formalization of carrying-capacity mean-field models

**Status: the numbered theorem package of Kenny Xie's specified manuscript is formalized.**
The target is *Mean-Field Limits for Multitype Birth–Death Systems with
Unbounded Moment Feedback*
([manuscript source](https://github.com/bobashopcashier/Carrying_Capacity_fixed/blob/c7688113e4a92910b6403fdd8ecb14fb0f3ce6a9/new.tex)). The checked results include
strong construction on specified Poisson measures, frozen compatibility and
nonexplosion, nonlinear well-posedness, uniform empirical and moment convergence,
fixed-time and J1 path-space chaos, the real-power Wp comparisons, and the
carrying-capacity models and closed mean ODE.
The general stopped comparison lemma is also proved for arbitrary adapted
càdlàg environments. Its finite-state real expectation bound follows from
ordinary rate integrability; no weighted comparison estimate is assumed.
The source-by-source inventory is in [PAPER_MAP.md](docs/PAPER_MAP.md).
Existing results for
[DeWitt, Evans, Hiesmayr, and Hummel (2024)](https://arxiv.org/html/2307.06010v2)
are retained as shared infrastructure and separately documented coverage;
completing that original paper is not the current target.
The unproved conclusions are neither axioms nor hidden
fields of a structure in this project.

The canonical coupled systems now satisfy Proposition 5.3's uniform exit and
stopped comparison estimates, with vanishing stopped expectation. All three
canonical comparison conclusions of Theorem 5.4 are assembled under the
manuscript's original initialization assumptions: averaged path discrepancy,
uniform empirical transport discrepancy between the paired systems, and every
fixed-focal path discrepancy tend to zero in probability. Actual initial/noise
relabeling proves the coordinate symmetry used in the last conclusion.
Section 6's expected jump-variation estimate, uniform independent empirical
limit, and uniform interacting empirical and generalized-moment limits are
proved. Exact initial-record projection gives these conclusions for the canonical
system with the original initial vector law. Every fixed finite particle vector
converges weakly at each fixed time to the product nonlinear law. Genuine
Borel AE-measurable path maps now also give empirical weak convergence to the
Dirac law of the nonlinear curve and chaos in one vector-valued J1 space,
where all coordinates share a single time change.

Actual pathwise horizon consistency now gives one all-time canonical nonlinear
process, its own-marginal counting equation, and a unique global weak law in the
locally Lyapunov-moment-bounded class. Finite-activity grid approximations
converge in the genuine Skorokhod J1 metric and prove the actual random path
maps Borel AE measurable. The path-law limits retain the original initial
vector law and the canonical driving noise.

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
python3 scripts/test_audit.py
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

The complete repository-wide build passed without warnings, and its exhaustive
audit checked
**4,579 theorem declarations and 5,992 safe declarations across 349 modules**.
These counts include private helpers and compiler-generated declarations;
they are not counts of distinct results from the papers. The counts include the
prescribed-space, real-power transport, model and mean-equation modules. Separate negative
checks confirmed that the audit rejects
custom project axioms, both public and private placeholder proofs, and a
forbidden dependency imported transitively through a safe definition. The
audit retains the upstream Lean axiom traversal state across declarations,
avoiding repeated traversal of shared dependencies. Temporary fixture tests
check the rejection behavior without adding invalid proofs to project sources.

## What is formalized

| File | Checked content | Boundary |
|---|---|---|
| [MomentGeometry](CarryingCapacity/MomentGeometry.lean) | Discrete κ scales; genuine adapted state metric; weight and ℓ¹ bounds; finite moment and Lyapunov sublevels | Does not prove probability-space completeness or Wasserstein–Orlicz results |
| [RealPowerMoment](CarryingCapacity/RealPowerMoment.lean), [RealPowerIntegrals](CarryingCapacity/RealPowerIntegrals.lean), [PowerWasserstein](CarryingCapacity/PowerWasserstein.lean), [PowerWassersteinMetric](CarryingCapacity/PowerWassersteinMetric.lean), [PowerWassersteinTopology](CarryingCapacity/PowerWassersteinTopology.lean) | Genuine ordinary Wp coupling metric for every real p>1; both exact comparison inequalities; moment convergence derived from Wp convergence; equality of the two metric topologies | Completes Remark 2.1; no Wasserstein–Orlicz extension is asserted |
| [CoordinateMoments](CarryingCapacity/CoordinateMoments.lean), [PopulationCoordinateMoments](CarryingCapacity/PopulationCoordinateMoments.lean) | The l1 distance between vectors of κ moments is bounded by actual Wκ; measurable running vector error and uniform convergence under the manuscript initialization | Gives every type mean simultaneously for linear κ; the closed mean ODE is separate |
| [UsualFiltration](CarryingCapacity/UsualFiltration.lean), [CanonicalUsualFiltration](CarryingCapacity/CanonicalUsualFiltration.lean) | Minimal completed right-continuous augmentation of the actual history; completeness of the restricted law; actual particle, driven and nonlinear paths adapted there; exact localization exits are stopping times | Canonical histories; arbitrary supplied inputs require the transfer below |
| [MarkedNoiseReconstruction](CarryingCapacity/MarkedNoiseReconstruction.lean), [MarkedNoiseObservation](CarryingCapacity/MarkedNoiseObservation.lean), [MarkedPastReconstruction](CarryingCapacity/MarkedPastReconstruction.lean), [CountingMeasureStrongFunction](CarryingCapacity/CountingMeasureStrongFunction.lean) | Measurable recovery of canonical noise from its actual counts; a separate past-only decoder; exact equality of completed count and indexed histories; entire paths are measurable functions of initial data and actual measures | Reconstruction is derived on probability-one events; no extra random input or assumed decoder identity |
| [PoissonObservationLaw](CarryingCapacity/PoissonObservationLaw.lean) | Standard independent Poisson count laws determine the entire countable observation law, via disjoint Boolean atoms and finite-cylinder uniqueness | Supplies the law bridge for prescribed-noise realization; path properties and adaptation need separate transfer |
| [PrescribedPoissonRealization](CarryingCapacity/PrescribedPoissonRealization.lean), [PrescribedPoissonFiltration](CarryingCapacity/PrescribedPoissonFiltration.lean), [PrescribedJumpProcess](CarryingCapacity/PrescribedJumpProcess.lean) | Supplied PRMs reconstruct the exact original initial/noise product law; actual natural count filtration and usual augmentation; measurable strong paths, nonexplosion, left limits, supplied-measure counting equations and pathwise uniqueness | Global construction; explicit frozen-level/exit and usual-martingale consumers are supplied by the modules below |
| [PrescribedConfigurationProcess](CarryingCapacity/PrescribedConfigurationProcess.lean), [PrescribedNonlinearProcess](CarryingCapacity/PrescribedNonlinearProcess.lean) | Concrete interacting and nonlinear strong processes on the supplied space; exact empirical/own-marginal equations, usual-natural adaptedness, finite activity and pathwise uniqueness | Nonlinear equation fixes the proved limiting law curve, as in Corollary 4.4; exact finite-horizon uniqueness is supplied below |
| [PrescribedConfigurationLocalization](CarryingCapacity/PrescribedConfigurationLocalization.lean), [PrescribedConfigurationFrozenEquation](CarryingCapacity/PrescribedConfigurationFrozenEquation.lean), [PrescribedConfigurationCompatibility](CarryingCapacity/PrescribedConfigurationCompatibility.lean) | Actual supplied frozen paths, finite enlargement, natural-history stopping times, true exit attainment and stopped compatibility including the exit jump; stopped moments, reciprocal exits, exhaustion and global patch agreement | The path is confined to the finite enlargement when initially active; otherwise it stays at its actual initial state |
| [PrescribedConfigurationEstimates](CarryingCapacity/PrescribedConfigurationEstimates.lean) | Exact empirical weighted and total activity before the genuine exit; global integrability; actual all-real running-supremum measurability and tail; literal population/horizon suprema of Corollary 3.6 | Constants depend on model and horizon, not population size or initial law; only the manuscript initial moment bound is used |
| [UsualMartingale](CarryingCapacity/UsualMartingale.lean), [ConfigurationUsualMartingale](CarryingCapacity/ConfigurationUsualMartingale.lean), [PrescribedMartingale](CarryingCapacity/PrescribedMartingale.lean), [PrescribedConfigurationMartingale](CarryingCapacity/PrescribedConfigurationMartingale.lean) | Genuine generator martingale in the supplied completed right-continuous natural filtration; reverse causal event pullback and dominated right-limit argument | Finite-support test functions; the actual time-dependent supplied realization uses the manuscript initial moment |
| [PrescribedConfigurationExchangeability](CarryingCapacity/PrescribedConfigurationExchangeability.lean) | Actual initial/noise relabeling and separate coordinate-equation uniqueness prove supplied-system exchangeability at every nonnegative time | Exchangeable initial law and independent standard labelled PRMs |
| [PrescribedDeterministicEnvironment](CarryingCapacity/PrescribedDeterministicEnvironment.lean), [PrescribedNonlinearExit](CarryingCapacity/PrescribedNonlinearExit.lean), [PrescribedNonlinearFiniteHorizon](CarryingCapacity/PrescribedNonlinearFiniteHorizon.lean) | Full prescribed deterministic-environment realization and forward uniqueness; nonlinear whole-horizon Lyapunov tail; uniqueness using competing equations only on the stated finite horizon | Deterministic environments are held at the endpoint after the selected horizon, exactly as in the manuscript |
| [IndependenceLimit](CarryingCapacity/IndependenceLimit.lean), [UsualPoissonIndependence](CarryingCapacity/UsualPoissonIndependence.lean), [PrescribedCountingKernel](CarryingCapacity/PrescribedCountingKernel.lean) | Future rectangle-count independence in the usual natural filtration, actual s-finite counting kernel and predictable compensation for supplied PRMs | Derived from genuine Poisson laws and initial independence; no compensator assumption |
| [RightContinuousProcessMeasurability](CarryingCapacity/RightContinuousProcessMeasurability.lean), [StoppedComparisonLocalization](CarryingCapacity/StoppedComparisonLocalization.lean) | Joint measurable versions from right-grid observations, simultaneous path agreement, actual stopped-supremum measurability; Fatou removal of exhausting localization and derived real integrability | Generic analytic ingredients; the separate thinning equations are discharged in `PrescribedRandomEnvironmentComparison` |
| [PrescribedObservableLaws](CarryingCapacity/PrescribedObservableLaws.lean), [PrescribedPopulationLimits](CarryingCapacity/PrescribedPopulationLimits.lean), [PrescribedPathLimits](CarryingCapacity/PrescribedPathLimits.lean) | Exact laws of AE-measurable observables; uniform empirical, scalar-moment and vector-moment convergence on the supplied space; actual empirical and focal J1 path maps and limiting laws | The record and output laws are proved from genuine PRM laws and initial independence, not assumed |
| [PredictableStoppingMask](CarryingCapacity/PredictableStoppingMask.lean), [IndependentIncrementCompensation](CarryingCapacity/IndependentIncrementCompensation.lean) | Inclusive arbitrary-stopping-time mask is predictable; full nonnegative predictable compensation on any filtered space derived from unweighted intensity and independent future counts | Compensation ingredients; the full arbitrary-environment comparison is supplied below |
| [CadlagRateRegularity](CarryingCapacity/CadlagRateRegularity.lean), [CadlagCompactBounds](CarryingCapacity/CadlagCompactBounds.lean), [CadlagFiniteRange](CarryingCapacity/CadlagFiniteRange.lean), [FiniteHorizonCountingUniqueness](CarryingCapacity/FiniteHorizonCountingUniqueness.lean) | Rate observables agree with genuine left limits almost everywhere; compact-time rate bounds and finite discrete ranges; candidate uniqueness from separate coordinate equations only through the chosen horizon | Environments may have infinitely many jumps; no assumed finite activity |
| [UniversalFrozenNoise](CarryingCapacity/UniversalFrozenNoise.lean), [UniversalThinningComparison](CarryingCapacity/UniversalThinningComparison.lean), [UniversalStoppedComparison](CarryingCapacity/UniversalStoppedComparison.lean), [RandomEnvironmentPathwise](CarryingCapacity/RandomEnvironmentPathwise.lean) | One full noise event supports every later coefficient/path choice; candidate equations imply the true stopped running-supremum positive-increment bound, including the stopping jump | Finite sets and rate caps are derived samplewise from càdlàg paths |
| [RandomEnvironmentCompensation](CarryingCapacity/RandomEnvironmentCompensation.lean), [RateTableCompensation](CarryingCapacity/RateTableCompensation.lean), [RateTableSumCompensation](CarryingCapacity/RateTableSumCompensation.lean), [RandomEnvironmentComparison](CarryingCapacity/RandomEnvironmentComparison.lean) | Predictable left versions, exact three-region compensation, measurable stopped suprema and their full expected comparison | Countable scalar-rate tables avoid an extra Polish assumption on the environment law space |
| [PrescribedRandomEnvironmentCompensation](CarryingCapacity/PrescribedRandomEnvironmentCompensation.lean), [RandomEnvironmentActivityIntegral](CarryingCapacity/RandomEnvironmentActivityIntegral.lean), [FiniteStateActivityIntegrability](CarryingCapacity/FiniteStateActivityIntegrability.lean), [PrescribedRandomEnvironmentComparison](CarryingCapacity/PrescribedRandomEnvironmentComparison.lean) | Full Lemma 4.1 on the specified Poisson space, exact κ distance and coupling activity; ordinary real expectation and derived integrability; finite-state case follows from ordinary rates | No compensator, paired-equation or stochastic-comparison premise; no finite-state restriction in the general finite-RHS result |
| [PrescribedFixedTimeChaos](CarryingCapacity/PrescribedFixedTimeChaos.lean) | Exact first-k vector law of the supplied finite system and its weak convergence to the product nonlinear marginal | Corollary 6.4 uses the original initialization assumptions and actual supplied inputs |
| [LinearCoordinateApproximation](CarryingCapacity/LinearCoordinateApproximation.lean), [LinearCoordinateForward](CarryingCapacity/LinearCoordinateForward.lean), [LinearMeanGenerator](CarryingCapacity/LinearMeanGenerator.lean), [LinearMeanEquation](CarryingCapacity/LinearMeanEquation.lean), [LinearMeanLipschitz](CarryingCapacity/LinearMeanLipschitz.lean), [LinearMeanUniqueness](CarryingCapacity/LinearMeanUniqueness.lean) | Finite-support coordinate approximation and activity-dominated state/time limits justify the true mean equation; exact birth/death/mutation drift; actual global nonnegative solution; local Lipschitz bounds and compact-time Gronwall prove uniqueness | Completes Proposition 7.5's ODE conclusion without assuming bounded candidate means or an unbounded-test equation |
| [AdaptedCoordinateForward](CarryingCapacity/AdaptedCoordinateForward.lean), [QuadraticMeanEquation](CarryingCapacity/QuadraticMeanEquation.lean) | Ordinary coordinate tests justified for general normalized κ by actual adapted activity; quadratic-feedback first-mean integral and differential equations, genuine time integrability and right derivative at zero | The quadratic first mean retains second-moment feedback; no autonomous first-mean closure is asserted |
| [LinearCarryingCapacity](CarryingCapacity/LinearCarryingCapacity.lean), [LinearCarryingCapacityBounds](CarryingCapacity/LinearCarryingCapacityBounds.lean), [LinearJumpGeometry](CarryingCapacity/LinearJumpGeometry.lean), [LinearCarryingCapacityHypotheses](CarryingCapacity/LinearCarryingCapacityHypotheses.lean), [LinearCarryingCapacityApplication](CarryingCapacity/LinearCarryingCapacityApplication.lean) | Exact multitype vector-mean mortality and mutation rates; full activity/coupling bounds; Lyapunov powers for every real p>1; canonical nonexplosion, nonlinear uniqueness, uniform empirical and vector-mean convergence, and J1 chaos | Proposition 7.3 and the canonical Corollary 7.4 application; Proposition 7.5's closed ODE remains separate |
| [RealPowerLyapunov](CarryingCapacity/RealPowerLyapunov.lean), [QuadraticRealLyapunov](CarryingCapacity/QuadraticRealLyapunov.lean), [QuadraticFeedbackApplication](CarryingCapacity/QuadraticFeedbackApplication.lean) | Quadratic-feedback Lyapunov verification for every real r>2; canonical nonexplosion, nonlinear uniqueness, uniform empirical/second-moment convergence and J1 chaos | Proposition 7.7 and the canonical Corollary 7.8 application; prescribed-space transfer remains separate |
| [Transport](CarryingCapacity/Transport.lean) | Actual probability laws with integrable κ weight; actual marginal couplings; finite coupling costs; infimum transport cost, symmetry and zero self-distance; `\|Mκ(μ)−Mκ(ν)\| ≤ Wκ(μ,ν)` and consequent moment convergence | The metric, completeness, and empirical LLN results are supplied by the modules below; general optimal-plan existence remains separate |
| [TransportMetric](CarryingCapacity/TransportMetric.lean) | Actual disintegration-based gluing; triangle inequality; separation by measurable events; a genuine `MetricSpace`; Lipschitz moment map | Does not assert existence of an optimal coupling for every pair of laws |
| [TransportCompleteness](CarryingCapacity/TransportCompleteness.lean) | Infinite simultaneous coupling through Ionescu–Tulcea; constructed finite-moment limit law; transport tail estimate; genuine `CompleteSpace` instance | Nonlinear process construction remains separate |
| [LyapunovFlowSpace](CarryingCapacity/LyapunovFlowSpace.lean) | Lower semicontinuity of genuine extended Lyapunov moments; closed complete moment sublevels and continuous-curve spaces; nonempty complete manuscript space with its exponential envelope | The actual invariant evolution, fixed point and full moment-bounded forward-law uniqueness are supplied below |
| [BieleckiFlowSpace](CarryingCapacity/BieleckiFlowSpace.lean) | Exact exponentially weighted supremum metric, uniform equivalence, and completeness; Volterra integration gives contraction factor A/(λ−A); conditional unique fixed point for λ>2A | The actual stochastic estimate and application to the constructed evolution are supplied below |
| [EmpiricalMeasure](CarryingCapacity/EmpiricalMeasure.lean) | Genuine finite empirical probability laws; exact integral identities; paired and permuted transport couplings; single-update estimate; generator bridge | Exact optimal matching is a separate result |
| [EmpiricalMatching](CarryingCapacity/EmpiricalMatching.lean) | Splits arbitrary couplings across repeated particle labels; Birkhoff decomposition; exact attained permutation optimum; measurable optimal matching preserving the empirical law | Randomized exchangeable initialization is supplied by `ExchangeableMatching` |
| [FiniteTransport](CarryingCapacity/FiniteTransport.lean) | Explicit common-mass coupling; transport bounded by diameter times total variation on a common finite support; atomic convergence implies transport convergence | Both laws must be concentrated on the same finite set |
| [EmpiricalLLN](CarryingCapacity/EmpiricalLLN.lean) | Full almost-sure Wκ convergence of empirical laws from measurable pairwise independent samples with a common finite-moment law; scalar, tail, and truncated strong laws | A fixed-law sampling theorem; uniform convergence of stochastic paths remains separate |
| [EmpiricalMeanError](CarryingCapacity/EmpiricalMeanError.lean) | Derived empirical Lyapunov expectations and uniform integrability; expected Wκ error tends to zero; error ≤2Mκ; time-integrated convergence under a uniform Lyapunov bound | The time theorem assumes jointly measurable samples and a continuous law curve; it does not construct the nonlinear process |
| [EmpiricalArrayError](CarryingCapacity/EmpiricalArrayError.lean) | Exact iid finite-vector laws; transfer of expected and time-integrated empirical transport convergence to N-dependent arrays, even on different probability spaces | Requires independence within each row at each fixed time; no independence across rows or times is imposed |
| [IndependentArrayLLN](CarryingCapacity/IndependentArrayLLN.lean) | Canonical iid strong law and exact finite-vector law transfer prove centered empirical-mean probability limits for any integrable real observable, on varying row spaces | Requires the observable's genuine integrability and each row's exact product law; no compatibility across population sizes. Actual interval variations satisfy these premises below |
| [EmpiricalTimeGrid](CarryingCapacity/EmpiricalTimeGrid.lean) | Actual empirical pairing and the Wasserstein triangle inequality give cell and all-real supremum bounds on a finite grid; exact equally spaced mesh identities | Deterministic bridge; the actual variation estimates and stochastic application are supplied below |
| [RightContinuousSupremum](CarryingCapacity/RightContinuousSupremum.lean) | Right continuity identifies the true time supremum with rational observations plus the terminal value; derives AE measurability from measurable evaluations | Unlike local-constancy lemmas, permits a continuously varying target law; no uniform convergence conclusion |
| [NonlinearEmpiricalSupremum](CarryingCapacity/NonlinearEmpiricalSupremum.lean) | The actual independent empirical error is right continuous on one full-probability event; its uncountable running supremum has a countable observation representation and is AE measurable | Derives regularity from actual particle paths and the continuous nonlinear law; uniform convergence is supplied below |
| [NonlinearActivityBound](CarryingCapacity/NonlinearActivityBound.lean), [NonlinearPathVariation](CarryingCapacity/NonlinearPathVariation.lean) | Actual accepted weighted jump variation, predictable integrands, measurable variation and exact compensation; the genuine nonlinear marginals and moment envelope bound expected current activity | No expected variation or integrability assumption; the finite interval estimate is supplied below |
| [NonlinearVariationDisplacement](CarryingCapacity/NonlinearVariationDisplacement.lean), [NonlinearVariationBounds](CarryingCapacity/NonlinearVariationBounds.lean) | One event gives all-time displacement domination by actual accepted variation; finite expected variation, real integrability and the exact linear Wasserstein time modulus follow | Lemma 6.1's estimates for the actual canonical process on the selected horizon, including right-endpoint jumps |
| [NonlinearEmpiricalUniform](CarryingCapacity/NonlinearEmpiricalUniform.lean) | Exact iid record laws and integrable cell variations yield finite-grid probability limits, then uniform independent empirical convergence to the nonlinear law over every real time in the horizon | Proposition 6.2; genuine stochastic estimates are derived, and no across-row or across-time independence is assumed. Interacting empirical convergence is supplied by `PopulationEmpiricalLimit`; the J1 path-law conclusions are supplied below |
| [ExchangeableMatching](CarryingCapacity/ExchangeableMatching.lean) | Independent uniform common permutation of optimally matched arrays; exact preservation of both full vector laws; joint exchangeability; optimal cost and expectation identities; iid comparison specialization | Expected-error convergence is connected through explicit empirical-error hypotheses; interacting-particle versus nonlinear process comparison remains separate |
| [InitialCoupling](CarryingCapacity/InitialCoupling.lean) | Full initial-coupling lemma: jointly exchangeable pairs with exact original and iid vector marginals, optimal integrable cost, and vanishing expected pairing cost, derived from convergence in probability and the expected empirical Lyapunov bound | Constructs initial joint laws; comparison of the interacting particles with independent nonlinear trajectories remains separate |
| [Symmetrization](CarryingCapacity/Symmetrization.lean), [EmpiricalGenerator](CarryingCapacity/EmpiricalGenerator.lean) | Permutation equivariance; empirical equality iff relabeling; actual exchangeable symmetrization kernel; deterministic empirical state under that kernel; well-defined quotient generator and intertwining identity | Does not prove process exchangeability, the Markov mapping theorem, or Feller generation |
| [LyapunovTails](CarryingCapacity/LyapunovTails.lean) | Superlinear Lyapunov control gives uniform moment tails; genuine uniform integrability of empirical transport errors; in-probability initialization upgrades to expected-error convergence | Uses a common probability space and genuine integrability; does not supply the initial in-probability convergence assumption |
| [Framework](CarryingCapacity/Framework.lean) | Multitype birth/death/mutation maps; invalid-jump convention; generator linearity; distinct original TV and extended moment assumptions | Assumption structures record hypotheses; they are not the main theorems |
| [OriginalParticleSystem](CarryingCapacity/OriginalParticleSystem.lean) | Actual empirical probability rates under the original assumptions; finite total-population sublevels and affine drift; arbitrary-initial nonexplosive particle process, càdlàg paths, finite activity, counting equations and coordinate-equation pathwise uniqueness | No moment-law restriction or extension LyapunovControl; Feller generation, Markov identification and the original mean-field theorem remain separate |
| [DeterministicEnvironmentRates](CarryingCapacity/DeterministicEnvironmentRates.lean) | The diagonal coupling bound derives fixed-state rate Lipschitz continuity in Wκ; measurable rates along continuous or endpoint-clamped law curves; activity derives finite-active-set rate bounds on compact horizons | Supplies actual coefficient hypotheses; does not construct the nonlinear law curve |
| [DeterministicEnvironmentFrozen](CarryingCapacity/DeterministicEnvironmentFrozen.lean) | Actual endpoint-clamped frozen environment path with a derived positive rate cap; joint/raw-history measurability, càdlàg paths, counting identity, Dynkin change formula and generator martingale; exact original-environment drift up to the selected horizon | Coupling/activity assumptions and a continuous law curve discharge every rate premise; this is the finite-active-set construction used by the global result below |
| [DeterministicEnvironmentLyapunov](CarryingCapacity/DeterministicEnvironmentLyapunov.lean), [DeterministicEnvironmentProcess](CarryingCapacity/DeterministicEnvironmentProcess.lean) | Paper hypotheses derive uniform spatial rate caps, affine and time-dependent Lyapunov drift; actual global prescribed-environment path, initial law, joint measurability, raw adaptedness, exhaustion, càdlàg regularity, finite activity, moments, counting equations and coordinate-equation pathwise uniqueness | Genuine environment Lyapunov bounds and an integrable initial Lyapunov value support nonexplosion; the manuscript curve supplies them. Original rates hold through the selected horizon; all-time statements use the clamped environment |
| [DeterministicEnvironmentEnvelope](CarryingCapacity/DeterministicEnvironmentEnvelope.lean), [DeterministicEnvironmentLaw](CarryingCapacity/DeterministicEnvironmentLaw.lean) | Exact manuscript exponential envelope for the actual process and its marginal laws, in ordinary and extended moments; actual pushforward output MomentLaw with finite adapted moment, exact initial law and integral identities | Supplies genuine laws and the moment component of invariance; transport continuity and the complete self-map are supplied below |
| [TimeDependentStochasticContinuity](CarryingCapacity/TimeDependentStochasticContinuity.lean), [LawCurveContinuity](CarryingCapacity/LawCurveContinuity.lean), [DeterministicEnvironmentEvolution](CarryingCapacity/DeterministicEnvironmentEvolution.lean) | Nonatomic proposal times give almost-sure continuity at each fixed time; actual joint couplings and superlinear uniform integrability give Wκ-continuous marginals; the actual prescribed-environment evolution preserves the complete manuscript curve space | Fixed-time null events may differ with time; no continuous-sample-path claim. Stochastic contraction, fixed-point realization and prescribed-environment forward-law uniqueness are supplied below |
| [SynchronousPositiveIncrement](CarryingCapacity/SynchronousPositiveIncrement.lean), [SynchronousFrozenCounting](CarryingCapacity/SynchronousFrozenCounting.lean), [SynchronousGlobalCounting](CarryingCapacity/SynchronousGlobalCounting.lean) | Exact shared-height positive increments and three-region height activity, including simultaneous jumps; paired actual recursions on a common chronological list; cutoff-free pathwise distance domination on every prefix of a horizon | The generic global result uses exhaustion of the two genuine exit sequences; no pathwise coupling inequality is assumed |
| [TimeDependentGlobalPreStateTime](CarryingCapacity/TimeDependentGlobalPreStateTime.lean), [SynchronousCompensation](CarryingCapacity/SynchronousCompensation.lean) | Actual pre-states equal current states at almost every time; predictable positive coupled increments; exact nonnegative compensation and integrated height activity; actual extended expected-distance inequality | Allows infinite expectations; no finite expected activity or expected coupling inequality is an input |
| [CouplingExpectation](CarryingCapacity/CouplingExpectation.lean), [CoupledDistanceContinuity](CarryingCapacity/CoupledDistanceContinuity.lean), [DeterministicEnvironmentCoupling](CarryingCapacity/DeterministicEnvironmentCoupling.lean) | Genuine integrability of coupled distance and activity; exact coefficient L(1+2K(T)) from the paper assumptions; continuity of the actual expected distance via superlinear uniform integrability; actual output-law coupling | Applies to the existing processes on their common initial-record/noise space; no assumed expected continuity or stochastic estimate |
| [VolterraGronwall](CarryingCapacity/VolterraGronwall.lean), [DeterministicEnvironmentVolterra](CarryingCapacity/DeterministicEnvironmentVolterra.lean) | Explicit forced Gronwall convolution; actual compensation yields the finite real integral inequality; fixed-time expected-distance and output-law Volterra bounds | Supplies the precise bound required by Bielecki contraction; running-supremum control is supplied separately below |
| [SynchronousRunningSupremum](CarryingCapacity/SynchronousRunningSupremum.lean) | Actual supremum over every time in a horizon equals rational-plus-terminal observations almost surely; AE measurability and extended expected-supremum bound from actual compensation | Genuine exit exhaustion derives right-local constancy; the generic estimate permits infinite expectations |
| [DeterministicEnvironmentRunningSupremum](CarryingCapacity/DeterministicEnvironmentRunningSupremum.lean) | The manuscript's exact exponential convolution bounds the expected supremum of the actual shared-noise path distance over every real time in [0,t]; finite expectation, almost-sure finiteness and integrability of the real version are derived | Original coupling, activity and Lyapunov hypotheses on the chosen horizon; no supplied supremum measurability, integrability or stochastic estimate |
| [NonlinearFixedPoint](CarryingCapacity/NonlinearFixedPoint.lean) | Actual evolution has exactly one fixed curve in the complete manuscript space, using Bielecki weight 2A+1; canonical realized process is measurable, adapted, nonexplosive and càdlàg, has exactly those marginals and the moment envelope, and solves its own-marginal counting equation | Genuine finite initial Ψ moment; self-consistency is proved on the selected [0,T]. The environment is held at its endpoint afterward; full moment-bounded law uniqueness and law consistency across horizons are supplied below; arbitrary external PRM realization remains separate |
| [FiniteJumpForward](CarryingCapacity/FiniteJumpForward.lean) | Probability-valued weak forward solutions with explicit genuine tested time integrability; finite-test and atomic continuity derived from the equation; finite jump fibers give finite generator influence | Defines the candidate solution class without assuming uniqueness, a moment bound, a Markov property, or a law-identification conclusion |
| [TimeDependentFrozenForward](CarryingCapacity/TimeDependentFrozenForward.lean), [DeterministicEnvironmentFrozenForward](CarryingCapacity/DeterministicEnvironmentFrozenForward.lean) | Actual frozen singleton masses, probability bounds and continuity; finite forward system derived from Dynkin/Fubini; exact outgoing leakage and self-jump cancellation; manuscript coefficients and uniform caps | Targets inside the active set form a finite system; exiting mass stays frozen outside it |
| [FiniteForwardComparison](CarryingCapacity/FiniteForwardComparison.lean), [FiniteJumpRestriction](CarryingCapacity/FiniteJumpRestriction.lean), [FrozenForwardMinimality](CarryingCapacity/FrozenForwardMinimality.lean) | Comparison from genuine integrated finite systems; finite restriction of any weak law has derived nonnegative external inflow; each actual frozen mass is bounded by the competing law inside the active set | Uses all-subinterval identities derived from equality, not a one-sided time-zero inequality; no minimality assumption |
| [TimeDependentFrozenLawLimit](CarryingCapacity/TimeDependentFrozenLawLimit.lean), [TimeDependentForwardUniqueness](CarryingCapacity/TimeDependentForwardUniqueness.lean) | Actual exit exhaustion gives frozen singleton-mass convergence by bounded convergence; atomic domination and probability normalization identify the global law with every weak solution | Generic theorem assumes genuine construction exhaustion, finite jump fibers and continuous coefficients; the paper specialization below discharges these |
| [DeterministicEnvironmentFiniteSupport](CarryingCapacity/DeterministicEnvironmentFiniteSupport.lean), [DeterministicEnvironmentForward](CarryingCapacity/DeterministicEnvironmentForward.lean) | Actual finite predecessor support bounds every nonzero global increment; signed compensation and product Fubini prove the untruncated finite-support weak forward equation; the canonical nonlinear fixed curve satisfies its own-law weak equation | All tested drift integrability is proved; original coefficients and nonlinear self-consistency are identified on the selected [0,T] |
| [DeterministicEnvironmentGeneralForward](CarryingCapacity/DeterministicEnvironmentGeneralForward.lean) | Actual original-rate weak forward existence for any prescribed Wκ-continuous environment with a uniform genuine Ψ bound; finite-support compensation and Fubini use the existing global process | Requires finite initial Ψ moment; no ManuscriptCurves premise or v(0)=ν restriction. General output-law Wκ continuity is supplied below |
| [DeterministicEnvironmentForwardUniqueness](CarryingCapacity/DeterministicEnvironmentForwardUniqueness.lean) | Actual general prescribed-environment existence and linear uniqueness on [0,T] against every probability-valued weak solution, without candidate moments; actual nonlinear weak-solution uniqueness within ManuscriptCurves via linear law identification and the proved fixed point | The prescribed curve is Wκ-continuous with uniformly bounded genuine Ψ moment, and the initial Ψ moment is finite; full nonlinear uniqueness is supplied below |
| [DeterministicEnvironmentGeneralLaw](CarryingCapacity/DeterministicEnvironmentGeneralLaw.lean) | Actual pushforward MomentLaw for every continuous prescribed environment with uniformly bounded genuine Ψ moment; exact initial law, derived affine-exponential moment bounds and Wκ-continuous output curve | Finite initial Ψ moment; no v(0)=ν restriction. The realization remains on the canonical initial-record/noise product |
| [AtomicTransportContinuity](CarryingCapacity/AtomicTransportContinuity.lean) | Exact finite-truncation atom identities, including the collapsed zero atom; uniform superlinear tails give Wκ convergence from atomic convergence; every moment-bounded weak solution is automatically Wκ-continuous | Genuine extended Ψ bound and tested time integrability; candidate continuity is derived |
| [DeterministicEnvironmentGeneralCoupling](CarryingCapacity/DeterministicEnvironmentGeneralCoupling.lean), [NonlinearForwardUniqueness](CarryingCapacity/NonlinearForwardUniqueness.lean) | Linear identification realizes arbitrary moment-bounded nonlinear candidates; actual shared-noise compensation, finite integral bounds and Gronwall prove full-class law uniqueness; actual existence, exact envelope and unique existence on [0,T] | Requires the paper's coupling/activity/Lyapunov hypotheses and finite initial Ψ moment; no candidate continuity or manuscript-envelope premise. This proves Theorem 4.3's law well-posedness |
| [FiniteJumpForwardRestriction](CarryingCapacity/FiniteJumpForwardRestriction.lean), [NonlinearHorizonConsistency](CarryingCapacity/NonlinearHorizonConsistency.lean) | Restriction and coefficient/law congruence preserve genuine tested integrability; larger fixed curves restrict exactly to smaller fixed curves; actual environments and process marginal laws agree on overlapping horizons | This module proves law consistency; actual pathwise consistency and the all-time realization are supplied below |
| [TimeDependentLocalUniqueness](CarryingCapacity/TimeDependentLocalUniqueness.lean) | Same-input counting equations with locally equal rates and genuine left limits give path equality through the terminal time | Generic candidate equations and regularity are explicit; the nonlinear construction supplies them below |
| [NonlinearPathConsistency](CarryingCapacity/NonlinearPathConsistency.lean) | Actual nonlinear paths agree on overlapping horizons, including endpoints; one event gives compatibility of all integer horizons | Uses the same initial record and original noise, without assuming path compatibility |
| [NonlinearGlobalProcess](CarryingCapacity/NonlinearGlobalProcess.lean) | One jointly measurable, raw-adapted, càdlàg nonlinear process for all nonnegative times; actual marginal law, Wκ continuity, exact moment envelope and finite-horizon agreement | Canonical initial/noise space; arbitrary external PRM realization and usual filtration remain separate |
| [NonlinearGlobalCounting](CarryingCapacity/NonlinearGlobalCounting.lean) | Genuine predictable left state; own-marginal counting equation and pathwise test-increment integrability on every horizon; correct initial state, finite activity and actual localization exhaustion | Each fixed test has one event for all horizons; no unbounded-test expectation or martingale is inferred |
| [NonlinearGlobalForward](CarryingCapacity/NonlinearGlobalForward.lean) | Actual global weak-law existence and uniqueness under genuine local Lyapunov bounds; candidate transport continuity and exact envelope are derived | Finite-support tested equations include genuine time integrability; negative-time extensions are not identified |
| [ParticleNoiseProjection](CarryingCapacity/ParticleNoiseProjection.lean), [ParticleInputRecords](CarryingCapacity/ParticleInputRecords.lean) | Exact full product law of particle initial/noise records; mutual independence; pointwise projected counting-measure identity; measurability in the raw shared history | Initial coordinates have the prescribed iid vector marginal; the rest of the paired initial record is unrestricted |
| [NonlinearParticleArray](CarryingCapacity/NonlinearParticleArray.lean), [NonlinearParticleContinuation](CarryingCapacity/NonlinearParticleContinuation.lean) | Actual independent nonlinear trajectories on the shared particle-noise space; full product marginals, raw adaptedness, simultaneous càdlàg and left-limit properties, actual initial values, integrable increments and all-horizon counting equations | These modules establish coordinate-sigma-algebra independence; `NonlinearSkorokhodArray` below supplies actual J1 path independence. The environment is endpoint-held after T |
| [CompactIntervalIntegration](CarryingCapacity/CompactIntervalIntegration.lean), [NonlinearParticleEmpirical](CarryingCapacity/NonlinearParticleEmpirical.lean) | Actual expected empirical error is genuinely integrable, bounded by twice the moment and terminal envelope, and tends to zero at fixed times and after real time integration | Applies to the constructed independent comparison array under the extension's assumptions; actual population comparison is supplied below |
| [PredictableExitMask](CarryingCapacity/PredictableExitMask.lean) | Rational strict-past survival is raw predictable; actual right-local constancy identifies it with the inclusive genuine-exit mask; nonnegative compensation retains the exit jump | Generic compensation bridge; its actual population application is supplied below |
| [DeterministicEnvironmentConfiguration](CarryingCapacity/DeterministicEnvironmentConfiguration.lean), [ConfigurationTimeDependent](CarryingCapacity/ConfigurationTimeDependent.lean), [NonlinearParticleConfiguration](CarryingCapacity/NonlinearParticleConfiguration.lean) | Actual interacting and prescribed-environment configurations use the same time-dependent construction; independent nonlinear coordinates equal the prescribed-environment configuration on one full-probability event, including positive-time pre-states | Identification preserves the actual common noise; full population convergence remains separate |
| [ExitTimeMeasurability](CarryingCapacity/ExitTimeMeasurability.lean), [StoppedPathMeasurability](CarryingCapacity/StoppedPathMeasurability.lean) | Actual exit attainment and AE measurability; jointly AE measurable stopped paths and measurable versions of their uncountable running costs | Derived from the actual joint path measurability and right-local constancy; no raw stopping-time or usual-filtration assertion |
| [SynchronousStoppedCompensation](CarryingCapacity/SynchronousStoppedCompensation.lean), [SynchronousStoppedRunningSupremum](CarryingCapacity/SynchronousStoppedRunningSupremum.lean) | Compensation through the genuine joint exit and actual stopped expected-supremum inequality; the exit jump is retained | Extended expectations may initially be infinite; later population integrability is derived below |
| [PopulationCouplingAlgebra](CarryingCapacity/PopulationCouplingAlgebra.lean), [PopulationStoppedCoupling](CarryingCapacity/PopulationStoppedCoupling.lean), [PopulationStoppedIntegrability](CarryingCapacity/PopulationStoppedIntegrability.lean) | Exact coordinate activity averaging and moment decomposition; actual stopped population inequality, AE measurability, finite expectation, and real integrability with no assumed stochastic comparison | Constants are independent of N; sharp Gronwall and the population limit are supplied below |
| [GlobalLyapunovExit](CarryingCapacity/GlobalLyapunovExit.lean), [PopulationCouplingExit](CarryingCapacity/PopulationCouplingExit.lean), [PopulationCouplingRemoval](CarryingCapacity/PopulationCouplingRemoval.lean) | Actual whole-horizon joint-exit probability bounded by C/R with an N-independent constant under uniform initial moments; exact stopped/unstopped agreement and Markov cutoff-removal estimate | Supplies the tail and event bounds, not the final population limit or focal comparison |
| [IntegrableGronwall](CarryingCapacity/IntegrableGronwall.lean), [PopulationCouplingTime](CarryingCapacity/PopulationCouplingTime.lean) | Forced exponential comparison for integrable subsolutions; actual expected stopped cost is monotone, measurable, finite and time integrable | No expected-cost continuity or assumed stochastic estimate is used |
| [PopulationNonlinearError](CarryingCapacity/PopulationNonlinearError.lean), [PopulationStoppedVolterra](CarryingCapacity/PopulationStoppedVolterra.lean), [PopulationStoppedGronwall](CarryingCapacity/PopulationStoppedGronwall.lean) | Exact actual error identification with the independent nonlinear array; derived fixed-time/product integrability; sharp actual stopped Volterra and Gronwall estimates with a coefficient independent of N | Establishes the canonical stochastic estimates of Proposition 5.3; externally supplied PRM-space realization remains separate |
| [PopulationCouplingInitialization](CarryingCapacity/PopulationCouplingInitialization.lean) | Exact vector marginal preservation transfers initial Lyapunov integrability and uniform expectations; actual expected pairing error tends to zero from manuscript initialization | Retains jointly exchangeable initial laws; actual paired-path symmetry is supplied by the relabeling modules below |
| [PopulationCouplingProbability](CarryingCapacity/PopulationCouplingProbability.lean), [PopulationCouplingConvergence](CarryingCapacity/PopulationCouplingConvergence.lean) | Actual stopped expectations vanish for fixed R; genuine uniform exit estimate removes the cutoff after the population limit, proving vanishing running-cost event probabilities | Family theorem uses initial expected pairing-error convergence; the final wrapper below derives it |
| [PopulationEmpiricalCoupling](CarryingCapacity/PopulationEmpiricalCoupling.lean), [PopulationSynchronousApproximation](CarryingCapacity/PopulationSynchronousApproximation.lean) | Genuine all-time empirical transport supremum is dominated by the average coordinate supremum; original initialization yields paired canonical systems with exact initial marginals, vanishing stopped expectation, averaged path discrepancy and empirical discrepancy in probability | First two conclusions of Theorem 5.4; the fixed-focal conclusion is supplied below. Canonical initial-vector projection and Section 6's nonlinear-law limit are supplied below; an external whole-trajectory law identification remains separate |
| [ParticleRelabeling](CarryingCapacity/ParticleRelabeling.lean), [ConfigurationRelabeling](CarryingCapacity/ConfigurationRelabeling.lean), [PopulationStoppedExchangeability](CarryingCapacity/PopulationStoppedExchangeability.lean) | Exact measure-preserving paired-input relabeling, noise counting-measure identities, and actual path equivariance via counting equations and pathwise uniqueness; genuine common exit invariance and equal expected stopped coordinate costs | No path-symmetry or equal-expectation premise; these are derived from initial exchangeability. Does not identify an external process law |
| [PopulationFocalProbability](CarryingCapacity/PopulationFocalProbability.lean), [PopulationFocalConvergence](CarryingCapacity/PopulationFocalConvergence.lean), [PopulationFocalApproximation](CarryingCapacity/PopulationFocalApproximation.lean) | One common exit term plus k times the stopped mean gives the actual focal probability bound; population-then-cutoff limits prove fixed-focal approximation; all three canonical Theorem 5.4 conclusions hold for one family supplied by manuscript initialization | Exact first-k interpretation once N is at least k; Section 6's independent empirical uniform limit is supplied above and the path-space conclusion below |
| [PopulationEmpiricalLimit](CarryingCapacity/PopulationEmpiricalLimit.lean) | Manuscript initialization yields uniform-in-time empirical Wκ and generalized-moment convergence in probability for the actual canonical system with the exact original initial vector law | Theorem 6.3's canonical uniform conclusions; no externally supplied trajectory-law identification or J1 random-path measurability |
| [CoupledLawConvergence](CarryingCapacity/CoupledLawConvergence.lean) | Vanishing mismatch probability and an exact comparison law imply weak convergence of actual pushforward probability laws via bounded continuous tests | Countable state spaces and genuine measurable couplings; no across-row compatibility |
| [PopulationFixedTimeChaos](CarryingCapacity/PopulationFixedTimeChaos.lean) | For each fixed time and finite k, actual canonical first-k laws converge weakly to the product nonlinear marginal under manuscript initialization | Fixed-time Corollary 6.4; the stronger path-law conclusion is proved separately in `PopulationPathChaos` |
| [SkorokhodJ1](CarryingCapacity/SkorokhodJ1.lean) | Increasing homeomorphic time changes, genuine J1 metric and Borel structure on actual càdlàg paths, time-change convergence criterion and uniform-to-J1 convergence | Actual Borel path maps and stochastic path-law limits are supplied below; no path-space completeness claim |
| [SkorokhodPathOperations](CarryingCapacity/SkorokhodPathOperations.lean), [FiniteTimeChange](CarryingCapacity/FiniteTimeChange.lean), [SkorokhodStepApproximation](CarryingCapacity/SkorokhodStepApproximation.lean) | Actual restrictions and uniformly continuous state maps; piecewise-affine time changes; measurable finite-grid paths converging in J1 for finite-activity trajectories | Derives genuine Borel AE measurability from actual coordinate observations and finite activity; retains the terminal value; no path-space completeness claim |
| [CanonicalSkorokhodPaths](CarryingCapacity/CanonicalSkorokhodPaths.lean), [AdaptedStateSpace](CarryingCapacity/AdaptedStateSpace.lean) | Actual canonical configuration/nonlinear trajectories as Borel AE-measurable J1 paths; adapted state metric with the original measurable sets; finite-vector maximum metric and uniformly continuous empirical-law map | Càdlàg regularity and finite activity are derived from the constructed processes; a constant fallback only affects exceptional samples |
| [CoupledPathLawConvergence](CarryingCapacity/CoupledPathLawConvergence.lean), [ConcentratingLaw](CarryingCapacity/ConcentratingLaw.lean) | Bounded continuous tests convert a null-measurable discrepancy event or distance concentration into weak convergence of actual pushforward probability laws on varying sample spaces | Generic probability-limit premises are discharged by the actual population theorems below; no separability or completeness premise on the target path space |
| [NonlinearSkorokhodArray](CarryingCapacity/NonlinearSkorokhodArray.lean) | Exact finite-product laws of full input records give a Borel AE-measurable vector J1 path with mutually independent, identically distributed full nonlinear coordinate paths | One path in the finite product state space, with a common time change; no identification with a product-of-paths topology is assumed |
| [PopulationSkorokhodLimit](CarryingCapacity/PopulationSkorokhodLimit.lean) | Actual empirical J1 distance is bounded by the proved uniform transport error; canonical empirical path laws converge weakly to the Dirac law of the continuous nonlinear curve | Theorem 6.3's empirical path-space conclusion under manuscript initialization, for each finite horizon including zero |
| [PopulationPathChaos](CarryingCapacity/PopulationPathChaos.lean) | The proved focal discrepancy bound gives whole-vector path equality outside a vanishing null-measurable event; exact initial projection yields canonical weak convergence to the independent nonlinear vector-path law | Theorem 6.3's focal J1 chaos in the maximum adapted metric; fixed k, with explicit padding of the finitely many rows N<k; includes k=0 |
| [RateControl](CarryingCapacity/RateControl.lean) | Every admissible jump has adapted length at least one; total rate is bounded by weighted activity; actual finite-configuration Lyapunov sublevels are finite | Gives deterministic finiteness needed for freezing, without constructing the driving random measures |
| [FiniteGenerator](CarryingCapacity/FiniteGenerator.lean) | Single-particle update identity; exact generator identity for empirical averages; averaged Lyapunov drift | Does not apply Dynkin's formula or construct a process |
| [Freezing](CarryingCapacity/Freezing.lean) | Finite-proposal recursion; one-jump enlargement; retaining the exit jump; permanent freezing; unique compatible patch; finite-horizon agreement; exit-tail bounds imply almost-sure exhaustion and patching | Requires the exit bounds and compatibility; does not derive them from a Poisson SDE or prove adaptedness of the patch |
| [CountableJumpProcess](CarryingCapacity/CountableJumpProcess.lean) | Actual product exponential waiting times; independence; positive waits and strictly increasing arrivals tending to infinity almost surely; measurable locally finite arrival counting measure | Distributional identities are supplied in the clock-law modules below |
| [FrozenProcess](CarryingCapacity/FrozenProcess.lean) | Actual independent uniform marks; measurable thinning paths from a deterministic initial state; finite-range confinement; a.s. right continuity, left limits, and permanent freezing | Does not yet establish adaptedness, the compensator, or common-noise compatibility across cutoff clock rates |
| [PoissonClockLaw](CarryingCapacity/PoissonClockLaw.lean) | Exponential survival and conditional memorylessness; residual-life law; exact zero-proposal probability for the constructed count | These partial clock laws are not a proof of the full Poisson-process characterization |
| [PoissonIncrements](CarryingCapacity/PoissonIncrements.lean) | Shifted-clock law and head/tail independence; nonatomic arrivals; renewal recurrence; exact Poisson law of the actual count at every nonnegative time | One-time laws alone do not imply independent increments |
| [PoissonRestart](CarryingCapacity/PoissonRestart.lean) | Whole-clock restart under survival of the first wait; exact two-count law; actual count/increment product law; stationary increment law and independence from the starting count | Independence from a count alone does not establish independence from its entire history |
| [PoissonFiniteDimensional](CarryingCapacity/PoissonFiniteDimensional.lean) | Full mutual independence of all increments on every finite monotone time grid; actual product Poisson law, including repeated times and arbitrary nonnegative starting time | Full-past independence is supplied below; the marked PRM law remains separate |
| [PoissonMoments](CarryingCapacity/PoissonMoments.lean) | Poisson first-moment series, finite extended moment, genuine integrability, and exact expectations for actual clock counts and increments | Does not identify a marked-noise compensator |
| [PoissonTransform](CarryingCapacity/PoissonTransform.lean) | Absolute integrability and exact complex power transforms for Poisson laws, actual clock counts and increments, and finite products, for every complex argument | Distributional transforms alone do not give independence from a filtration |
| [CountVectorTransform](CarryingCapacity/CountVectorTransform.lean) | Finite count-vector laws are determined by their power integrals on the unit torus, using characteristic-function uniqueness | A uniqueness theorem for supplied finite measures, not a count-law construction |
| [PoissonSuperposition](CarryingCapacity/PoissonSuperposition.lean) | Independent vectors with product Poisson laws sum to a product Poisson vector with summed coordinate rates; exact transform and integrability | Full-vector independence and each component law are explicit hypotheses, discharged for actual strips below |
| [PoissonPastIndependence](CarryingCapacity/PoissonPastIndependence.lean) | Future clock increment independent of the entire past count filtration, proved from finite-vector laws and a directed union; exact conditional increment expectation | This is the clock's raw natural filtration; the larger marked-noise history still needs its own independence proof |
| [PoissonMartingale](CarryingCapacity/PoissonMartingale.lean) | Actual compensated clock N_t−rt is an integrable adapted martingale with zero mean; stopping at a deterministic horizon preserves it | Does not assert random optional sampling or a marked-process compensator |
| [MarkedNoise](CarryingCapacity/MarkedNoise.lean) | One actual counting-measure family for every cutoff, built from independent unit strips; measurable noise; simultaneous local finiteness and absence of coincident arrival times | Full marked PRM characterization remains separate; compensation is supplied below |
| [MarkedIntensity](CarryingCapacity/MarkedIntensity.lean) | Exact expected counting measure equals product Lebesgue measure on the nonnegative quadrant; counts have the correct expected area on every measurable set; full nonnegative deterministic Campbell identity | Does not prove the marked Poisson law or compensation for random predictable integrands |
| [MarkedProducts](CarryingCapacity/MarkedProducts.lean) | Exact iid uniform-mark product integrals; integration over marks reduces the actual bounded clock-product expectation to a power of the single-mark mean | One common horizon; no random predictable-integrand formula |
| [MarkedStripCounts](CarryingCapacity/MarkedStripCounts.lean) | Measurable category prefix and window counts; finite disjoint-union additivity; actual translated strip and common-noise rectangle masses identified with those counts almost surely | Identifications alone do not establish their distributions or time independence |
| [MarkedThinning](CarryingCapacity/MarkedThinning.lean) | A measurable category in an actual strip has Poisson law with parameter T times its uniform-mark probability, including zero intensity | One category at one nonnegative horizon |
| [MarkedSplitting](CarryingCapacity/MarkedSplitting.lean) | Full product Poisson law and mutual independence for finitely many disjoint measurable categories in one actual strip | All categories use the same nonnegative horizon; the strip's finite-grid extension is supplied below |
| [MarkedBlockProducts](CarryingCapacity/MarkedBlockProducts.lean) | Actual iid law at distinct mark coordinates; exact product integrals over disjoint finite index sets and consecutive blocks with arbitrary starting index | Deterministic mark-index blocks; random time blocks are supplied below |
| [MarkedTimeCounts](CarryingCapacity/MarkedTimeCounts.lean) | Measurable actual grid counts; identification with disjoint consecutive mark blocks; block lengths are clock increments; translated strip masses agree with those counts almost surely | These identifications alone do not establish a distributional law |
| [MarkedTimeProducts](CarryingCapacity/MarkedTimeProducts.lean) | Exact exponential transform for bounded measurable mark products on the actual random blocks of a finite monotone nonnegative time grid | Integrates deterministic factors assigned to each window; no predictable random-integrand formula |
| [MarkedGridLaw](CarryingCapacity/MarkedGridLaw.lean) | Full product Poisson law for actual strip counts on a finite time grid, with any finite category type and categories varying between windows | Categories must be disjoint within each window; the full common-noise extension is supplied below |
| [MarkedBoundedCounts](CarryingCapacity/MarkedBoundedCounts.lean) | Bounded-height common-noise prefix and window counts are finite sums of actual strip counts; translated category probabilities sum to positive Lebesgue mass | Categories have a common strict natural upper bound; this module does not identify their joint law |
| [MarkedRectangleLaw](CarryingCapacity/MarkedRectangleLaw.lean) | Actual masses of disjoint bounded-height rectangles have the joint product Poisson law with parameters T times positive Lebesgue masses | One fixed label and a common horizon T≥0; general finite-intensity planar sets and bounded future-rectangle independence are supplied below |
| [MarkedGridRectangles](CarryingCapacity/MarkedGridRectangles.lean) | Actual common counting-measure masses on finite-grid rectangles have the full product Poisson law, with parameters window length times positive Lebesgue category mass | One fixed label, monotone grid with nonnegative start, and measurable categories disjoint per window under a common strict natural height bound; arbitrary finite-intensity planar-set laws are supplied below; joint future-grid independence from the past remains separate |
| [MarkedSetCounts](CarryingCapacity/MarkedSetCounts.lean), [PoissonLawLimit](CarryingCapacity/PoissonLawLimit.lean), [MarkedSetPoissonLimit](CarryingCapacity/MarkedSetPoissonLimit.lean) | Actual finite-intensity natural counts and exact expectations; symmetric-difference error bounds; full-vector Poisson laws pass through summable set approximation | Law-transfer bridge takes proved approximating laws; the final application below discharges them |
| [FiniteDisjointApproximation](CarryingCapacity/FiniteDisjointApproximation.lean), [MarkedRectangleAlgebra](CarryingCapacity/MarkedRectangleAlgebra.lean), [MarkedBoxApproximation](CarryingCapacity/MarkedBoxApproximation.lean), [MarkedAlgebraExtension](CarryingCapacity/MarkedAlgebraExtension.lean) | Disjoint measure-dense algebra approximations; summable bounded-box truncation; extension from bounded Boolean rectangle laws to finite-intensity measurable sets | Pure approximation and extension; finite target intensity is required |
| [TimeGridRefinement](CarryingCapacity/TimeGridRefinement.lean), [PoissonCoordinateSum](CarryingCapacity/PoissonCoordinateSum.lean), [MarkedBoundedAlgebraLaw](CarryingCapacity/MarkedBoundedAlgebraLaw.lean), [MarkedPoissonMeasure](CarryingCapacity/MarkedPoissonMeasure.lean) | Finite Boolean rectangle refinement and product-Poisson aggregation; exact product law and joint independence for actual masses of every finite disjoint family of measurable finite-intensity planar sets | One fixed noise label and finite target intensities; the full extension is supplied below |
| [MarkedInfiniteIntensity](CarryingCapacity/MarkedInfiniteIntensity.lean), [IndependentNoiseLabels](CarryingCapacity/IndependentNoiseLabels.lean), [MarkedFullPoissonLaw](CarryingCapacity/MarkedFullPoissonLaw.lean) | Actual mass is almost surely infinite on each infinite-intensity set; whole random measures are jointly independent across labels; exact product laws for arbitrary measurable disjoint sets, including mixed finite/infinite intensities and finite arrays of distinct labels | Disjointness is required within each label only; joint future-array independence from the whole marked past remains separate |
| [NullAugmentedIndependence](CarryingCapacity/NullAugmentedIndependence.lean), [ClockPastObservation](CarryingCapacity/ClockPastObservation.lean) | Independence survives ambient-null augmentation; exact censored arrivals and arrival masks are measurable in the augmented full count history; the next clock increment remains independent | Retains the actual samples, including exceptional values; does not assert right continuity of the filtration |
| [MarkedPastProducts](CarryingCapacity/MarkedPastProducts.lean), [MarkedObservation](CarryingCapacity/MarkedObservation.lean) | Deterministic disjoint mark products factor; actual censored arrival-time/mark observations have explicit measurable clock means; past/future mark factors separate after fixing a good clock | Random-index independence is derived by integration, not assumed |
| [MarkedPastTransform](CarryingCapacity/MarkedPastTransform.lean) | Exact factorization of finite observed-past test products against a future-window mark transform, using proved clock-past independence | Deterministic window and mark factors; no predictable compensation |
| [CountRestriction](CarryingCapacity/CountRestriction.lean), [CylinderIndependence](CarryingCapacity/CylinderIndependence.lean) | Power transforms identify restricted count laws, including zero-mass events; finite-cylinder factorization generates independence of the whole product-valued observation | Generic bridge lemmas with explicit transform or event-factorization hypotheses, applied to the actual strip below |
| [MarkedPastIndependence](CarryingCapacity/MarkedPastIndependence.lean) | The actual future category count has its Poisson law and is independent of the full indexed history of censored arrival times and marks in one strip | One future category count and one strip; the common-noise lift is supplied below, while joint future windows/categories within a strip remain separate |
| [IndependentProductHistory](CarryingCapacity/IndependentProductHistory.lean) | Coordinatewise past/future independence lifts through the actual infinite product law to independence of complete observation and future arrays | Uses proved coordinate independence and measurable coordinate functions; does not infer joint independence from pairwise independence |
| [CommonMarkedPastIndependence](CarryingCapacity/CommonMarkedPastIndependence.lean) | Future strip-category arrays, bounded strip sums, and actual bounded rectangle masses are independent of the full existing common-noise history, including its null augmentation and completed law | One deterministic window and one category per strip; joint future windows/categories within a strip remain separate |
| [InitialMarkedPastIndependence](CarryingCapacity/InitialMarkedPastIndependence.lean) | Actual future rectangle counts are independent of the complete initial-record plus marked-noise history, also under null augmentation and the completed law | One future window and bounded measurable height category |
| [MarkedCountMoments](CarryingCapacity/MarkedCountMoments.lean), [MarkedCountAdapted](CarryingCapacity/MarkedCountAdapted.lean), [MarkedCountMartingale](CarryingCapacity/MarkedCountMartingale.lean) | Actual count finiteness, integrability and first moments; adaptedness to the full marked history; conditional window means and compensated-count martingale | Bounded measurable height categories; raw noise filtration for the martingale |
| [MarkedElementaryCompensation](CarryingCapacity/MarkedElementaryCompensation.lean), [InitialElementaryCompensation](CarryingCapacity/InitialElementaryCompensation.lean) | Past-measurable nonnegative coefficients times actual future counts; elementary predictable compensation, including completed initial-product histories | Full predictable extension is supplied below for raw histories |
| [PredictableSets](CarryingCapacity/PredictableSets.lean), [PredictableCompensation](CarryingCapacity/PredictableCompensation.lean) | Positive-time predictable sigma algebra; actual Campbell measure equals product intensity on it; compensation for every nonnegative predictable integrand, allowing infinite expectations | No arbitrary-planar Poisson law or optional sampling is assumed or asserted |
| [MarkedCountingKernel](CarryingCapacity/MarkedCountingKernel.lean), [PredictableIntegral](CarryingCapacity/PredictableIntegral.lean) | Actual s-finite counting kernel; Bochner Fubini; predictable integrability equivalence and signed or vector-valued compensation | Explicit integrability under the deterministic sample-time-height measure is required |
| [InitialPredictableCompensation](CarryingCapacity/InitialPredictableCompensation.lean) | Fixing any initial record preserves predictability; full nonnegative compensation under the actual initial-record/noise product law | Raw product filtration; arbitrary completed predictable integrands remain separate |
| [FrozenCompatibility](CarryingCapacity/FrozenCompatibility.lean) | Nested frozen recursions agree through their actual first exit, including the exit jump; exit indices are monotone; stopped continuous-time paths agree under a common locally finite clock | This module uses a common proposal sequence; actual cutoff-list compatibility is supplied below |
| [ChronologicalEvents](CarryingCapacity/ChronologicalEvents.lean) | Jointly measurable chronological lists from actual time-height boxes; strict ordering, exact membership, time prefixes, and height filtering simultaneously for all cutoffs almost surely | Local finiteness and distinct times come from the constructed common noise |
| [RejectedProposals](CarryingCapacity/RejectedProposals.lean), [CommonFrozenProcess](CarryingCapacity/CommonFrozenProcess.lean) | Actual shared-noise frozen paths; joint measurability and finite range; almost-sure invariance under changing a valid rate bound, permanent freezing, and nested-path agreement through the exit jump | Countable state space, finitely many directions and autonomous rates; the generator expectation identity is supplied below |
| [CommonFrozenRegularity](CarryingCapacity/CommonFrozenRegularity.lean), [CommonFrozenExit](CarryingCapacity/CommonFrozenExit.lean) | Genuine first exits as infima; almost-sure càdlàg paths, initial interval, finite-exit attainment, monotone exits, and stopped-larger-path equality with the smaller frozen path | Exit probability estimates and stopping-time properties are supplied below |
| [TimeDependentFrozenProcess](CarryingCapacity/TimeDependentFrozenProcess.lean), [TimeDependentRateLocalization](CarryingCapacity/TimeDependentRateLocalization.lean), [TimeDependentFrozenExit](CarryingCapacity/TimeDependentFrozenExit.lean) | Actual event-time rates in the common-noise recursion; joint measurability, finite confinement, càdlàg paths and genuine exits; cutoff independence and nested compatibility from horizon-local bounds by time clamping | Finite active sets and time horizons; global cutoff removal is supplied below |
| [PredictableTime](CarryingCapacity/PredictableTime.lean), [TimeDependentHistory](CarryingCapacity/TimeDependentHistory.lean), [TimeDependentPredictable](CarryingCapacity/TimeDependentPredictable.lean), [TimeDependentInitial](CarryingCapacity/TimeDependentInitial.lean) | All-sample raw-history factorization and adaptedness; predictable evaluation of measurable time coefficients; actual pre-jump states and arbitrary independent initial records | Finite active set; no proposed-process measurability or predictability is assumed |
| [TimeDependentJumpIdentity](CarryingCapacity/TimeDependentJumpIdentity.lean), [TimeDependentCountingIdentity](CarryingCapacity/TimeDependentCountingIdentity.lean), [TimeDependentInitialCounting](CarryingCapacity/TimeDependentInitialCounting.lean) | Actual chronological telescoping and integrable signed counting-measure equation with event-time rates, including the exit jump and independent initial records | Fixed finite height cutoff; the global cutoff-free equation is supplied below |
| [TimeDependentIntensity](CarryingCapacity/TimeDependentIntensity.lean), [TimeDependentInitialCompensation](CarryingCapacity/TimeDependentInitialCompensation.lean), [TimeDependentGeneratorIntegral](CarryingCapacity/TimeDependentGeneratorIntegral.lean), [TimeDependentPreStateTime](CarryingCapacity/TimeDependentPreStateTime.lean), [TimeDependentDynkin](CarryingCapacity/TimeDependentDynkin.lean) | Finite-box product integrability, signed compensation, actual current-state generator identification and initialized Dynkin formula; genuine Fubini yields the integral of expected drift | Measurable time rates, nonnegative and bounded on the active set during the horizon; change identity needs no initial moment, separate expectations require an integrable initial test value |
| [TimeDependentHistoryIntegral](CarryingCapacity/TimeDependentHistoryIntegral.lean) | Exact later-history reconstruction and raw-history measurability of actual current-state time integrals | This is a measurability statement; integrability and Dynkin are supplied separately |
| [TimeDependentMartingale](CarryingCapacity/TimeDependentMartingale.lean), [TimeDependentGeneratorMartingale](CarryingCapacity/TimeDependentGeneratorMartingale.lean) | Actual compensated accepted-increment martingale and classical current-state generator martingale in the raw filtration; genuine integrability and zero expectation | Finite active set; the all-time generator martingale requires nonnegative bounded active rates for every positive time, provided by the endpoint-clamped construction |
| [TimeDependentExpectation](CarryingCapacity/TimeDependentExpectation.lean), [TimeDependentLyapunovBound](CarryingCapacity/TimeDependentLyapunovBound.lean), [TimeDependentInitialExit](CarryingCapacity/TimeDependentInitialExit.lean) | Actual frozen expectation continuity and Fubini; affine-exponential Lyapunov estimate; Markov bound for the genuine first-exit event | Derived from pointwise active drift and integrable initial Lyapunov value, without an assumed expectation or exit bound |
| [TimeDependentLocalization](CarryingCapacity/TimeDependentLocalization.lean), [TimeDependentGlobalProcess](CarryingCapacity/TimeDependentGlobalProcess.lean), [TimeDependentGlobalActivity](CarryingCapacity/TimeDependentGlobalActivity.lean) | Canonical finite-sublevel paths and positive rate caps; compatible paths and monotone exits; raw jointly measurable adapted global patch; horizon agreement, càdlàg paths and finite actual activity | Generic path conclusions use explicit exit exhaustion; monotonicity of the chosen caps is unnecessary |
| [TimeDependentNonexplosion](CarryingCapacity/TimeDependentNonexplosion.lean), [TimeDependentGlobalMoment](CarryingCapacity/TimeDependentGlobalMoment.lean) | Actual exit tails discharge exhaustion; global nonexplosion and horizon agreement; Fatou gives integrability and ordinary/extended global Lyapunov bounds | Nonnegative rates, finite sublevels, affine drift and an integrable initial Lyapunov value are genuine model hypotheses |
| [TimeDependentGlobalCounting](CarryingCapacity/TimeDependentGlobalCounting.lean), [TimeDependentEquationUniqueness](CarryingCapacity/TimeDependentEquationUniqueness.lean), [TimeDependentGlobalUniqueness](CarryingCapacity/TimeDependentGlobalUniqueness.lean) | Global predictable pre-state equals the actual left limit; pathwise integrable counting equation has no spatial or height cutoff; same-input pathwise uniqueness from separating tests | Generic construction uses proved exhaustion; the environment wrapper discharges it. Candidate uniqueness needs càdlàg paths, the initial value and equations, with no candidate moment or activity bound |
| [IntegralGronwallComparison](CarryingCapacity/IntegralGronwallComparison.lean), [TimeDependentLyapunovComparison](CarryingCapacity/TimeDependentLyapunovComparison.lean), [TimeDependentGlobalComparison](CarryingCapacity/TimeDependentGlobalComparison.lean) | Deterministic forced Gronwall comparison; actual frozen and global Lyapunov bounds under a time-dependent envelope, including genuine integrability and extended moments | Expected drift is derived from the pointwise generator bound; the deterministic envelope is a checked supersolution, and coarse affine drift separately supplies nonexplosion |
| [CommonNoiseFiltration](CarryingCapacity/CommonNoiseFiltration.lean) | Genuine filtration of arrived labelled noise points; exact all-sample factorization of frozen paths through observed history; adaptedness, including initial information measurable at time zero | Full-past independence and predictable compensation are supplied by the modules above |
| [CommonFrozenStopping](CarryingCapacity/CommonFrozenStopping.lean) | Minimal augmentation of noise histories by ambient null sets; actual completed probability law; exact first exits are stopping times and measurable in the completed space, AE-measurable in the original space | No right-continuity or optional-stopping theorem is asserted; Lyapunov exit estimates are derived below from the proved Dynkin identity |
| [CommonInitialNoise](CarryingCapacity/CommonInitialNoise.lean) | Actual product of an arbitrary initial-record law and the full noise law; exact marginals and independence; prescribed initial-state law; joint measurability, adaptedness, and almost-sure càdlàg paths and stopped compatibility | Accepts constructed paired initial laws through measurable projections; Dynkin is supplied below, while the population comparison is supplied by the later population modules |
| [CommonInitialStopping](CarryingCapacity/CommonInitialStopping.lean) | Minimal null augmentation of the actual initial-record/noise product histories; exact first exits are stopping times, completed-measurable and raw AE-measurable; measurable truncated exits and adapted paths | The terminal history is the supremum of finite histories; no right continuity, optional sampling, or compensator is asserted |
| [PredictableStepApproximation](CarryingCapacity/PredictableStepApproximation.lean), [FrozenPredictableIntegrand](CarryingCapacity/FrozenPredictableIntegrand.lean), [InitialFrozenPredictable](CarryingCapacity/InitialFrozenPredictable.lean) | Strict-past deterministic approximations construct predictable pre-jump versions; actual path left limits and accepted test-function increments are identified almost surely, also with arbitrary initial records | The nonpositive-time fallback is fixed; increments vanish there |
| [FrozenJumpIdentity](CarryingCapacity/FrozenJumpIdentity.lean), [FrozenCountingIdentity](CarryingCapacity/FrozenCountingIdentity.lean), [InitialFrozenCountingIdentity](CarryingCapacity/InitialFrozenCountingIdentity.lean) | Actual chronological telescoping, finite atomic integrability and signed counting-measure equation, retaining the exit jump | Finite height cutoff and autonomous rates; non-explosive patching remains separate |
| [FrozenIntensity](CarryingCapacity/FrozenIntensity.lean), [FrozenGeneratorIntegral](CarryingCapacity/FrozenGeneratorIntegral.lean) | Finite active-set bounds give product integrability; actual height integration gives the rate-weighted drift and frozen generator | Nonnegative active rates and a dominating cutoff are required for generator identification |
| [FrozenCompensation](CarryingCapacity/FrozenCompensation.lean), [InitialFrozenCompensation](CarryingCapacity/InitialFrozenCompensation.lean) | Signed compensation and integrability for the actual finite-horizon frozen increments, with all integrability premises discharged | Arbitrary test functions; no initial moment assumption is needed for increments |
| [FrozenPreStateTime](CarryingCapacity/FrozenPreStateTime.lean) | Actual current and pre-jump states agree outside the countable proposal-time set; their restricted time integrals agree, also with sampled initial records | A time-null assertion; equality at jump times is not asserted |
| [FrozenDynkin](CarryingCapacity/FrozenDynkin.lean) | Actual frozen-process Dynkin expectation identity with the current-state generator; test-function and time-integrated drift integrability are derived | Fixed deterministic initial state and horizon; Gronwall and Lyapunov exit estimates are supplied below |
| [InitialFrozenDynkin](CarryingCapacity/InitialFrozenDynkin.lean) | Actual randomly initialized frozen-process Dynkin identity; changes and time-integrated current-state drift are integrable without an initial moment assumption; separate expectations follow when the initial test value is integrable | Fixed horizons and autonomous rates; Lyapunov Gronwall, exit bounds and non-explosion are supplied below |
| [IntegralGronwall](CarryingCapacity/IntegralGronwall.lean), [InitialFrozenExpectation](CarryingCapacity/InitialFrozenExpectation.lean) | Integral Gronwall from continuity; actual sample-time generator integrability and Fubini; expected frozen test values are Lipschitz in time | Fixed finite active set and autonomous rates; no expected-value derivative is assumed |
| [FrozenLyapunovBound](CarryingCapacity/FrozenLyapunovBound.lean), [InitialLyapunovExit](CarryingCapacity/InitialLyapunovExit.lean) | Actual frozen expectation ≤(1+initial expectation) exp(bt)−1; genuine first-exit probability ≤terminal expectation/R; reciprocal tails imply exhaustion | Nonnegative Lyapunov function, affine drift and integrable initial value |
| [LyapunovLocalization](CarryingCapacity/LyapunovLocalization.lean), [ConfigurationLocalization](CarryingCapacity/ConfigurationLocalization.lean) | Canonical finite sublevels and positive rate bounds; simultaneous actual exit monotonicity and compatibility; exact empirical generator and uniform configuration drift from LyapunovControl | Finitely many jump labels; positive particle number for the configuration specialization |
| [GlobalLocalizedProcess](CarryingCapacity/GlobalLocalizedProcess.lean), [GlobalLocalizedActivity](CarryingCapacity/GlobalLocalizedActivity.lean) | Measurable adapted limit of actual cutoffs; prescribed initial state; finite-horizon agreement, cadlag paths, and finite actual proposal lists containing all changes | Generic regularity lemmas take genuine-exit exhaustion explicitly; it is discharged below |
| [ActualNonexplosion](CarryingCapacity/ActualNonexplosion.lean), [ConfigurationNonexplosion](CarryingCapacity/ConfigurationNonexplosion.lean) | Actual exit tails and exhaustion derived from Lyapunov hypotheses; measurable adapted global configuration paths with cadlag regularity and finite activity | No expectation, exit bound or exhaustion assumption; arbitrary initial laws and global uniqueness are supplied below; full mean-field statements remain separate |
| [GlobalLyapunovMoment](CarryingCapacity/GlobalLyapunovMoment.lean), [ActualGlobalMoment](CarryingCapacity/ActualGlobalMoment.lean) | Fatou transfers the level-uniform bound to the actual global path; global Lyapunov integrability and exponential expectation estimate | Bounds the current-time moment; expected running-maximum and weighted-activity estimates remain separate |
| [GlobalLocalizedCountingIdentity](CarryingCapacity/GlobalLocalizedCountingIdentity.lean), [ActualGlobalCounting](CarryingCapacity/ActualGlobalCounting.lean) | Actual predictable global pre-jump state and left limit; unrestricted accepted-increment counting equation and pathwise integrability; Lyapunov and configuration specializations discharge exhaustion | No freezing indicator or height cap remains; global equation uniqueness is supplied below |
| [DiscreteCausalUniqueness](CarryingCapacity/DiscreteCausalUniqueness.lean), [CountingEquationUniqueness](CarryingCapacity/CountingEquationUniqueness.lean), [GlobalCountingUniqueness](CarryingCapacity/GlobalCountingUniqueness.lean), [ActualGlobalUniqueness](CarryingCapacity/ActualGlobalUniqueness.lean) | First-disagreement argument in a discrete state space; pathwise uniqueness from a countable separating family of genuine counting equations; actual particle-coordinate specialization | Candidate paths are càdlàg with the same initial record and driving noise; no candidate activity, rate, or localization bound is assumed |
| [ArbitraryInitialNonexplosion](CarryingCapacity/ArbitraryInitialNonexplosion.lean) | Deterministic-initial Lyapunov proofs give one full noise event for every state; actual nonexplosion, càdlàg paths, finite activity, counting equation, and coordinate uniqueness for arbitrary independent initial laws | Removes the initial-moment premise from these path properties; expectation bounds still require their stated integrability assumptions |
| [FiniteSupportGeometry](CarryingCapacity/FiniteSupportGeometry.lean), [FiniteSupportGlobal](CarryingCapacity/FiniteSupportGlobal.lean), [GlobalFiniteSupportDrift](CarryingCapacity/GlobalFiniteSupportDrift.lean) | Finite backward jump support, bounded test and raw generator, deterministic product integrability of unrestricted increments, and identification of the actual current-state generator compensator | Finitely supported configuration tests; no expected global activity premise |
| [InitialConditionalCompensation](CarryingCapacity/InitialConditionalCompensation.lean), [PredictableHistoryTruncation](CarryingCapacity/PredictableHistoryTruncation.lean), [PredictableCountingMartingale](CarryingCapacity/PredictableCountingMartingale.lean) | Past-event testing derives conditional zero for actual compensated integrals; history truncation gives adaptedness; the actual counting equation implies a martingale | Generic bridge assumes predictable product integrability and the counting equation, both discharged for the configuration application |
| [GlobalHistoryIntegral](CarryingCapacity/GlobalHistoryIntegral.lean), [ConfigurationMartingale](CarryingCapacity/ConfigurationMartingale.lean), [ConfigurationForwardEquation](CarryingCapacity/ConfigurationForwardEquation.lean) | All-sample raw-history reconstruction of time integrals; actual current-state generator martingale; integrated weak forward equation via proved sample-time Fubini | Finitely supported configuration tests and any independent initial probability law; no initial moment required; semigroup and strong Markov statements, and specialization of forward-law uniqueness to the configuration model, remain separate |
| [InitialPredictableIntegral](CarryingCapacity/InitialPredictableIntegral.lean) | Actual initialized counting kernel, predictable integrability equivalence, signed/vector compensation and random-integral integrability | Raw initial-product filtration; deterministic product integrability is explicit |
| [ThinningKernel](CarryingCapacity/ThinningKernel.lean) | Exact accepted-label probabilities; mean one-proposal increment; clock-rate normalization equals the frozen generator; finite active sets admit positive rate bounds | The actual continuous-time Dynkin identity is proved above |
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

`OriginalParticleSystem` now constructs the original finite-N system directly
from `OriginalAssumptions`, using empirical probability measures with no moment
restriction. Its total-population drift follows from the original lineage-linear
rate bound: births contribute one, deaths contribute a nonpositive amount, and
mutations preserve total population. Finite sublevels and the proved localization
chain give nonexplosion, the actual counting equation and coordinate-equation
pathwise uniqueness for arbitrary independent initial laws. This establishes
the particle construction without borrowing the extension's stronger moment hypotheses.

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
from the shared marked noise's measurable chronological event lists. Almost
surely, changing a valid dominating rate bound does not change the path, and
nested active sets give monotone actual exit times and stopped-path compatibility,
including the exit jump. The frozen paths are almost surely càdlàg and are
adapted to the filtration generated by arrived labelled
noise points. The exact first exits are stopping times after the minimal null
augmentation, also on the actual product space with an arbitrary independent
initial law. The underlying exponential clock has its full finite-grid Poisson
law and future increments independent of the entire past count history.

The marked measure has the correct Lebesgue intensity and deterministic Campbell
identity. For one fixed label and a common horizon T≥0, its masses on disjoint
bounded-height rectangles have the joint product Poisson law. Within one strip,
the full marked finite-grid law is proved, allowing categories to vary between
windows and requiring disjointness only within each window. The same full joint
law is proved for bounded-height grid rectangles in the original common counting
measure, for one fixed label. Its parameters are window length times the
positive Lebesgue mass of each category. Boolean rectangle refinement and
summable disjoint measure approximation now extend this to every finite family
of disjoint measurable planar sets of finite intensity, for one fixed noise label.
The full extension now also covers infinite intensity: bounded-box Poisson
lower tails force the genuine mass to be infinite almost surely. Complete
label records, and therefore the entire random counting measures, are jointly
independent across labels. `MarkedFullPoissonLaw.countingMeasure_arrays_map`
gives the exact nested product law for finite arrays of arbitrary measurable
sets at distinct labels, allowing infinite intensities and requiring disjointness
only among sets attached to the same label. Bounded future rectangle counts
are now independent of the full marked history, including an arbitrary
independent initial record. This suffices to prove nonnegative predictable
compensation on the actual raw noise and initial-product filtrations. The
actual frozen path also satisfies its test-function counting equation and
Dynkin expectation identity. Actual expectation/time Fubini and integral
Gronwall now give the uniform Lyapunov expectation estimate. The actual exit
identity then gives reciprocal probability bounds and almost-sure exhaustion.
The global patch is jointly measurable and adapted, agrees with one finite
proposal construction throughout every bounded horizon, and has cadlag paths
and finite activity. The configuration specialization derives its drift directly
from the single-lineage LyapunovControl at the genuine empirical law.

The frozen Dynkin proof uses these actual objects throughout. Strict-past grid
approximations construct predictable pre-jump states, and chronological
finite-list telescoping identifies the real counting-measure integral with
the test-function change, including the exit jump. Finite active states and a
finite time-height box give signed integrability. Compensation and height
integration then identify the expected drift with the existing frozen
generator. Current and pre-jump states differ only at the countable proposal
times, so either version gives the same time integral. This proves a
fixed-horizon expectation identity, also on the actual initial-record product.
The change form needs no initial moment assumption; the separate-expectation
form assumes an integrable initial test value. The subsequent Lyapunov and
patching modules prove non-explosion for the actual autonomous configuration
construction. Fatou also proves the global Lyapunov value is integrable and
retains the exponential bound. The global predictable pre-jump state is proved
to be the actual left limit. Its accepted-increment counting equation holds
against the original counting measures, with the active-set indicator and
height cutoff removed and pathwise integrability proved. The configuration
specialization discharges exhaustion using LyapunovControl. The global equation
is now pathwise unique among discrete càdlàg candidates, even when the candidate
is given only by the particle-coordinate equations. Applying deterministic-initial
nonexplosion on one countable intersection removes the initial-moment assumption
from the path properties for arbitrary independent initial laws.

For finitely supported configuration tests, the finite set of one-jump predecessors
bounds both the raw generator and the actual counting integrand. Past-event
compensation derives the conditional martingale identity. The classical expression
`F(X_t) - F(X_0) - ∫₀ᵗ AF(X_s) ds` has a raw-adapted version proved by reconstructing
the entire past from the terminal observed history; the definition using the
prescribed initial record is itself a martingale. Sample-time Fubini gives its
integrated weak forward equation. These results need no initial moment. Specializing
forward-law uniqueness to the configuration model, semigroup/strong Markov
statements and optional sampling remain separate. The time-dependent frozen construction now evaluates each rate at
the actual proposal time, with raw history adaptation and predictable strict-past
states supplied by the accompanying modules. Endpoint clamping derives
cutoff independence and compatibility from bounds valid only on the selected
horizon. `DeterministicEnvironmentRates` derives the required time measurability
and finite-region horizon bounds from the manuscript assumptions along a
continuous law curve. The actual finite-active time-dependent path satisfies
its counting equation and initialized Dynkin formula. Signed increment
integrability comes from finite-box support; sample-time Fubini gives the
ordinary Lebesgue integral of the expected current-state drift. The change
identity needs no initial test moment, while separate expectations require one.
The actual compensated process and current-state generator expression are
raw-filtration martingales. `DeterministicEnvironmentFrozen` instantiates
these theorems with the actual paper rates, a cap chosen from the activity
bound, and the endpoint-clamped continuous environment. Its horizon-specific
Dynkin formula uses the exact original-environment generator. The all-time
martingale is for the clamped environment, which agrees with the original
one up to the selected horizon.

The time-dependent construction now also has a global spatial localization.
Canonical finite Lyapunov sublevels give compatible frozen paths and monotone
actual exits, with no monotonicity assumption on their chosen rate caps.
Actual Dynkin, Gronwall and Markov estimates prove exit exhaustion from affine
drift and an integrable initial Lyapunov value. The resulting global path is
jointly measurable, raw-adapted, càdlàg and locally finitely active. Fatou retains
its Lyapunov moment bound. Its predictable pre-state agrees with the true left
limit, and the full counting equation has neither a spatial freezing indicator
nor a height cutoff. Same-input pathwise uniqueness follows from the coordinate
equations and càdlàg regularity, without candidate moment or activity assumptions.

`DeterministicEnvironmentProcess` discharges those construction hypotheses from
the manuscript assumptions and a prescribed continuous environment with genuine
Lyapunov moment bounds. For an input from the manuscript curve space, the
time-zero constraint supplies the required initial integrability. The actual
process uses the original environment on `[0,T]` and its endpoint-clamped
extension at later times. `DeterministicEnvironmentEnvelope` verifies the scalar
integral identity for the exact manuscript envelope and proves that envelope
for both the ordinary and extended moments of the actual process.
`DeterministicEnvironmentLaw` packages its genuine pushforward marginals as
MomentLaw values, derives their finite adapted moments, and proves their exact
initial law and integral identities. Nonatomic actual arrival times give
almost-sure continuity at each fixed deterministic time; the event may depend
on the time. Actual joint pushforward couplings and the superlinear Lyapunov
bound yield uniform integrability, so Vitali gives Wκ continuity of these laws.
`DeterministicEnvironmentEvolution` combines this continuity, initial-law identity
and exact envelope into an actual self-map of the complete manuscript curve
space.

The two actual environment paths can now be compared on their common marked
noise. Finite paired recursions give pathwise positive-increment domination,
including shared jumps; the pre-state and current state agree outside a
time-null set. Nonnegative predictable compensation turns the actual jump sum
into the exact integrated height activity, without assuming finite expected
activity or a coupling estimate. The manuscript coupling hypothesis then gives
the coefficient `A = L(1+2K(T))` using the proved input and output moments.
Superlinear uniform integrability proves continuity of the actual expected
distance. An integrating-factor comparison yields the exponential Volterra
bound for the fixed-time expected distance and hence for the output laws.
The actual running supremum is also AE measurable: right-local constancy
identifies it with rational observations and the terminal value. Its expectation
is bounded by the same integrated positive activity.
`DeterministicEnvironmentRunningSupremum` proves the paper's exact exponential
convolution bound for this expected supremum, deriving its finite expectation
and the integrability of its real-valued version. No continuity or finite
expectation of the running supremum is assumed.

`NonlinearFixedPoint` applies the proved estimate to the actual evolution with
Bielecki weight `2A+1`. Under a genuine finite initial Lyapunov moment, it proves
exactly one fixed curve in the manuscript's invariant space and constructs its
canonical initialized process. This process is measurable, adapted, càdlàg and
nonexplosive; its actual marginals equal the fixed curve, obey the exact moment
envelope, and occur in its own no-cutoff counting equation on `[0,T]`. After `T`
the construction holds that environment at its endpoint, so all-time nonlinear
self-consistency is not asserted.

Finite-support tests now give the actual untruncated weak forward equation.
Their finite predecessor sets bound all nonzero accepted increments and the
current-state generator. Signed predictable compensation and genuine product
integrability justify Fubini, so the tested equation is derived from the
constructed counting process. The fixed curve also satisfies the nonlinear
weak equation with its own actual law in the generator.

Linear law uniqueness uses finite-state comparison. The actual frozen masses
satisfy a finite integrated system, including outgoing loss at the boundary;
self-jumps cancel exactly. Restricting any probability-valued weak solution
adds a nonnegative finite external inflow. Comparison orders the masses, then
actual exit exhaustion and bounded convergence pass that order to the global
law. Since both laws have total mass one, atomic domination implies equality.
The weak-solution definition requires genuinely integrable tested drifts;
continuity of its atoms is derived, and no competing-law moment is assumed.
`DeterministicEnvironmentGeneralForward` supplies existence and the matching
uniqueness module identifies every competing weak law on `[0,T]`. This applies
to general prescribed Wκ-continuous environments with uniformly bounded genuine
Ψ moment and a finite initial Ψ moment, without requiring the environment's
time-zero value to equal the initial law. No arbitrary continuation beyond the
chosen interval is identified. `DeterministicEnvironmentGeneralLaw` packages
these actual marginals as MomentLaw values and proves their Wκ continuity from
fixed-time path continuity and genuine uniform superlinear moments. The
canonical construction therefore includes Proposition 4.2's general output-law
continuity. `PrescribedDeterministicEnvironment` supplies its formulation on
an arbitrary supplied PRM space with a completed right-continuous filtration.

`AtomicTransportContinuity` derives Wκ continuity for any moment-bounded
nonlinear weak solution. It uses atomic continuity from the tested equation,
finite-truncation atom identities and uniform Lyapunov tails; candidate
continuity is not assumed. Linear law uniqueness then identifies each candidate
with its actual driven process. `DeterministicEnvironmentGeneralCoupling`
compares two such processes with the same initial record and noise. Their
candidate bounds control genuine endpoint moments, and predictable compensation
yields an integrable expected-distance inequality. The actual joint law bounds
input transport by expected distance, so Gronwall forces equality.
`NonlinearForwardUniqueness` thus proves Theorem 4.3's law existence and
uniqueness in the full uniformly Ψ-bounded weak-solution class. Identification
with the constructed fixed curve also gives the exact K(t) envelope. On the
interval domain, the theorem is an exact unique-existence statement for
arbitrary law functions with genuine tested time integrability.

`FiniteJumpForwardRestriction` preserves that integrability under restriction
and local changes of coefficients and laws. `NonlinearHorizonConsistency`
uses it to prove that larger fixed curves restrict to smaller ones, and their
actual process marginals agree throughout the overlap. `TimeDependentLocalUniqueness`
and `NonlinearPathConsistency` then prove actual same-input path equality, including
the endpoint. `NonlinearGlobalProcess` constructs one measurable, raw-adapted,
càdlàg process on all nonnegative times, with the consistent law as its actual
marginal and the exact moment envelope. `NonlinearGlobalCounting` proves its
predictable left-state counting equation, integral finiteness and finite activity
on every bounded interval. `NonlinearGlobalForward` gives global weak-law existence
and uniqueness under local genuine Lyapunov bounds. The prescribed-space
realization and usual-natural adaptedness are supplied by
the reconstruction and concrete process modules above. Localization and
usual-filtration martingale consumers remain separate.

`EmpiricalLLN.wasserstein_strongLaw` proves the full empirical transport strong
law using finite-state common-mass couplings and vanishing moment tails.
`EmpiricalMeanError` upgrades this to expected and time-integrated error
convergence under the manuscript's Lyapunov assumptions.
`ExchangeableMatching.exists_exchangeable_optimal_iid_coupling` constructs the
actual paired law while preserving both full vector marginals. It uses a fresh
uniform permutation of the matched pair array to obtain joint exchangeability.
`InitialCoupling.exists_initial_coupling` assembles that construction with the
proved uniform-integrability and LLN results: its expected pairing cost tends
to zero under the manuscript's initialization hypotheses. `EmpiricalArrayError`
transfers expected and time-integrated errors to finite iid arrays that vary
with N, without requiring those arrays to be initial segments of one sequence.
`CommonInitialNoise` then realizes a prescribed initial record independently
of the entire common noise and constructs the corresponding adapted frozen
paths. A paired-array law from `InitialCoupling` can serve as that initial record,
preserving its complete joint law while either vector projection initializes a
process. `CommonInitialStopping` supplies the completion and exact first-exit
stopping-time statements for that enlarged product filtration.

`ParticleNoiseProjection` and `ParticleInputRecords` now prove the full joint
law of the nonlinear initial/noise records extracted from this same space.
`NonlinearParticleArray` applies the actual nonlinear process to these records:
the trajectories are independent for the coordinate sigma algebra, their
fixed-time vector law is the product nonlinear law, and their counting
equations use the original particle-labelled measures. The continuation after
the chosen horizon keeps the environment fixed at its endpoint.
`NonlinearSkorokhodArray` additionally proves full coordinate-path independence
in the genuine J1 Borel spaces, and gives the exact joint vector-path law.
`PopulationPathChaos` transfers the focal estimate to that law using whole-path
equality outside the discrepancy event and exact canonical initial projection.
`NonlinearParticleEmpirical` derives genuine error and time integrability and
proves the actual time-integrated independent empirical error tends to zero.
`PredictableExitMask` proves compensation up to and including a genuine exit
using a raw predictable rational-history version. It does not discard the
exit jump or assume a completed-filtration compensation theorem.

The quadratic coupling calculation includes the shared-jump contribution.
For a nonlinear κ, even a simultaneous birth can increase the distance;
controlling only unmatched jumps would miss this term.

## Completed manuscript scope and boundaries

All numbered results in manuscript snapshot `c768811` have checked proofs under
the stated model and initialization hypotheses. The full standalone Lemma 4.1
now applies to arbitrary adapted càdlàg environment pairs and a common stopping
time. Separate coordinate equations imply the pathwise positive-increment
bound; actual Poisson compensation yields its expectation. The finite-state
case derives the required integrability from ordinary jump rates, while the
general bound and Fatou localization passage cover an integrably controlled
right-hand side.

The supplied-space frozen paths, true exit compatibility, stopping times,
stopped moments and exit estimates are proved. Lemma 3.5 and Corollary 3.6
now have their exact supplied-space activity and population-uniform moment
and maximal bounds. Proposition 4.2 now has its
explicit prescribed-input formulation. Corollary 4.4 has its actual
whole-horizon maximal bound and pathwise uniqueness using candidate equations
only on the stated finite horizon. The generator martingale in the prescribed
usual-natural filtration and supplied-system exchangeability are proved;
right continuity is handled by dominated limits of genuine past-event
integrals, rather than inferred from adaptedness.

Future bounded-height Poisson counts remain independent of the usual natural
past. A genuine s-finite counting kernel equals the supplied measures almost
surely, so predictable compensation there follows from their actual Poisson
laws and initial independence. The universal noise event quantifies over arbitrary candidate coefficients
and paths afterward. Compact-horizon càdlàg bounds then give the samplewise
finite sets and rate caps needed for the comparison, without imposing extra
finite-state or finite-activity assumptions on the general result.

Proposition 7.5's closed first-moment ODE is proved with genuine unbounded-test
justification and global nonnegative uniqueness. The multitype hypotheses for
every real p>1, quadratic hypotheses for every real r>2 and model limit
applications are also proved.

Remark 2.1 is proved, including both exact real-power comparison inequalities,
the genuine ordinary Wp metric and equality of convergence topologies.

Optional sampling, semigroup/strong Markov results and stronger joint-future
independence assertions may be useful extensions, but they are not additional
mandatory targets of the specified Kenny manuscript. All canonical Section 6 conclusions are now proved.

The original paper remains a separate, inactive completion target: Feller/core
and empirical Markov identification, and the mean-field and chaos results under
its weaker initialization, are unfinished. Its actual finite-N nonexplosive
construction and coordinate-equation pathwise uniqueness are proved directly
from its own assumptions; Kenny's stronger moment hypotheses do not replace
that original convergence theorem.

The Lean kernel checks the formal statements and proofs. Matching them to a
paper remains a mathematical review task, which is why the source map and
these scope distinctions are part of the deliverable.
