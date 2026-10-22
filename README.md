# Lean formalization of carrying-capacity mean-field models

**Status: partial formalization, with checked proofs and an explicit boundary.**
The current target is Kenny Xie's *Mean-Field Limits for Multitype Birth–Death Systems with
Unbounded Moment Feedback*
([manuscript source](https://github.com/bobashopcashier/Carrying_Capacity_fixed/blob/c7688113e4a92910b6403fdd8ecb14fb0f3ce6a9/new.tex)). It does **not** yet
prove either paper's complete stochastic theorem package, mean-field limit, or
propagation-of-chaos theorem. Existing results for
[DeWitt, Evans, Hiesmayr, and Hummel (2024)](https://arxiv.org/html/2307.06010v2)
are retained as shared infrastructure and separately documented coverage;
completing that original paper is not the current target.
The unproved conclusions are neither axioms nor hidden
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

The complete build passed without warnings, and the exhaustive audit checked
**3,281 theorem declarations and 4,081 safe declarations across 232 modules**.
These counts include private helpers and compiler-generated declarations;
they are not counts of distinct results from the papers. Separate negative
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
| [FiniteJumpForwardRestriction](CarryingCapacity/FiniteJumpForwardRestriction.lean), [NonlinearHorizonConsistency](CarryingCapacity/NonlinearHorizonConsistency.lean) | Restriction and coefficient/law congruence preserve genuine tested integrability; larger fixed curves restrict exactly to smaller fixed curves; actual environments and process marginal laws agree on overlapping horizons | Equality of laws is proved; sample-path consistency and a single nonlinear realization for all times are not asserted |
| [ParticleNoiseProjection](CarryingCapacity/ParticleNoiseProjection.lean), [ParticleInputRecords](CarryingCapacity/ParticleInputRecords.lean) | Exact full product law of particle initial/noise records; mutual independence; pointwise projected counting-measure identity; measurability in the raw shared history | Initial coordinates have the prescribed iid vector marginal; the rest of the paired initial record is unrestricted |
| [NonlinearParticleArray](CarryingCapacity/NonlinearParticleArray.lean), [NonlinearParticleContinuation](CarryingCapacity/NonlinearParticleContinuation.lean) | Actual independent nonlinear trajectories on the shared particle-noise space; full product marginals, raw adaptedness, simultaneous càdlàg and left-limit properties, actual initial values, integrable increments and all-horizon counting equations | Trajectory independence uses the coordinate sigma algebra, not a Skorokhod-space identification; the environment is endpoint-held after T |
| [CompactIntervalIntegration](CarryingCapacity/CompactIntervalIntegration.lean), [NonlinearParticleEmpirical](CarryingCapacity/NonlinearParticleEmpirical.lean) | Actual expected empirical error is genuinely integrable, bounded by twice the moment and terminal envelope, and tends to zero at fixed times and after real time integration | Applies to the constructed independent comparison array under the extension's assumptions; does not yet estimate its discrepancy from the interacting particles |
| [PredictableExitMask](CarryingCapacity/PredictableExitMask.lean) | Rational strict-past survival is raw predictable; actual right-local constancy identifies it with the inclusive genuine-exit mask; nonnegative compensation retains the exit jump | Generic compensation bridge; stopped interacting-particle running-cost estimates remain to be assembled |
| [DeterministicEnvironmentConfiguration](CarryingCapacity/DeterministicEnvironmentConfiguration.lean), [ConfigurationTimeDependent](CarryingCapacity/ConfigurationTimeDependent.lean), [NonlinearParticleConfiguration](CarryingCapacity/NonlinearParticleConfiguration.lean) | Actual interacting and prescribed-environment configurations use the same time-dependent construction; independent nonlinear coordinates equal the prescribed-environment configuration on one full-probability event, including positive-time pre-states | Identification preserves the actual common noise; full population convergence remains separate |
| [ExitTimeMeasurability](CarryingCapacity/ExitTimeMeasurability.lean), [StoppedPathMeasurability](CarryingCapacity/StoppedPathMeasurability.lean) | Actual exit attainment and AE measurability; jointly AE measurable stopped paths and measurable versions of their uncountable running costs | Derived from the actual joint path measurability and right-local constancy; no raw stopping-time or usual-filtration assertion |
| [SynchronousStoppedCompensation](CarryingCapacity/SynchronousStoppedCompensation.lean), [SynchronousStoppedRunningSupremum](CarryingCapacity/SynchronousStoppedRunningSupremum.lean) | Compensation through the genuine joint exit and actual stopped expected-supremum inequality; the exit jump is retained | Extended expectations may initially be infinite; later population integrability is derived below |
| [PopulationCouplingAlgebra](CarryingCapacity/PopulationCouplingAlgebra.lean), [PopulationStoppedCoupling](CarryingCapacity/PopulationStoppedCoupling.lean), [PopulationStoppedIntegrability](CarryingCapacity/PopulationStoppedIntegrability.lean) | Exact coordinate activity averaging and moment decomposition; actual stopped population inequality, AE measurability, finite expectation, and real integrability with no assumed stochastic comparison | Constants are independent of N; the sharp stopped Gronwall estimate and Proposition 5.3's limit remain to be assembled |
| [GlobalLyapunovExit](CarryingCapacity/GlobalLyapunovExit.lean), [PopulationCouplingExit](CarryingCapacity/PopulationCouplingExit.lean), [PopulationCouplingRemoval](CarryingCapacity/PopulationCouplingRemoval.lean) | Actual whole-horizon joint-exit probability bounded by C/R with an N-independent constant under uniform initial moments; exact stopped/unstopped agreement and Markov cutoff-removal estimate | Supplies the tail and event bounds, not the final population limit or focal comparison |
| [IntegrableGronwall](CarryingCapacity/IntegrableGronwall.lean) | Forced exponential comparison for merely integrable subsolutions and nonnegative integrable forcing | The actual stopped population subsolution must still be connected to this deterministic result |
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
| [CommonInitialNoise](CarryingCapacity/CommonInitialNoise.lean) | Actual product of an arbitrary initial-record law and the full noise law; exact marginals and independence; prescribed initial-state law; joint measurability, adaptedness, and almost-sure càdlàg paths and stopped compatibility | Accepts constructed paired initial laws through measurable projections; Dynkin is supplied below, while interacting-particle versus nonlinear trajectory comparison remains open |
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
continuity. Its formulation on an arbitrary supplied PRM space with a completed
right-continuous filtration remains separate.

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
actual process marginals agree throughout the overlap. This is law consistency;
sample-path consistency and a single nonlinear realization across all horizons
remain separate, as does realization on arbitrary externally supplied PRM spaces.

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
`NonlinearParticleEmpirical` derives genuine error and time integrability and
proves the actual time-integrated independent empirical error tends to zero.
`PredictableExitMask` proves compensation up to and including a genuine exit
using a raw predictable rational-history version. It does not discard the
exit jump or assume a completed-filtration compensation theorem.

The quadratic coupling calculation includes the shared-jump contribution.
For a nonlinear κ, even a simultaneous birth can increase the distance;
controlling only unmatched jumps would miss this term.

## Remaining work for complete paper formalizations

1. Extend the proved bounded-rectangle independence from the full common
   marked past to joint future windows/categories within strips. Arbitrary
   measurable-set Poisson laws, infinite-intensity masses and simultaneous
   cross-label laws are already proved. Predictable
   compensation is proved from the scalar independence and intensity, without
   requiring this stronger joint law. Dynkin's expectation identity is also
   proved for the actual frozen construction. Lyapunov expectation and exit
   estimates, almost-sure exhaustion, finite-activity global patching and the
   global moment bound are proved for the actual initial-record/noise product
   construction, including the empirical particle model. The unrestricted global
   counting equation, pathwise uniqueness, finite-support generator martingale,
   and weak forward equation are proved. These path and finite-support results
   now allow arbitrary independent initial laws. The usual right-continuous
   filtration, optional sampling, and Markov/semigroup statements remain separate.
2. For the original theorem: Feller generation, the Markov empirical process,
   Yule domination, tightness, and convergence under its weaker initial data.
   Its actual finite-N nonexplosive construction and coordinate-equation
   pathwise uniqueness now follow directly from the original assumptions.
3. For the extension: establish sample-path compatibility of the canonical
   nonlinear realizations across horizons and a single nonlinear process for all
   times, then extend realization to arbitrary externally supplied PRM spaces.
   General-environment output-law Wκ continuity, full moment-bounded nonlinear
   law uniqueness, the exact envelope and consistency of laws across horizons
   are proved. The completed right-continuous filtration formulation remains
   separate from the proved raw-history and completion results.
4. Derive the stopped interacting-particle running-cost estimate, remove
   localization using the uniform exit bounds, and prove time-grid convergence
   and path-space propagation of chaos. The actual independent nonlinear array,
   exact shared-noise identities, its time-integrated empirical-error limit,
   and inclusive exit-mask compensation are now proved. These ingredients have
   not yet been assembled into the interacting-particle comparison theorem.

The Lean kernel checks the formal statements and proofs. Matching them to a
paper remains a mathematical review task, which is why the source map and
these scope distinctions are part of the deliverable.
