# Lean formalization of carrying-capacity mean-field models

**Status: partial formalization, with checked proofs and an explicit boundary.**
This project formalizes definitions and proof components from both
[DeWitt, Evans, Hiesmayr, and Hummel (2024)](https://arxiv.org/html/2307.06010v2)
and Kenny Xie's *Mean-Field Limits for Multitype Birth–Death Systems with
Unbounded Moment Feedback*
([manuscript source](https://github.com/bobashopcashier/Carrying_Capacity_fixed/blob/c7688113e4a92910b6403fdd8ecb14fb0f3ce6a9/new.tex)). It does **not** yet
prove either paper's complete stochastic theorem package, mean-field limit, or
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
**2,135 theorem declarations and 2,646 safe declarations across 135 modules**.
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
| [LyapunovFlowSpace](CarryingCapacity/LyapunovFlowSpace.lean) | Lower semicontinuity of genuine extended Lyapunov moments; closed complete moment sublevels and continuous-curve spaces; nonempty complete manuscript space with its exponential envelope | Preservation by the stochastic dynamics remains open |
| [BieleckiFlowSpace](CarryingCapacity/BieleckiFlowSpace.lean) | Exact exponentially weighted supremum metric, uniform equivalence, and completeness; Volterra integration gives contraction factor A/(λ−A); conditional unique fixed point for λ>2A | The invariant evolution map and its stochastic Volterra estimate are explicit inputs, not constructed here |
| [EmpiricalMeasure](CarryingCapacity/EmpiricalMeasure.lean) | Genuine finite empirical probability laws; exact integral identities; paired and permuted transport couplings; single-update estimate; generator bridge | Exact optimal matching is a separate result |
| [EmpiricalMatching](CarryingCapacity/EmpiricalMatching.lean) | Splits arbitrary couplings across repeated particle labels; Birkhoff decomposition; exact attained permutation optimum; measurable optimal matching preserving the empirical law | Randomized exchangeable initialization is supplied by `ExchangeableMatching` |
| [FiniteTransport](CarryingCapacity/FiniteTransport.lean) | Explicit common-mass coupling; transport bounded by diameter times total variation on a common finite support; atomic convergence implies transport convergence | Both laws must be concentrated on the same finite set |
| [EmpiricalLLN](CarryingCapacity/EmpiricalLLN.lean) | Full almost-sure Wκ convergence of empirical laws from measurable pairwise independent samples with a common finite-moment law; scalar, tail, and truncated strong laws | A fixed-law sampling theorem; uniform convergence of stochastic paths remains separate |
| [EmpiricalMeanError](CarryingCapacity/EmpiricalMeanError.lean) | Derived empirical Lyapunov expectations and uniform integrability; expected Wκ error tends to zero; error ≤2Mκ; time-integrated convergence under a uniform Lyapunov bound | The time theorem assumes jointly measurable samples and a continuous law curve; it does not construct the nonlinear process |
| [EmpiricalArrayError](CarryingCapacity/EmpiricalArrayError.lean) | Exact iid finite-vector laws; transfer of expected and time-integrated empirical transport convergence to N-dependent arrays, even on different probability spaces | Requires independence within each row at each fixed time; no independence across rows or times is imposed |
| [ExchangeableMatching](CarryingCapacity/ExchangeableMatching.lean) | Independent uniform common permutation of optimally matched arrays; exact preservation of both full vector laws; joint exchangeability; optimal cost and expectation identities; iid comparison specialization | Expected-error convergence is connected through explicit empirical-error hypotheses; process coupling remains separate |
| [InitialCoupling](CarryingCapacity/InitialCoupling.lean) | Full initial-coupling lemma: jointly exchangeable pairs with exact original and iid vector marginals, optimal integrable cost, and vanishing expected pairing cost, derived from convergence in probability and the expected empirical Lyapunov bound | Constructs initial joint laws; coupling the evolving processes remains separate |
| [Symmetrization](CarryingCapacity/Symmetrization.lean), [EmpiricalGenerator](CarryingCapacity/EmpiricalGenerator.lean) | Permutation equivariance; empirical equality iff relabeling; actual exchangeable symmetrization kernel; deterministic empirical state under that kernel; well-defined quotient generator and intertwining identity | Does not prove process exchangeability, the Markov mapping theorem, or Feller generation |
| [LyapunovTails](CarryingCapacity/LyapunovTails.lean) | Superlinear Lyapunov control gives uniform moment tails; genuine uniform integrability of empirical transport errors; in-probability initialization upgrades to expected-error convergence | Uses a common probability space and genuine integrability; does not supply the initial in-probability convergence assumption |
| [Framework](CarryingCapacity/Framework.lean) | Multitype birth/death/mutation maps; invalid-jump convention; generator linearity; distinct original TV and extended moment assumptions | Assumption structures record hypotheses; they are not the main theorems |
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
| [TimeGridRefinement](CarryingCapacity/TimeGridRefinement.lean), [PoissonCoordinateSum](CarryingCapacity/PoissonCoordinateSum.lean), [MarkedBoundedAlgebraLaw](CarryingCapacity/MarkedBoundedAlgebraLaw.lean), [MarkedPoissonMeasure](CarryingCapacity/MarkedPoissonMeasure.lean) | Finite Boolean rectangle refinement and product-Poisson aggregation; exact product law and joint independence for actual masses of every finite disjoint family of measurable finite-intensity planar sets | One fixed noise label; no infinite-intensity or simultaneous cross-label characterization is asserted by the final theorem |
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
| [CommonNoiseFiltration](CarryingCapacity/CommonNoiseFiltration.lean) | Genuine filtration of arrived labelled noise points; exact all-sample factorization of frozen paths through observed history; adaptedness, including initial information measurable at time zero | Full-past independence and predictable compensation are supplied by the modules above |
| [CommonFrozenStopping](CarryingCapacity/CommonFrozenStopping.lean) | Minimal augmentation of noise histories by ambient null sets; actual completed probability law; exact first exits are stopping times and measurable in the completed space, AE-measurable in the original space | No right-continuity or optional-stopping theorem is asserted; Lyapunov exit estimates are derived below from the proved Dynkin identity |
| [CommonInitialNoise](CarryingCapacity/CommonInitialNoise.lean) | Actual product of an arbitrary initial-record law and the full noise law; exact marginals and independence; prescribed initial-state law; joint measurability, adaptedness, and almost-sure càdlàg paths and stopped compatibility | Accepts constructed paired initial laws through measurable projections; Dynkin is supplied below, while trajectory comparison estimates remain open |
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
| [GlobalHistoryIntegral](CarryingCapacity/GlobalHistoryIntegral.lean), [ConfigurationMartingale](CarryingCapacity/ConfigurationMartingale.lean), [ConfigurationForwardEquation](CarryingCapacity/ConfigurationForwardEquation.lean) | All-sample raw-history reconstruction of time integrals; actual current-state generator martingale; integrated weak forward equation via proved sample-time Fubini | Finitely supported configuration tests and any independent initial probability law; no initial moment required; semigroup, strong Markov property, and forward-law uniqueness remain separate |
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
The final theorem states the exact product Poisson law of the genuine counting
measure masses and derives joint independence. Infinite-intensity sets and a
simultaneous cross-label characterization remain separate. Bounded future rectangle counts
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
integrated weak forward equation. These results need no initial moment. Forward-law
uniqueness, semigroup/strong Markov statements, optional sampling, and
time-dependent deterministic environments remain separate.

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

The quadratic coupling calculation includes the shared-jump contribution.
For a nonlinear κ, even a simultaneous birth can increase the distance;
controlling only unmatched jumps would miss this term.

## Remaining work for complete paper formalizations

1. Extend the proved finite-intensity planar-set characterization to
   infinite-intensity sets and simultaneous noise labels, and extend the
   proved bounded-rectangle independence from the full common
   marked past to joint future windows/categories within strips. Predictable
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
3. For the extension: deterministic-environment forward uniqueness, preservation
   of the Lyapunov curve space, and the stochastic Volterra estimate for the
   actual evolution map. The complete Bielecki space and conditional contraction
   and fixed-point argument are proved; the nonlinear flow is not yet constructed.
4. Derive localized process coupling, time-grid estimates, and path-space
   propagation of chaos from the proved initialization and empirical-error lemmas.

The Lean kernel checks the formal statements and proofs. Matching them to a
paper remains a mathematical review task, which is why the source map and
these scope distinctions are part of the deliverable.
