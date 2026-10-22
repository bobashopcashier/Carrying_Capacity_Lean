# Sources and formalization boundaries

This inventory distinguishes the two papers and the deterministic lemmas from
stochastic theorems that are not yet formalized. A theorem mentioned here is
not a Lean theorem merely because it appears in this document.

## Sources

- Original: DeWitt, Evans, Hiesmayr, and Hummel, *Mean-field interacting multi-type
  birth-death processes with a view to applications in phylodynamics*,
  [arXiv:2307.06010v2](https://arxiv.org/html/2307.06010v2), 1 April 2024;
  published DOI [10.1016/j.tpb.2024.07.002](https://doi.org/10.1016/j.tpb.2024.07.002).
  The assumptions and main conclusions below were checked against the primary
  arXiv version, rather than inferred from the local transcription.
- Extension: Kenny Xie, *Mean-Field Limits for Multitype Birth–Death Systems with
  Unbounded Moment Feedback*,
  [paper repository](https://github.com/bobashopcashier/Carrying_Capacity_fixed/tree/c7688113e4a92910b6403fdd8ecb14fb0f3ce6a9),
  `new.tex`, source version `c768811`. Section paths below refer to that paper
  repository, not this standalone verification repository. The attached
  `new.pdf` is byte-identical to the paper repository's `new.pdf`: SHA256
  `cf1d663ae6fd9b72038a37f07a6bcb52aceed59d7ccfe089aa066240835660e5`.

## Original-paper inventory

The original Assumption 2.1 imposes lineage-linear growth uniformly over laws,
and a global Lipschitz bound using state distance plus total variation.
Rates vanish when the relevant source-type count is zero. Rates do not depend
on the number of lineages.

| Original result | Content | Full stochastic proof status |
|---|---|---|
| Proposition 2.3 | Feller semigroup and finitely-supported generator core | Not formalized |
| Proposition 2.4 | Exchangeability and Markov empirical process | Symmetrization kernel and generator intertwining proved; full process statement remains open |
| Theorem 2.5 | Deterministic nonlinear forward law and empirical path convergence | Not formalized |
| Remark 2.6; Corollary 2.7 | Fixed-time and path-space propagation of chaos | Not formalized |
| Lemmas 3.1–3.3; Propositions 3.5, 3.7–3.9; Lemmas 3.11–3.12 | Symmetrization, domination, freezing, tightness | Algebraic symmetrization and marked frozen paths partly formalized; domination, process-law identification, and tightness remain open |

Theorem 2.5 starts from a uniformly symmetrized deterministic empirical law
converging weakly. It does **not** assume the extension's uniform Lyapunov
moments. Remark 2.2 motivates moment-dependent rates. Section 4 discusses
moment-mediated examples; Example 4.2 notes a truncation requirement.
[Primary source, Sections 2–4](https://arxiv.org/html/2307.06010v2#S2).

## Extension definitions and theorem inventory

The following numbered results refer exclusively to Xie's manuscript, not to
the original paper's numbering.

| Source location | Exact objects or result | Required formal ingredients |
|---|---|---|
| `sections/04_wasserstein_model_and_theorem.tex:10` | `E = ℕ₀ᴰ`; κ(0)=0; κ(n+1)−κ(n)≥1; Kκ=sum of coordinate κ values; Mκ=integral Kκ; ρκ=sum of absolute transformed-coordinate differences; Wκ=infimum coupling cost | Discrete geometry; integrals; probability couplings; infima |
| same file, Remark 2.1 | Wp^p≤Wκ and Wκ≤p(Mκ(μ)^((p−1)/p)+Mκ(ν)^((p−1)/p))Wp | Real powers, Hölder, transport couplings |
| same file, lines 103–153 | Admissible birth/death/type-transition maps; single and empirical generators; positive-increment coupling cost Cκ | Finite sums and admissibility |
| same file, Assumptions 2.2–2.6 | Weighted synchronous bound; weighted activity; superlinear Lyapunov drift; exchangeable initialization | Exact hypotheses, not consequences |
| Theorem 2.7 | Non-explosive strong finite systems; unique nonlinear flow in the moment class; uniform empirical and moment convergence; fixed-focal path chaos | All subsequent stochastic infrastructure |
| `sections/05_lyapunov_and_tightness.tex`, Lemmas 3.1–3.2 | Frozen Poisson construction and compatibility, including the exit jump | PRM local finiteness and deterministic recursion |
| same file, Proposition 3.3 | Stopped Lyapunov and exit estimates uniform in the level | Compensation, Dynkin, stopping times, Gronwall |
| same file, Proposition 3.4 | Patch frozen paths into unique global strong non-explosive paths | Compatibility, almost-sure exhausting exit times, path measurability |
| same file, Lemma 3.5; Corollary 3.6 | Weighted activity before stopping; unstopped expected moment and exit bounds | Finite algebra, Fatou, monotone exit events |
| `sections/06_limit_identification.tex`, Lemma 4.1 | Running maximum bounded by positive jump increments in expectation | Deterministic inequality and PRM compensation |
| same file, Proposition 4.2 | Non-explosive chain in a deterministic environment and uniqueness of its linear forward law | PRM construction; jump kernel; last-jump iteration |
| same file, Theorem 4.3; Corollary 4.4 | Invariant Lyapunov envelope, Bielecki contraction, nonlinear law and strong realization | Complete Wasserstein flow space; Banach contraction; full-class uniqueness |
| `sections/07_wasserstein_uniqueness.tex`, Lemmas 5.1–5.2 | Exchangeable optimal initial pairing and integrated independent empirical error | Uniform integrability; finite optimal matching; iid transport LLN |
| same file, Proposition 5.3; Theorem 5.4 | Localized coupling estimate, removal of stopping, focal comparison | Positive increments, averaged coefficients, compensation, two-stage limits |
| `sections/08_path_space_chaos.tex`, Lemma 6.1; Proposition 6.2 | Expected metric variation and uniform iid empirical convergence | Compensation, fixed-grid LLN, mesh refinement |
| same file, Theorem 6.3; Corollary 6.4 | Uniform empirical path limit and fixed-focal chaos | Coupling transfer, path topology, independence |
| `sections/09_carrying_capacity_corollary.tex`, Proposition 7.3; Corollary 7.4 | Linear-moment carrying-capacity hypothesis verification and application | Rate algebra, Lyapunov powers, main theorem |
| same file, Proposition 7.5 | Uniform first-moment convergence and globally well-posed closed mean ODE | Coupling moment estimate; unbounded-test justification; ODE invariance |
| same file, Proposition 7.7; Corollary 7.8 | Quadratic-feedback activity/coupling/Lyapunov checks and mean-field application | Piecewise birth/death algebra; higher moment; main theorem |

The initial-coupling assertion of Lemma 5.1 is supplied by
`InitialCoupling.exists_initial_coupling`. The independent empirical-error
conclusions of Lemma 5.2 are supplied for measurable iid arrays and a continuous
law curve with the required Lyapunov bound by `EmpiricalArrayError`; constructing
those processes and that curve remains separate. Proposition 3.3's actual
frozen Lyapunov expectation and reciprocal exit estimates are now proved,
including their empirical configuration specialization. The exhaustion,
measurable adapted patch, cadlag regularity and finite activity parts of
Proposition 3.4 are proved, as is the unrestricted test-function counting equation
for the constructed global path. The global Lyapunov expectation part of Corollary 3.6
follows by Fatou. Global equation pathwise uniqueness is proved, including the
particle-coordinate formulation. The actual finite-support generator martingale
and integrated weak forward equation are proved. Countability also removes the
initial-moment premise from nonexplosion and these finite-support conclusions.
Weighted-activity estimates and the nonlinear/mean-field statements remain open.

## Dependency order

1. Define the state, jump maps, empirical averages, rate data, adapted metric,
   and probability moment with the paper's domain and integrability conditions.
2. Prove deterministic metric, generator, finite-state, and rate inequalities.
3. Construct frozen PRM-driven processes; prove measurability, adaptedness,
   local finite activity, compatibility, Dynkin, and Lyapunov exit estimates.
4. Deduce almost-sure exhaustion and apply deterministic path patching.
5. Construct deterministic-environment laws and prove linear forward uniqueness.
6. Establish the invariant moment envelope, Wasserstein completeness, and
   Bielecki contraction; then prove uniqueness in the entire moment-bounded class.
7. Formalize initial matching, uniform-integrability upgrades, empirical LLNs,
   localized population coupling, and the successive N-then-R limit.
8. Formalize the time-grid argument, Skorokhod transfer, and independence of
   fixed collections; assemble the main theorem and model corollaries.

The original proof has a different route through Feller generation, Markov
mapping, Yule domination, frozen-process convergence, and tightness. Its weaker
initial assumptions require separate treatment; adding moments is a restricted
corollary, not a formalization of the original theorem as stated.

## Current Lean coverage

All paths below are relative to `CarryingCapacity/`. These are proved
subresults and explicit definitions, not replacements for the full stochastic
statements listed above. The project build and axiom audit should be rerun after
any subsequent edits.

| Module | Implemented mathematical coverage | Boundaries |
|---|---|---|
| `MomentGeometry.lean` | Discrete κ normalization; linear/quadratic scales; metric axioms for ρκ; Kκ and coordinate bounds; finite state and Lyapunov sublevels | Does not prove completeness of the law space or the Wp comparison of Remark 2.1 |
| `Transport.lean` | Genuine probability measures with integrable Kκ; all measure couplings with their probability property; independent/diagonal/swapped couplings; integrability of every coupling cost; the infimum Wκ with zero self-distance and symmetry; moment difference bounded by Wκ; moment convergence from Wκ convergence | Metric and completeness are proved in the following modules; arbitrary-law optimal-plan existence remains open |
| `TransportMetric.lean` | Actual conditional-kernel gluing; cost triangle; separation by indicator tests; MetricSpace; Lipschitz moment and event-probability maps | No arbitrary-law optimal coupling theorem |
| `TransportCompleteness.lean` | Actual Ionescu–Tulcea simultaneous coupling of near-optimal consecutive plans; a.s. finite total path distance; measurable finite-moment limit law; tail transport bound; CompleteSpace instance | Does not construct nonlinear laws |
| `LyapunovFlowSpace.lean` | Genuine extended Lyapunov integral; lower semicontinuity from continuous atomic masses; finite bounds imply integrability; closed complete moment sublevels and uniform-metric curve spaces; nonempty complete manuscript space with its exact exponential envelope | Preservation by the evolution remains open; weighted completeness is supplied below |
| `BieleckiFlowSpace.lean` | Exact weighted supremum metric; exp(−λT)d_uniform≤d_λ≤d_uniform; explicit uniform equivalence and completeness; actual Volterra-kernel integration gives A/(λ−A); conditional unique fixed point for λ>2A | Matches the analytic argument in Section 4; takes an independently supplied invariant map and its Volterra estimate as inputs, so does not construct the nonlinear flow |
| `EmpiricalMeasure.lean` | Empirical probability/MomentLaw constructions; test integrals; paired and permuted couplings; Wκ upper bound; update estimate; exact empirical-integral generator and Lyapunov identities | No process law follows from the generator algebra alone |
| `EmpiricalMatching.lean` | Repeated-state mass splitting; doubly stochastic label plan preserving transport cost; Birkhoff decomposition; Wκ equals attained minimum over permutations; measurable selected matching with exact empirical law and cost | Randomized joint exchangeability is supplied by `ExchangeableMatching` |
| `FiniteTransport.lean` | Explicit diagonal common mass and normalized residual-product coupling; exact marginals; Wκ ≤ diameter times half the sum of absolute atomic mass differences; transport convergence from atomic convergence on fixed finite support | Finite-support comparison, not an arbitrary-law optimal-plan theorem |
| `EmpiricalLLN.lean` | Full almost-sure empirical Wκ convergence from measurable pairwise independent identically distributed samples and a finite κ moment; scalar, moment, singleton, tail, and truncated strong laws; finite Ψ gives a MomentLaw | Fixed-law convergence; no uniform-in-time path theorem |
| `EmpiricalMeanError.lean` | Common marginals imply exact empirical Ψ expectations; derived uniform integrability and expected Wκ convergence; βN≤2Mκ; jointly measurable errors and time-integrated convergence under a continuous law curve and uniform Ψ integral bound | Uses initial segments of an infinite sample family; the finite-array transfer is supplied below |
| `EmpiricalArrayError.lean` | Constructed canonical iid sequence; exact finite-vector product law; empirical errors are identically distributed with canonical errors; integrability, βN≤2Mκ, expected-error limit and time-integrated limit for arbitrary N-dependent iid arrays | Matches the independent empirical-error conclusions of Lemma 5.2; assumes measurable samples and continuous target laws, and does not construct nonlinear trajectories |
| `ExchangeableMatching.lean` | Actual law obtained from optimal matching and an independent uniform common permutation; preservation of both full exchangeable vector laws; joint paired exchangeability; exact optimal cost; cost distribution, integrability and expectation identities; iid-target specialization | Supplies the finite-population construction used by the fully assembled initial lemma below |
| `InitialCoupling.lean` | Lemma 5.1: exact original and iid full-vector marginals, joint exchangeability, integrable optimal cost, and expected cost tending to zero, derived from probability convergence and the uniform expected empirical Ψ bound | Produces coupling laws on paired arrays; `CommonInitialNoise` supplies independent future noise, while stochastic trajectory comparison remains open |
| `Symmetrization.lean` | Generator equivariance; uniform permutation average; equal empirical measures iff a relabeling exists; genuine exchangeable symmetrized measure with deterministic empirical state | Stochastic exchangeability still needs process construction and uniqueness |
| `EmpiricalGenerator.lean` | Countable space of actual empirical measures; representative-independent symmetrization Markov kernel; pushforward is the prescribed Dirac law; quotient generator; Bα=αA intertwining | Does not assert the empirical process is Markov or supply a Feller semigroup |
| `LyapunovTails.lean` | Actual uniform integral tails from superlinear Ψ; affine-envelope uniform integrability; empirical-transport in-measure to L1 upgrade using expected empirical Ψ bound | Common probability space; explicit integrability is required to avoid totalized-integral loopholes; the initial in-probability convergence is an input |
| `Framework.lean` | Correct birth/death/type-transition maps, boundary rates, generators; original total-variation growth/Lipschitz assumptions; extension's positive-increment coupling, activity, and Lyapunov hypotheses | These are assumption structures, not proofs that arbitrary rates satisfy them; initialization and full nonlinear forward equation are not encoded |
| `FiniteGenerator.lean` | Exact 1/N empirical-generator identity and averaged Lyapunov drift | The empirical-law interpretation is proved in EmpiricalMeasure; Dynkin and process expectation bounds remain separate |
| `RateControl.lean` | Admissible jumps have ρκ-length at least one; total rate ≤ weighted activity; empirical Lyapunov sublevels of N-lineage configurations are finite for N>0 | Does not yet construct a finite-strip PRM event list or derive its stochastic properties |
| `Freezing.lean` | Finite proposal recursion, retention of exit jump, permanent freezing, compatible path patching, a.e. exhaustion from reciprocal exit tails, a.e. unique pointwise patch | No PRM construction, derivation of exit bounds, or measurability/adaptedness of the patched process |
| `CountableJumpProcess.lean` | Independent exponential waiting times on an infinite product; a.s. positive waits and strictly increasing divergent arrivals; measurable arrival counting measure; a.s. finite mass on bounded time intervals | Distributional count identities are supplied below |
| `FrozenProcess.lean` | Actual independent iid uniform labels and thinning marks; measurable recursion and time evaluations from deterministic initial states; finite range; right continuity and left limits a.s.; permanent freezing | No filtration/adaptedness, compensator, or compatibility across different clock rates |
| `PoissonClockLaw.lean` | Survival multiplication, conditional residual exponential law, and exact zero-count probability | Not the complete Poisson-process characterization |
| `PoissonIncrements.lean` | Actual shifted-clock law; independent head and tail; nonatomic arrivals; derived count renewal recurrence and its evaluated integral; count pushforward equals Poisson(rt) for every t≥0 | One-time marginals alone do not establish independent increments |
| `PoissonRestart.lean` | Whole-clock conditional survival restart, renewal recurrence for two counts, exact joint count masses, product count/increment pushforward, stationary increment law, and independence from the starting count | These two-variable identities alone do not establish full finite-grid independence or independence from the past filtration |
| `PoissonFiniteDimensional.lean` | Full finite-profile renewal induction; exact joint atom probabilities; actual product Poisson pushforward and mutual independence of conventional increments on every finite monotone grid, allowing repeated times and arbitrary nonnegative starting time | Full-past independence and the scalar compensated martingale are supplied below; marked law identification remains separate |
| `PoissonMoments.lean` | Weighted Poisson mass series, finite extended first moment, genuine integrability, and exact means for actual clock counts and increments | These are derived distributional moments, not an assumed intensity or compensator |
| `PoissonTransform.lean` | Absolute convergence and integrability of the complex Poisson power series for every complex argument; exact transforms under Poisson laws and actual clock count/increment laws; arbitrary finite-product transform | These formulas do not by themselves establish independence from a filtration |
| `CountVectorTransform.lean` | Equality of power integrals on the unit torus determines finite measures on natural-valued vectors, through an injective Euclidean embedding and characteristic-function uniqueness | Includes dimension zero; finite measures and equality of transforms are explicit hypotheses |
| `PoissonSuperposition.lean` | Finite sums of independent vectors with product Poisson laws have product Poisson laws with summed coordinate parameters; exact transform and integrability for all complex arguments | Independence is between complete vectors, not merely pairwise counts; component laws and independence must be supplied |
| `PoissonPastIndependence.lean` | Full past-count sigma algebra built from directed finite observation families; actual future increment independent of that entire past; natural-filtration identification; conditional increment expectation r·t | Raw scalar clock filtration only; the marked noise has a larger observation history and still needs its own independence proof |
| `PoissonMartingale.lean` | Actual compensated count N_t−rt is a martingale on nonnegative times; integrability, adaptedness, zero conditional increments and zero mean; deterministic-horizon stopped martingale | Does not assert random optional sampling or a compensator for the marked counting measure |
| `MarkedNoise.lean` | A single actual probability space and measurable counting-measure family from independent unit vertical strips; a common probability-one event gives local finiteness for every real time/height cutoff and no simultaneous arrivals | Full marked PRM characterization remains separate; predictable compensation is supplied below |
| `MarkedIntensity.lean` | Actual mark/clock product probabilities, count expectations, translated uniform-strip decomposition, and exact expected counting measure equal to quadrant Lebesgue measure; full nonnegative deterministic Campbell identity and expected mass of every measurable set | First-moment identities do not establish the full marked Poisson law, past independence, or predictable random-integrand compensation |
| `MarkedProducts.lean` | Finite iid uniform-mark product integrals; measurable and integrable actual clock products for bounded factors; Fubini reduces their expectation to the clock expectation of a power of the single-mark mean | One common horizon; does not assert a formula for random predictable integrands |
| `MarkedStripCounts.lean` | Measurable natural-valued category prefix and window counts, finite disjoint-union additivity, and a.s. identification with genuine translated strip-measure rectangle and time-window masses; common counting measure equals the sum of strip counts | Time-window mass identification is pathwise and is not a time-increment distribution theorem |
| `MarkedThinning.lean` | Scalar count-law uniqueness from complex power integrals; derived Poisson law for every measurable category of an actual strip at T≥0, with rate T times its uniform-mark probability | One category and one horizon, including zero intensity; mutual independence requires a joint law |
| `MarkedSplitting.lean` | Derived multivariate transform, product Poisson law, and mutual independence for finitely many disjoint measurable categories at one common horizon in an actual strip; transfer to genuine translated strip masses | Disjointness is required among height categories; the strip's joint time-window law is supplied below |
| `MarkedBlockProducts.lean` | Actual iid law of finite distinct mark coordinates; exact integrals of coordinate-dependent products over pairwise disjoint finite index sets; consecutive blocks by lengths or monotone endpoints, including arbitrary offsets and empty blocks | Deterministic index sets; random time blocks require the clock and Fubini connection below |
| `MarkedTimeCounts.lean` | Measurable natural-valued index, window, and grid count arrays; prefix differences equal block counts; actual mark blocks are pairwise disjoint on the full-measure locally finite clock event; block lengths equal clock increments; translated strip-grid masses agree with counts a.s. | No distributional independence is assumed or concluded by these pathwise identifications alone |
| `MarkedTimeProducts.lean` | Measurability and integrability of actual random time-block products for measurable factors of norm at most one; exact exponential transform from deterministic block integration and the full clock increment law | Finite monotone grids with nonnegative starting time and deterministic per-window factors; no predictable compensation |
| `MarkedGridLaw.lean` | Actual multivariate transform and product Poisson law for all strip window/category counts on a finite monotone grid; arbitrary finite category type, varying categories per window, repeated times and arbitrary nonnegative first time | Requires measurable categories disjoint within each window; categories may overlap across different windows; the full common-noise bounded-height grid extension is supplied below |
| `MarkedBoundedCounts.lean` | On one probability-one event, actual common-noise prefix and window masses below a strict natural height cutoff equal finite sums of strip counts for all measurable categories and ordered nonnegative endpoints; finite sums of category probabilities equal positive Lebesgue mass | Negative-height portions have zero mass; no independence or distribution is asserted by this module alone |
| `MarkedRectangleLaw.lean` | Complete category vectors from actual distinct strips are independent; finite superposition gives the product Poisson law for bounded-height category counts and for the genuine rectangle masses embedded in extended nonnegative reals | One fixed label j, a common horizon T≥0, and pairwise disjoint measurable Bᵢ⊆(−∞,m); the grid extension is supplied below, while general finite-intensity planar sets are supplied below; bounded future-rectangle independence is supplied below |
| `MarkedGridRectangles.lean` | Entire actual strip grid vectors are independent across strips; finite superposition gives the full product Poisson law for bounded window/category arrays and the genuine common counting-measure grid-rectangle masses embedded in extended nonnegative reals | One fixed label j, finite monotone grid u with u₀≥0, measurable B[a,i]⊆(−∞,m) for a common natural m, and category disjointness within each window; parameters are Δuₐ times positive Lebesgue mass; arbitrary finite-intensity planar sets are supplied below; joint future-grid independence from the past remains separate |
| `MarkedSetCounts.lean`, `PoissonLawLimit.lean`, `MarkedSetPoissonLimit.lean` | Actual natural-valued finite-intensity counts; exact expectation and symmetric-difference discrepancy bound; summable approximations give AE eventual equality and full-vector Poisson-law limits | Target-law independence is never assumed; approximating laws are supplied by the later application |
| `FiniteDisjointApproximation.lean`, `MarkedRectangleAlgebra.lean`, `MarkedBoxApproximation.lean`, `MarkedAlgebraExtension.lean` | Disjointification with controlled errors; dense lower-box algebra; summable bounded-box approximation; extension to arbitrary measurable finite-intensity disjoint families | Pure geometric approximation and law extension |
| `TimeGridRefinement.lean`, `PoissonCoordinateSum.lean`, `MarkedBoundedAlgebraLaw.lean`, `MarkedPoissonMeasure.lean` | Finite Boolean rectangle decomposition on a monotone time grid; product-Poisson summation; exact product law and joint independence of genuine random-measure masses on any finite disjoint measurable family of finite intensity | Fixed noise label; infinite-intensity sets, simultaneous cross-label characterization, and future-vector independence from raw histories remain separate |
| `NullAugmentedIndependence.lean` | Exact independence survives ambient-null augmentation on either or both sigma algebras and passage to the completed ambient measure; measurable functions of augmented independent histories are independent | Augmentation uses the original ambient law, not its trim to the smaller history; no filtration right-continuity claim |
| `ClockPastObservation.lean` | Actual censored arrivals and arrival masks are measurable in the augmented full count history; raw count masks are measurable and match arrival masks a.s.; the next count increment is independent of the augmented history | Exact exceptional samples are retained; nonnegative deterministic observation and future-window times |
| `MarkedPastProducts.lean` | Distinct past mark factors and future deterministic index blocks have factorized integrals; unarrived past coordinates contribute constants; unit bounds give genuine integrability | No stopped-index independence hypothesis; arbitrary empty blocks are included |
| `MarkedObservation.lean` | Actual full pair-valued censored strip observations; measurable bounded finite products; explicit clock means; exact mark integration; good-clock past/future factorization; clock means measurable in the augmented count past | The observable retains arrival times and marks, not merely aggregate counts |
| `MarkedPastTransform.lean` | Genuine strip-product Fubini and the proved augmented-clock independence yield factorization of finite observed-past products against a future-window mark transform | One deterministic future window with a deterministic measurable mark factor; no random predictable integrands |
| `CountRestriction.lean` | Weighted complex-power transforms identify the actual restricted natural-count pushforward and event probabilities, including zero-mass conditioning events | A generic implication from an explicit transform identity; no division by the conditioning probability |
| `CylinderIndependence.lean` | Finite intersections of coordinate events generate independence of the full product-valued observation; arbitrary observation index type is allowed | Explicit finite-cylinder event-factorization hypotheses are discharged for the actual strip in the next module |
| `MarkedPastIndependence.lean` | Actual future strip-category counts have the Poisson law with parameter t times uniform-mark category probability and are independent of the full censored indexed strip history; exact restricted cylinder laws precede the pi-system extension | One strip and one future category-count variable; the common-noise lift is supplied below, while joint future windows/categories within a strip remain separate |
| `IndependentProductHistory.lean` | Exact masses of paired finite cylinders under the actual infinite product law; coordinatewise observation/future independence implies independence of the entire two arrays | Arbitrary index and dependent sample types; requires only measurable coordinate functions and the stated per-coordinate independence |
| `CommonMarkedPastIndependence.lean` | Complete strip-observation and future-count arrays are independent; an exact guarded height translation recovers the existing common view; finite sums and a.s. mass identification give independence of actual bounded future rectangle masses from the full raw and completed common-noise histories | One deterministic future window and one category per strip; the stronger joint future law within a strip remains separate |
| `InitialMarkedPastIndependence.lean` | Genuine independence of actual bounded future rectangle counts from the whole independent initial record and marked past, including completed histories | One deterministic future window and bounded category |
| `MarkedCountMoments.lean`, `MarkedCountAdapted.lean`, `MarkedCountMartingale.lean` | Actual mass finiteness before conversion to real values, first moments and integrability, full-history adaptedness, conditional means and compensated-count martingale | Raw common-noise filtration and bounded measurable height categories |
| `MarkedElementaryCompensation.lean`, `InitialElementaryCompensation.lean` | Exact weighted future-count and step-integrand formulas, including null-augmented initial-product histories | No integrability assumption on nonnegative coefficients; full extension below uses raw histories |
| `PredictableSets.lean`, `PredictableCompensation.lean` | Positive-time predictable sigma algebra; genuine Campbell measure from actual point pushforwards; finite-box measure uniqueness and zero nonpositive-time mass; full nonnegative predictable compensation | Proved from actual rectangle identities, not an assumed compensator |
| `MarkedCountingKernel.lean`, `PredictableIntegral.lean` | Actual s-finite counting kernel and composition product; Bochner Fubini; equivalence of predictable integrability and compensation for signed or vector integrands | Explicit product-integrability hypothesis; frozen Dynkin is supplied below |
| `InitialPredictableCompensation.lean` | Every fixed-initial section is noise-predictable; Tonelli lifts full nonnegative compensation to the actual initial-product law | Raw initial-product predictable sigma algebra; no completed-section measurability shortcut |
| `FrozenCompatibility.lean` | Actual first-exit indices for nested frozen recursions; agreement including the exit jump; monotone exit indices; stopped larger recursion equals the permanently frozen smaller one; stopped continuous-time agreement under a common clock | Uses the same decoder and proposal sequence; cutoff-list compatibility is supplied below |
| `ChronologicalEvents.lean` | Measurable finite-set selection and chronological sorting; jointly measurable actual bounded-box event lists; exact membership and strict ordering; time-prefix and height-filter identities simultaneously for all boxes almost surely | Does not by itself identify the stochastic intensity of the counting measure |
| `RejectedProposals.lean` | Removing proposals rejected at every active state preserves the actual frozen recursion, including its accepted exit jump; height-bound specialization | Deterministic list identities, used to compare actual bounded-box paths |
| `CommonFrozenProcess.lean` | Frozen paths defined from the shared marked noise's chronological events; joint measurability and finite-range confinement; almost-sure bound independence, permanent freezing, and continuous-time nested-set agreement through the exit jump | Autonomous rates on a countable state space with finitely many directions; counting and generator identities are supplied below |
| `CommonFrozenRegularity.lean` | Almost-sure local right constancy and left constancy, càdlàg regularity, zero-time value and initial interval for all cutoffs and initial states | These path properties do not identify compensation or prove adaptedness |
| `CommonFrozenExit.lean` | Genuine extended first-exit infimum and pre-exit membership; almost-sure finite attainment, zero/infinite boundary cases, nested-exit monotonicity, and stopped larger path equals smaller path including its exit jump | Exit probability estimates and stopping-time properties are supplied below |
| `CommonNoiseFiltration.lean` | Actual observation filtration from arrived labelled marks, independent of the process; monotonicity and ambient measurability; all-sample history factorization; measurable time evaluations and adaptedness for deterministic or time-zero-measurable initial states | No full-σ-algebra shortcut or process-generated filtration; marked-future independence and predictable compensation are proved in dedicated modules |
| `CommonFrozenStopping.lean` | Actual completed ambient probability law; minimal augmentation of each raw history by ambient null sets; exact original first exit is a stopping time, completed-measurable and raw AE-measurable; raw time-zero-measurable initial states included | Infinity uses only the supremum of finite histories; right continuity and optional sampling are not claimed; the arbitrary-initial product extension is supplied below |
| `CommonInitialNoise.lean` | Actual arbitrary initial-record/noise product law, exact full marginals and independence, including measurable initial-state maps; initial-plus-observed-noise filtration; exact process initial law; joint measurability, adaptedness, and almost-sure regularity and stopped compatibility | Accepts the paired-array laws from Lemma 5.1; frozen generator identification is supplied below, while trajectory coupling estimates remain open |
| `CommonInitialStopping.lean` | Minimal augmentation of the actual initial-record/noise product histories by ambient product-law null sets; actual completed law; exact first exit is a stopping time, completed-measurable and raw AE-measurable; truncated exits are history-measurable and the initialized paths remain adapted | The terminal sigma algebra is the supremum of finite nonnegative histories; no right continuity, optional sampling, predictable compensation, or Lyapunov exit estimate is asserted |
| `PredictableStepApproximation.lean`, `FrozenPredictableIntegrand.lean`, `InitialFrozenPredictable.lean` | Strict-past grids and measurable limit versions; genuine predictable pre-jump state and marked test-function increments; common-event identification with actual left limits for base and initial-product paths | Exceptional paths need no regularity hypothesis; a fixed nonpositive-time fallback preserves predictability |
| `FrozenJumpIdentity.lean`, `FrozenCountingIdentity.lean`, `InitialFrozenCountingIdentity.lean` | Actual chronological telescoping, finite atomic integrability and signed test-function counting equation, retaining the exit jump; actual initialized equation follows by the common-event lift | Finite cutoffs and autonomous rates; no assumed stochastic integral equation |
| `FrozenIntensity.lean`, `FrozenGeneratorIntegral.lean` | Finite active-set increment bound and finite-box product integrability; exact height integration and time-integrated frozen generator identification | Active rates nonnegative and dominated by the height cutoff for drift identification |
| `FrozenCompensation.lean`, `InitialFrozenCompensation.lean` | Actual finite-horizon counting integrals are integrable and obey signed compensation, including arbitrary initial records | No initial moment needed for increments; finite active region supplies the bound |
| `FrozenPreStateTime.lean` | Current state equals predictable pre-jump state outside countably many actual proposal times; all restricted time integrals agree, including on the initial product space | Time-null equality; no claim of equality at proposal times |
| `FrozenDynkin.lean` | Genuine fixed-horizon Dynkin expectation formula for actual frozen paths and the existing current-state generator; test-function and time-integrated drift integrability derived | Deterministic initial state; no stopped Gronwall, Lyapunov exit bound, or non-explosion claim |
| `InitialFrozenDynkin.lean` | Actual initialized change-expectation Dynkin identity and integrability without an initial test moment; usual separate-expectation identity under integrable initial test value; generator evaluated at actual current state | Autonomous finite-active-set construction and fixed horizon; no Gronwall, exit bound or non-explosion claim |
| `IntegralGronwall.lean`, `InitialFrozenExpectation.lean` | Integral Gronwall from continuity; finite-active generator gives sample-time integrability, Fubini, the actual expectation primitive and Lipschitz continuity | No stochastic continuity or differential inequality of the original expectation is assumed |
| `FrozenLyapunovBound.lean`, `InitialLyapunovExit.lean` | Actual affine-exponential frozen Lyapunov bound; actual first-exit Markov bound; reciprocal tail exhaustion | Drift, nonnegative Lyapunov function and initial integrability are model hypotheses |
| `LyapunovLocalization.lean`, `ConfigurationLocalization.lean` | Canonical {V<n+1} active sets, derived finite positive rate bounds, simultaneous exit monotonicity/compatibility, exact actual empirical generator and drift | The configuration drift is derived from LyapunovControl, not supplied as a separate assumption |
| `GlobalLocalizedProcess.lean`, `GlobalLocalizedActivity.lean` | Raw jointly measurable and adapted patch; correct initial value; actual finite proposal-list representation, finite activity/range and cadlag paths | Generic regularity bridge uses actual exit exhaustion, discharged in the next layer |
| `ActualNonexplosion.lean`, `ConfigurationNonexplosion.lean` | Genuine exit bounds and exhaustion from the raw generator drift; actual nonexplosive global configuration construction with measurable adapted paths | No given moment bound or exhaustion conclusion; arbitrary initial laws and global equation uniqueness are supplied below; the mean-field theorem remains open |
| `GlobalLyapunovMoment.lean`, `ActualGlobalMoment.lean` | Fatou gives integrability and exponential expectation control of the actual global Lyapunov value | Current-time expectation, not expected running maximum or all weighted activity bounds |
| `GlobalLocalizedCountingIdentity.lean`, `ActualGlobalCounting.lean` | Predictable global pre-state identified with its actual left limit; genuine global rate-threshold counting equation and pathwise integrability; configuration specialization from LyapunovControl | No active-set or height cutoff in the global integrand; global equation uniqueness is supplied below |
| `DiscreteCausalUniqueness.lean`, `CountingEquationUniqueness.lean`, `GlobalCountingUniqueness.lean`, `ActualGlobalUniqueness.lean` | Discrete first-disagreement uniqueness; genuine left-limit counting equations for separating tests; actual finite-coordinate particle specialization | Candidate càdlàg paths, same initial record, and same driving measure; no candidate localization or finite-activity premise |
| `ArbitraryInitialNonexplosion.lean` | One full noise event for all deterministic states yields arbitrary-initial-law exhaustion, càdlàg paths, finite activity, counting equations and coordinate uniqueness | Countable states and autonomous rates satisfying the Lyapunov drift; no initial moment for path properties, while moment estimates keep their integrability premises |
| `FiniteSupportGeometry.lean`, `FiniteSupportGlobal.lean`, `GlobalFiniteSupportDrift.lean` | Finite backward influence of configuration tests; bounded raw generator; product integrability and current-state compensator identification | Finite support is essential to this argument; unbounded-test martingales are not inferred |
| `InitialConditionalCompensation.lean`, `PredictableHistoryTruncation.lean`, `PredictableCountingMartingale.lean` | Signed compensation tested on actual past events; conditional zero for future integrals; counting-equation-to-martingale bridge | Predictability and product integrability are explicit in the generic bridge, proved for the application |
| `GlobalHistoryIntegral.lean`, `ConfigurationMartingale.lean`, `ConfigurationForwardEquation.lean` | All-sample terminal-history reconstruction; raw-adapted current-state generator martingale; weak forward equation by actual Fubini | Any independent initial probability law, finitely supported configuration tests; no initial moment, semigroup, strong Markov, or forward-law uniqueness claim |
| `InitialPredictableIntegral.lean` | Actual initialized counting kernel and Campbell measure; predictable integrability equivalence; signed/vector compensation and random-integral integrability | Raw product filtration; full completed-predictable extension is separate |
| `ThinningKernel.lean` | Finite positive bound on active rates; exact accepted-label mass; expected proposal increment times card(J) C equals the frozen generator | Requires positive C and 0≤q≤C for this one-step normalization; actual continuous-time Dynkin is proved above |
| `LimitArguments.lean` | Successive population-then-cutoff limits, reciprocal cutoff removal, scalar three-region convergence criterion; explicit failure of arbitrary diagonal limits | Inputs are already-obtained scalar error/tail bounds; does not derive stochastic coupling or uniform integrability estimates |
| `Models.lean` | Boundary-aware scalar first/second/third generator identities; weighted activity; full three-term positive coupling cost including common births; birth/death estimates; affine feedback; cubic Lyapunov domination, drift and superlinearity; integrated generator identities under integrability | Covers scalar computations and r=3 Lyapunov control, not the general multitype application, every real r>2, stochastic forward identities, or limit corollaries |
| `ModelTransport.lean` | Actual-law moment-feedback coefficient comparison and scalar quadratic coupling/activity/drift inequalities for any nonnegative globally Lipschitz mortality on [0,∞) | No stochastic existence or mean-field limit is asserted; the framework bridge is provided by `QuadraticModel` |
| `QuadraticModel.lean` | Actual quadratic-feedback `Rates 1`; exact scalar/general generator, coupling and activity identifications; Assumptions 2.2 and 2.3; a `LyapunovControl` instance with Ψ=1+x³ | Verifies the model hypotheses, not initialization, arbitrary real Lyapunov exponents r>2, or the resulting stochastic limit |

The separate AI-assisted mathematical review of `MomentGeometry`, `Transport`, and
`Framework` found their definitions consistent with the two source frameworks.
The original birth-at-zero restriction is retained separately from the more
general extension's admissibility convention. In particular, the original
assumptions use all probability measures, not only finite-moment laws. The
transport definition ranges over all genuine measure couplings rather than a
finite-support approximation.

## Deterministic patching and measure exit tails

`CarryingCapacity/Freezing.lean` treats a finite active set, finitely many jump
directions, and a state-dependent proposal decoder. Its recursion remains in
the one-jump enlargement when started inside and stays at its initial state
when started outside. The accepted exit jump is retained, and every later
proposal is ignored.

The same file's `CompatibleFamily` and `ExitFamily` structures make compatibility,
nested regions/nondecreasing extended exit times, and exhaustion explicit input
hypotheses. The patch is independent of the chosen level, unique, and agrees
with every sufficiently high level throughout a prescribed finite horizon.
These deterministic patching results do not assert that Poisson random measures
exist, that their proposals are locally finite, or that the patched object has
the desired stochastic law. Almost-sure exhaustion is proved separately below
from explicit exit-tail bounds, rather than silently included as a conclusion
of pathwise compatibility.

The same file now also proves a genuine measure-theoretic implication: bounds
`μ {exit n ≤ T} ≤ C_T/(n+1)`, with finite `C_T`, force a null intersection of
exit events. Taking countably many integer horizons gives almost-sure
exhaustion of every finite nonnegative horizon. Combined with pathwise
compatibility and monotonicity, this yields an almost-sure unique patched
path. The later Lyapunov and global-process modules derive the actual exit
estimates and prove measurability and adaptedness of the patched process.

`CommonInitialNoise.lean` supplies the independent initial-record extension.
For the coupling in Lemma 5.1, take the initial record to be the whole paired
array with its constructed joint law. The actual product keeps that full law
and makes the entire record independent of the entire noise sample. Either
coordinate projection can initialize an adapted frozen system, and the exact
initial marginal law, almost-sure regularity, and stopped compatibility are
proved. `CommonInitialStopping.lean` completes the actual product law and
minimally augments each initial-plus-noise history by its ambient null sets.
The exact first exit, without changing exceptional sample values, is a stopping
time for this enlarged filtration. It is measurable on the completed space and
AE-measurable on the original product space; truncation at a fixed time is
measurable in that time's history. The terminal history is only the supremum of
finite histories. Neither right continuity nor optional sampling is inferred.

`FrozenCompatibility.lean` now derives compatibility and monotone exits for
actual recursions with nested active sets and the same proposal sequence. The
exit jump is included. Under a common locally finite clock, stopping the larger
continuous-time path at the smaller exit arrival gives the smaller frozen path.
`MarkedNoise.lean` constructs the common counting measures, with finitely many
proposals in every bounded time-height box and no coincident event times on a
single probability-one event. `ChronologicalEvents.lean` measurably enumerates
these events. `RejectedProposals.lean` and `CommonFrozenProcess.lean` prove that
inserting proposals above the smaller rate bound leaves its path unchanged.
The resulting actual shared-noise paths are jointly measurable and almost surely càdlàg.
`CommonNoiseFiltration.lean` constructs their genuine noise-history filtration
and proves adaptedness by exact factorization through the observed points on
every sample. It also handles initial information already measurable at time
zero. An arbitrary independent initial law is handled by the product extension
described above.
`CommonFrozenExit.lean` defines their genuine first exits, proves finite-exit
attainment and monotonicity, and proves stopped compatibility across distinct
cutoff event lists. This establishes the pathwise core of Lemmas 3.1–3.2;
`PoissonFiniteDimensional.lean` separately supplies the underlying clock's full
finite-grid product law. `CommonFrozenStopping.lean` uses finite-exit attainment
and permanent freezing to identify each exit event with the current outside
event almost surely. Adjoining precisely the ambient null sets to the noise
history makes the exact original first exit a stopping time, without changing
its values or assuming right continuity. The later Lyapunov, global counting,
and uniqueness modules supply the autonomous nonexplosive particle equation.

`MarkedStripCounts.lean` identifies actual strip masses with finite mark counts,
including masses of windows `(S,T] × B`. `MarkedProducts.lean` integrates the
actual independent marks, and `PoissonTransform.lean` supplies the exact complex
Poisson transform with its absolute integrability. `MarkedThinning.lean` and
`MarkedSplitting.lean` derive the scalar and joint category laws, using
`CountVectorTransform.lean` for multivariate uniqueness. The complete category
vectors in different strips are independent because the full strip records are
independent. `PoissonSuperposition.lean` adds those vectors, while
`MarkedBoundedCounts.lean` identifies the finite strip sum and its total
parameter. Consequently, `MarkedRectangleLaw.countingMeasure_rectangles_map`
gives the actual joint product Poisson law for rectangles `(-∞,T] × Bᵢ`, for
one label, one common T≥0, pairwise disjoint measurable height categories, and
a common bound `Bᵢ ⊆ (-∞,m)` with m natural. Its parameters are
`T * positiveVolume.real Bᵢ`. Zero horizon, empty vectors, zero-intensity
categories, and negative-height portions are included.

The marked finite-grid law within one strip is now supplied by
`MarkedGridLaw.gridVector_map`.
`MarkedBlockProducts.lean` factors mark integrals over disjoint finite index
sets. `MarkedTimeCounts.lean` identifies the actual time-window counts with
consecutive mark blocks, and `MarkedTimeProducts.lean` integrates them using
the full joint clock increment law. The resulting grid-vector law permits
categories `B[a,i]` to vary with the window a, with disjointness required only
among i in that window. Its parameters are
`(u[a+1] - u[a]) * uniformUnit.real B[a,i]`, for a monotone grid with `u[0]≥0`.
Empty category types, empty grids, repeated times, and zero-intensity categories
are included. `MarkedGridRectangles.countingMeasure_gridRectangles_map` now
transfers the joint law to the original common counting measure. For one fixed
label j, a monotone grid u with `u[0]≥0`, and measurable categories `B[a,i]`
under one strict natural upper bound, disjoint within each window, the actual
masses of `(u[a],u[a+1]] × B[a,i]` have the full product Poisson law with
parameters `(u[a+1] - u[a]) * positiveVolume.real B[a,i]`. The natural-valued
product law is embedded into extended nonnegative reals in the exact measure
identity. `TimeGridRefinement` extends this to finite Boolean combinations of
lower rectangles inside a bounded box, and `PoissonCoordinateSum` aggregates
the grid counts without weakening their full product law. Bounded-box exhaustion
and disjoint measure-dense approximations then give the arbitrary finite-intensity
set law. The symmetric-difference intensity controls count discrepancies;
summability gives almost-sure eventual equality of the entire finite count
vector. `MarkedPoissonMeasure.countingMeasure_map` states the resulting exact
law for genuine counting-measure masses, and `independent_countingMeasure`
gives joint independence. This is for one fixed label and finite target
intensities, without a target-law or independence premise.

`MarkedPastIndependence.independent_stripView_windowCount` now proves that one
future category count in `(s,s+t]` is independent of the entire indexed
arrival-time/mark observation of its strip up to time s, for s,t≥0 and any
measurable mark category. The observation reveals `(arrival,mark)` only after
the arrival and otherwise returns `(s+1,0)`. Its finite cylinders depend on
both times and marks. Fixing the clock separates the past and future mark
indices; `ClockPastObservation` makes the remaining mean measurable in the
null-augmented clock past, and the proved clock-increment independence factors
the outer integral. Power-transform uniqueness and a generating pi-system
then extend the result to the complete strip observation. No random-index
independence is assumed.

`IndependentProductHistory.indepFun_observations_futures` lifts the per-strip
result through the actual infinite product probability law. It proves joint
independence of complete past and future arrays by factoring paired finite
cylinders, rather than inferring it from pairwise independence.
`CommonMarkedPastIndependence` then recovers the existing common-noise view by
translating arrived heights and preserving the unseen sentinel. Consequently
the genuine mass of `(s,s+t] × B`, for measurable B below a strict natural
height bound, is independent of the complete common observation at s, across
all labels and strips. The result also holds for the null-augmented history
under the completed ambient law. It covers one category per strip in one
future window; the stronger joint future law within a strip remains separate.
`InitialMarkedPastIndependence` extends this to the actual independent
initial-record product and its completed histories by direct product-law
factorization for arbitrary measurable initial-plus-observation events.

`MarkedCountMoments` proves finiteness and integrability of actual bounded-height
counts before converting them to real values. `MarkedCountAdapted` factors each
prefix mass through the full observed marked history on every sample.
`MarkedCountMartingale` combines these facts with actual future independence to
prove the conditional window mean and compensated-count martingale.

`MarkedElementaryCompensation` proves weighted future-count identities for
arbitrary nonnegative past-measurable coefficients. `PredictableSets` defines
the positive-time predictable sigma algebra from past events times `(s,t]`
times height categories. `PredictableCompensation` constructs the actual
sample-point Campbell measure as a countable sum of point pushforwards. The
proved elementary identity gives agreement with product intensity on the
generating rectangles. Finite-box restrictions, measure uniqueness, and zero
nonpositive-time mass give equality on the entire predictable sigma algebra.
Thus `compensation_nonnegative` allows every nonnegative predictable integrand,
including infinite expectations. `MarkedCountingKernel` and
`PredictableIntegral` supply the actual s-finite kernel, Bochner Fubini,
integrability transfer, and signed/vector compensation.

`InitialElementaryCompensation` includes both raw and completed histories for
elementary coefficients. `InitialPredictableCompensation` proves that every
fixed-initial section of a raw initial-product predictable function is
noise-predictable. Applying the proved compensation sectionwise and Tonelli
then gives the full nonnegative identity under the actual arbitrary initial
law. Arbitrary completed predictable integrands are not included in that
section argument.

`FrozenJumpIdentity` telescopes the actual chronological recursion, including
the exit jump. Its strict-past state is identified with the constructed
predictable version from `PredictableStepApproximation` and
`FrozenPredictableIntegrand`. `FrozenCountingIdentity` proves finite atomic
integrability and converts the actual event sum into the original counting
measure integral. `InitialFrozenCountingIdentity` lifts that equation to the
actual initial-record product.

`FrozenIntensity` derives the signed integrability bound from finite active
states and finite time-height support, with no assumed stochastic moment
estimate. `FrozenCompensation` and `InitialFrozenCompensation` then apply the
proved compensation to the actual accepted increments. `FrozenGeneratorIntegral`
integrates height and identifies the sum of label drifts with the existing
frozen generator. `FrozenPreStateTime` shows that current and pre-jump states
differ only at countably many actual proposal times, and so have identical
time integrals. `FrozenDynkin.dynkin` combines these steps into a genuine
fixed-horizon expectation identity for the constructed process.
`InitialFrozenDynkin.dynkin_change` supplies the corresponding initialized
identity without requiring an initial test-function moment. Its
`dynkin` theorem gives separate expectations under exactly integrability of
the initial test value; it proves the future test value integrable.

The shared-noise construction currently uses autonomous rates `J → E → ℝ`.
It covers state feedback in a finite interacting configuration, but has not yet
been extended to rates with a deterministic time-dependent environment. Its
finite-box path regularity needs no rate sign or dominance condition; interpreting
the path as the desired intensity-driven system still requires nonnegative rates
and a valid rate bound. `InitialFrozenExpectation` supplies genuine Fubini and
Lipschitz expectation continuity; `IntegralGronwall` and `FrozenLyapunovBound`
derive the actual affine-exponential bound. `InitialLyapunovExit` identifies
the genuine exit event with the threshold event and applies Markov's inequality.
`ActualNonexplosion` combines these results with canonical sublevels and
common-noise compatibility, discharging all exit and exhaustion premises.
`ConfigurationNonexplosion` instantiates this chain from the manuscript's
single-lineage LyapunovControl and actual empirical rates. The global process
is raw jointly measurable and adapted, and `GlobalLocalizedActivity` derives a
finite actual proposal list containing every change on each bounded horizon.
`ActualGlobalMoment` retains the exponential moment estimate by Fatou.
`GlobalLocalizedCountingIdentity` identifies the global predictable pre-state
with the actual left limit. Before a sufficiently high genuine exit, that
pre-state lies in the active region and its rate is below the derived height
bound, so the freezing indicator and height cap disappear pointwise from the
accepted increment. The actual finite-level equation and pathwise integrability
then transfer to the global path. `ActualGlobalCounting` discharges exhaustion
from the Lyapunov assumptions, including the empirical configuration model.
`DiscreteCausalUniqueness` rules out a first disagreement by right continuity
and strict-past causality of the counting equation. `ActualGlobalUniqueness`
discharges the constructed process's exhaustion; finite coordinate tests separate
configurations, so candidate nonlinear-test equations are not assumed.
`ArbitraryInitialNonexplosion` applies the deterministic-initial theorem at each
state and takes a countable intersection in the actual noise law. Substitution
of any independent sampled initial state therefore gives the same path results
without an initial moment.

For finite-support tests, `FiniteSupportGeometry` proves that all states capable
of affecting a test lie in a finite backward influence set. This bounds the raw
generator and supplies product integrability of the actual counting field.
`InitialConditionalCompensation` tests signed compensation on every past event,
and conditional-expectation uniqueness gives conditional zero. The resulting
`ConfigurationMartingale.generator_martingale` uses the actual current state
and raw history filtration. Its adaptedness is proved on every sample by
`GlobalHistoryIntegral`, rather than inferred from an almost-sure modification.
`ConfigurationForwardEquation` derives genuine sample-time Fubini and the
integrated weak forward equation. No initial Lyapunov moment is required for
these finite-support results. Optional sampling, semigroup/strong Markov
statements, forward-law uniqueness, and right continuity of the completed
filtration remain open.


## Next connections to formalize

1. Extend the proved arbitrary measurable finite-intensity planar-set laws
   to infinite-intensity sets and simultaneous noise labels, and extend
   bounded-rectangle independence from the whole common marked
   history to joint future windows/categories within strips.
   Scalar future rectangle independence already suffices for the proved
   predictable compensation theorem; this stronger law is not a prerequisite
   for the next drift argument.
2. Prove the usual right-continuous filtration, optional sampling, and required
   semigroup/strong Markov statements. Actual nonexplosion, global counting
   equations, coordinate-equation pathwise uniqueness, the finite-support
   generator martingale and weak forward equation are now proved, including
   arbitrary independent initial laws. Lyapunov expectation bounds retain their
   initial-moment assumptions.
3. Construct the deterministic-environment forward law and its uniqueness;
   prove preservation of the complete Lyapunov curve space and the actual
   stochastic Volterra estimate, then apply the proved Bielecki contraction and
   conditional fixed-point theorem to construct the nonlinear flow.
4. Use the proved initialization coupling and empirical-error limits to derive
   localized process coupling, time-grid convergence, and Skorokhod/path-space
   chaos. Preserve the original theorem's weaker initialization as a distinct target.

The empirical transport LLN bridge is now proved: `FiniteTransport` constructs
the common-mass coupling and bounds transport by
`diam(S) * (1/2) * sum_{x in S} |μ{x} - ν{x}|`. `EmpiricalLLN` applies it to
finite-range truncations, then combines singleton and fixed-cutoff tail strong
laws, vanishing target tails, and the transport triangle inequality.
`EmpiricalMeanError` derives Lyapunov uniform integrability from the common
marginal law, obtaining expected-error convergence. Its time-integrated theorem
derives error measurability and domination from jointly measurable samples, a
continuous law curve, and a uniform Ψ integral bound on a finite time measure.
The samples in `EmpiricalMeanError` are initial segments of one infinite family.
`EmpiricalArrayError` proves equality of finite-vector laws and transfers the
expected and time-integrated limits to separately constructed finite iid
families. Their probability spaces may differ with N, and no cross-N or
cross-time independence is required. `InitialCoupling` then assembles the full
initial lemma with the exact original and iid vector marginals and vanishing
expected pairing cost; convergence of expected errors is derived, not assumed.
The time hypotheses quantify over the whole time type. For a finite-horizon
Lyapunov bound, choose that type to be the interval `[0,T]` itself. Restricting
only the integration measure while keeping time type ℝ does not restrict the
theorem's uniform-bound hypothesis to the interval.
