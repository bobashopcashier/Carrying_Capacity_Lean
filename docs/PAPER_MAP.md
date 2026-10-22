# Sources and formalization boundaries

The active formalization target is Xie's manuscript. Earlier original-paper
results are retained below as a separate inventory, not as an additional target.
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
  `new.pdf` is byte-identical to `new.pdf` at the recorded source version
  `c768811` (not necessarily the paper repository's latest formatted PDF): SHA256
  `cf1d663ae6fd9b72038a37f07a6bcb52aceed59d7ccfe089aa066240835660e5`.

## Original-paper inventory

The original Assumption 2.1 imposes lineage-linear growth uniformly over laws,
and a global Lipschitz bound using state distance plus total variation.
Rates vanish when the relevant source-type count is zero. Rates do not depend
on the number of lineages.

| Original result | Content | Full stochastic proof status |
|---|---|---|
| Proposition 2.3 | Feller semigroup and finitely-supported generator core | Actual nonexplosive particle construction and coordinate-equation pathwise uniqueness now proved under the original assumptions; the Feller semigroup and core statements remain open |
| Proposition 2.4 | Exchangeability and Markov empirical process | Symmetrization kernel and generator intertwining proved; full process statement remains open |
| Theorem 2.5 | Deterministic nonlinear forward law and empirical path convergence | Not formalized |
| Remark 2.6; Corollary 2.7 | Fixed-time and path-space propagation of chaos | Not formalized |
| Lemmas 3.1–3.3; Propositions 3.5, 3.7–3.9; Lemmas 3.11–3.12 | Symmetrization, domination, freezing, tightness | Algebraic symmetrization and marked frozen paths partly formalized; domination, process-law identification, and tightness remain open |

Theorem 2.5 starts from a uniformly symmetrized deterministic empirical law
converging weakly. It does **not** assume the extension's uniform Lyapunov
moments. Remark 2.2 motivates moment-dependent rates. Section 4 discusses
moment-mediated examples; Example 4.2 notes a truncation requirement.
[Primary source, Sections 2–4](https://arxiv.org/html/2307.06010v2#S2).

`OriginalParticleSystem` uses the original rates on all probability laws and
the actual empirical probability measure. For total population V, the proof
derives `AᴺV ≤ D L (V+N)` directly from the original growth bound. Births add
one, deaths do not increase V, and mutations preserve it, including the
invalid-jump convention. Finite sublevels, the actual shared-noise localization
and countable-state mixing then yield nonexplosion, measurable adapted paths,
càdlàg regularity, finite activity, the counting equation and coordinate-equation
pathwise uniqueness for every independent initial law. No extension
`LyapunovControl` or initial moment is imposed. This does not identify a Feller
semigroup, prove the Markov empirical-process statement, or establish the
original convergence theorem.

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
| same file, Proposition 4.2 | Non-explosive chain in a deterministic environment and uniqueness of its linear forward law | Actual PRM construction and finite-support forward equation; an alternative uniqueness proof by finite-state minimality and actual frozen-law convergence |
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
conclusions of Lemma 5.2 are now supplied for the actual constructed nonlinear
arrays by `NonlinearParticleArray` and `NonlinearParticleEmpirical`. The exact
product input law and original-noise identities come from `ParticleInputRecords`
and `ParticleNoiseProjection`; genuine integrability is proved before both the
fixed-time and real time-integrated error limits. The population coupling modules
now prove Proposition 5.3's actual uniform common-exit tail, sharp stopped
Gronwall estimate and vanishing stopped expectation for the canonical coupled
systems. All error integrability and comparison estimates are derived.
`PopulationFocalApproximation.exists_full_synchronous_approximation` combines
these with the original initialization assumptions: it constructs paired initial
laws with the exact original and iid vector marginals, then proves all three
canonical comparison conclusions of Theorem 5.4 for their actual shared-noise
paths. Averaged path discrepancy, uniform empirical transport discrepancy
between the paired systems, and fixed-focal path discrepancy tend to zero in
probability. Exact input relabeling and pathwise uniqueness prove the symmetry
and equal coordinate stopped expectations used for the focal limit. The
headline preserves initial vector laws;
it does not separately export a whole-trajectory pushforward identity to a
previously supplied process on another initial-record space. Proposition 3.3's actual
frozen Lyapunov expectation and reciprocal exit estimates are now proved,
including their empirical configuration specialization. The exhaustion,
measurable adapted patch, cadlag regularity and finite activity parts of
Proposition 3.4 are proved, as is the unrestricted test-function counting equation
for the constructed global path. The global Lyapunov expectation part of Corollary 3.6
follows by Fatou. Global equation pathwise uniqueness is proved, including the
particle-coordinate formulation. The actual finite-support generator martingale
and integrated weak forward equation are proved. Countability also removes the
initial-moment premise from nonexplosion and these finite-support conclusions.
Proposition 4.2 now has an actual prescribed-environment
realization on the canonical initial-record/noise product: measurable adapted
nonexplosive paths, a cutoff-free counting equation and coordinate-equation
pathwise uniqueness. The paper's assumptions discharge the required rate and
Lyapunov hypotheses. The exact exponential moment envelope in Theorem 4.3 is
proved for this process, and its time marginals define genuine MomentLaw values
with the correct initial law. Their Wκ continuity follows from fixed-time
almost-sure continuity and superlinear uniform integrability. The actual
prescribed-environment evolution therefore preserves the complete manuscript
curve space. Actual shared-noise positive increments and compensation now give
the stochastic Volterra estimate, including the manuscript's full expected
running-supremum bound with derived integrability. Applying Bielecki contraction
proves exactly one fixed curve in that invariant space and gives a canonical nonexplosive
process with those marginals and its own-marginal counting equation on `[0,T]`.
The actual untruncated finite-support weak forward equation is now proved.
Prescribed-environment linear law uniqueness holds against every probability-valued
weak solution with genuinely integrable tested drift, with no candidate moment
bound. General continuous environments with uniformly bounded genuine Ψ moments
are covered; their initial value need not equal the initial law. Their actual
output MomentLaw curve is now proved Wκ-continuous as well. For the nonlinear
problem, atomic continuity and uniform superlinear tails derive transport
continuity of every uniformly Ψ-bounded weak candidate. Linear identification
and actual shared-noise comparison then give full-class uniqueness by Gronwall.
The already constructed fixed curve supplies existence and the exact envelope,
so Theorem 4.3's law well-posedness statement is proved, including its full
moment-bounded uniqueness class. Genuine tested time integrability is explicit
in the formal definition of the weak equation.

The fixed law curves and actual canonical paths are consistent across
construction horizons, including their endpoints. `TimeDependentLocalUniqueness`
and `NonlinearPathConsistency` derive path equality from actual same-input
counting equations. `NonlinearGlobalProcess` gives one all-time measurable,
raw-adapted, càdlàg realization with its actual nonlinear marginals and exact
moment envelope. `NonlinearGlobalCounting` proves genuine predictable left
states, the all-time own-marginal counting equation, integral finiteness, finite
activity and horizon-local spatial exit exhaustion. `NonlinearGlobalForward`
proves global weak-law existence and uniqueness in the locally Ψ-bounded class;
continuity and the sharp envelope are derived for every candidate. Proposition
4.2 and Corollary 4.4 still retain their arbitrary supplied PRM-space and
completed right-continuous filtration obligations.

For Section 6, `NonlinearEmpiricalSupremum.runningError` is the actual
independent-array error supremum over every real time in `[0,T]`; its AE
measurability is proved from particle path regularity and the continuous law
curve. `IndependentArrayLLN` proves centered empirical-mean limits for any
integrable statistic of the iid particle inputs, and `EmpiricalTimeGrid`
supplies the exact deterministic cell and grid inequalities.
`NonlinearPathVariation` constructs the actual accepted weighted jump variation
on `(s,t]` and proves exact nonnegative compensation. `NonlinearActivityBound`
uses genuine marginal identities and the moment envelope to bound expected
current activity. `NonlinearVariationDisplacement` proves that actual variation
bounds every same-path displacement on one event, using a countable family of
distance tests in the genuine counting equations. `NonlinearVariationBounds`
derives the expectation estimate `C_activity * (1 + K(T))^2 * (t-s)`, almost-sure
finiteness, real integrability and the law's time modulus. These results discharge
all stochastic premises of `NonlinearEmpiricalUniform`, which proves Proposition
6.2's actual uniform independent empirical convergence. Each error threshold
selects one finite grid before the population limit; exact iid record laws give
the centered variation LLN, with no independence across times or population sizes.

`PopulationEmpiricalLimit` combines this uniform iid limit with the proved
synchronous comparison, then projects the paired record to its original initial
vector while retaining exactly the same noise. It proves Theorem 6.3's uniform
empirical Wκ and generalized-moment limits in probability for the actual canonical
population with the original vector law. `CoupledLawConvergence` and
`PopulationFixedTimeChaos` give weak convergence of each fixed-k vector at each
fixed time to the product nonlinear marginal, the fixed-time part of Corollary
6.4. `SkorokhodJ1` constructs the genuine path metric, its Borel structure and
time-change convergence criterion, including uniform-to-J1 convergence. The
actual random path maps have not yet been proved measurable for that Borel
structure, so Skorokhod path-space chaos is not asserted.

## Dependency order

1. Define the state, jump maps, empirical averages, rate data, adapted metric,
   and probability moment with the paper's domain and integrability conditions.
2. Prove deterministic metric, generator, finite-state, and rate inequalities.
3. Construct frozen PRM-driven processes; prove measurability, adaptedness,
   local finite activity, compatibility, Dynkin, and Lyapunov exit estimates.
4. Deduce almost-sure exhaustion and apply deterministic path patching.
5. Use the proved actual deterministic-environment laws, finite-support weak
   forward equation and finite-state minimality to identify every probability
   weak solution with the constructed law, without candidate moment assumptions.
6. Use the proved atomic-to-transport continuity, linear law identification and
   actual synchronous comparison to identify every moment-bounded nonlinear
   weak solution with the Bielecki fixed curve. The exact envelope and
   actual pathwise compatibility across horizons now give one all-time canonical
   nonlinear process and unique global law. External-PRM realization remains separate.
7. Initial matching, uniform-integrability upgrades, empirical LLNs,
   localized population coupling, and the successive N-then-R limit are proved
   for the canonical systems. Actual paired-path relabeling gives the stopped
   coordinate symmetry and fixed-focal comparison as well.
8. The time-grid argument, canonical uniform interacting empirical limit and
   fixed-time finite-particle chaos are proved. Connect actual random paths to
   the constructed J1 Borel space, prove path-space chaos, and complete the
   model corollaries and Wp comparisons.

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
| `LyapunovFlowSpace.lean` | Genuine extended Lyapunov integral; lower semicontinuity from continuous atomic masses; finite bounds imply integrability; closed complete moment sublevels and uniform-metric curve spaces; nonempty complete manuscript space with its exact exponential envelope | Actual prescribed-environment evolution preserves this space below; weighted completeness is supplied by the next module |
| `BieleckiFlowSpace.lean` | Exact weighted supremum metric; exp(−λT)d_uniform≤d_λ≤d_uniform; explicit uniform equivalence and completeness; actual Volterra-kernel integration gives A/(λ−A); conditional unique fixed point for λ>2A | The actual stochastic Volterra estimate and fixed-point application are supplied below; this generic theorem retains its explicit map and estimate inputs |
| `EmpiricalMeasure.lean` | Empirical probability/MomentLaw constructions; test integrals; paired and permuted couplings; Wκ upper bound; update estimate; exact empirical-integral generator and Lyapunov identities | No process law follows from the generator algebra alone |
| `EmpiricalMatching.lean` | Repeated-state mass splitting; doubly stochastic label plan preserving transport cost; Birkhoff decomposition; Wκ equals attained minimum over permutations; measurable selected matching with exact empirical law and cost | Randomized joint exchangeability is supplied by `ExchangeableMatching` |
| `FiniteTransport.lean` | Explicit diagonal common mass and normalized residual-product coupling; exact marginals; Wκ ≤ diameter times half the sum of absolute atomic mass differences; transport convergence from atomic convergence on fixed finite support | Finite-support comparison, not an arbitrary-law optimal-plan theorem |
| `EmpiricalLLN.lean` | Full almost-sure empirical Wκ convergence from measurable pairwise independent identically distributed samples and a finite κ moment; scalar, moment, singleton, tail, and truncated strong laws; finite Ψ gives a MomentLaw | Fixed-law convergence; no uniform-in-time path theorem |
| `EmpiricalMeanError.lean` | Common marginals imply exact empirical Ψ expectations; derived uniform integrability and expected Wκ convergence; βN≤2Mκ; jointly measurable errors and time-integrated convergence under a continuous law curve and uniform Ψ integral bound | Uses initial segments of an infinite sample family; the finite-array transfer is supplied below |
| `EmpiricalArrayError.lean` | Constructed canonical iid sequence; exact finite-vector product law; empirical errors are identically distributed with canonical errors; integrability, βN≤2Mκ, expected-error limit and time-integrated limit for arbitrary N-dependent iid arrays | Matches the independent empirical-error conclusions of Lemma 5.2; assumes measurable samples and continuous target laws, and does not construct nonlinear trajectories |
| `ExchangeableMatching.lean` | Actual law obtained from optimal matching and an independent uniform common permutation; preservation of both full exchangeable vector laws; joint paired exchangeability; exact optimal cost; cost distribution, integrability and expectation identities; iid-target specialization | Supplies the finite-population construction used by the fully assembled initial lemma below |
| `InitialCoupling.lean` | Lemma 5.1: exact original and iid full-vector marginals, joint exchangeability, integrable optimal cost, and expected cost tending to zero, derived from probability convergence and the uniform expected empirical Ψ bound | Produces coupling laws on paired arrays; `CommonInitialNoise` supplies independent future noise, while the population comparison is supplied by the later population modules |
| `Symmetrization.lean` | Generator equivariance; uniform permutation average; equal empirical measures iff a relabeling exists; genuine exchangeable symmetrized measure with deterministic empirical state | Stochastic exchangeability still needs process construction and uniqueness |
| `EmpiricalGenerator.lean` | Countable space of actual empirical measures; representative-independent symmetrization Markov kernel; pushforward is the prescribed Dirac law; quotient generator; Bα=αA intertwining | Does not assert the empirical process is Markov or supply a Feller semigroup |
| `LyapunovTails.lean` | Actual uniform integral tails from superlinear Ψ; affine-envelope uniform integrability; empirical-transport in-measure to L1 upgrade using expected empirical Ψ bound | Common probability space; explicit integrability is required to avoid totalized-integral loopholes; the initial in-probability convergence is an input |
| `Framework.lean` | Correct birth/death/type-transition maps, boundary rates, generators; original total-variation growth/Lipschitz assumptions; extension's positive-increment coupling, activity, and Lyapunov hypotheses | These are assumption structures, not proofs that arbitrary rates satisfy them; initialization and full nonlinear forward equation are not encoded |
| `OriginalParticleSystem.lean` | Exact empirical probability rates; total-population finite sublevels and original-growth drift; actual arbitrary-initial nonexplosive particle path, finite activity, counting equations and coordinate pathwise uniqueness | Uses only OriginalAssumptions, with no moment-law restriction; original Feller/core, Markov and mean-field statements remain open |
| `DeterministicEnvironmentRates.lean` | Identical-state coupling cost equals absolute rate differences weighted by jump lengths; fixed-state Wκ Lipschitz rates; time measurability and compact-horizon finite-active-set rate bounds from the actual coupling/activity assumptions | Does not assume separate rate regularity; the actual global application is supplied below |
| `DeterministicEnvironmentFrozen.lean` | Chooses the proved compact-horizon cap and constructs the actual endpoint-clamped frozen path; derives joint/raw-history measurability, càdlàg paths, signed counting equation, Dynkin change formula and generator martingale; original q.generator(v s) recovered on the horizon | Only the paper coupling/activity hypotheses and continuous environment are used for rate premises; signed changes need no initial test moment; this is the finite-active ingredient of the global construction |
| `DeterministicEnvironmentLyapunov.lean`, `DeterministicEnvironmentProcess.lean` | Exact LyapunovControl gives finite sublevels, affine and pointwise envelope drift, and all-time rate bounds for endpoint-clamped environments; actual global initialized path, raw measurability/adaptedness, exhaustion, càdlàg regularity, finite activity, moments and counting equation; finite-coordinate same-input uniqueness | The path definition does not depend on a supplied moment bound; nonexplosion uses genuine environment and initial Lyapunov bounds, supplied by the manuscript curve. Original rates are recovered only within its horizon; no arbitrary external PRM realization is asserted |
| `DeterministicEnvironmentEnvelope.lean`, `DeterministicEnvironmentLaw.lean` | Scalar derivative/FTC verifies the exact manuscript envelope; actual process and output laws have integrable Ψ and ordinary/extended moments bounded by K(t); actual time-marginal pushforward is a MomentLaw with exact initial law and integral identities | Supplies the laws and moment component of invariance; the actual continuous-curve map is supplied below |
| `TimeDependentStochasticContinuity.lean`, `LawCurveContinuity.lean`, `DeterministicEnvironmentEvolution.lean` | Actual indexed arrival times are nonatomic; fixed-time no-proposal events and localization give AE continuity at each deterministic time; genuine paired couplings, superlinear UI and Vitali give Wκ continuity; exact output laws define an invariant self-map of ManuscriptCurves | The full event may depend on the deterministic time; no assertion of everywhere-continuous sample paths. Actual contraction, fixed-point self-consistency and linear forward uniqueness are supplied below; arbitrary external-space realization remains separate |
| `SynchronousPositiveIncrement.lean`, `SynchronousFrozenCounting.lean`, `SynchronousGlobalCounting.lean` | Exact shared-height update and three positive regions; genuine paired recursions use the same finite chronological proposals; finite telescoping and atomic counting integrals yield actual global positive-increment domination for every horizon prefix | Both genuine exit sequences supply the localization; a common maximum rate cap aligns the lists without assuming cap monotonicity or a coupling equation |
| `TimeDependentGlobalPreStateTime.lean`, `SynchronousCompensation.lean` | Countably many localized levels give actual pre-state/current-state equality at almost every time; predictability, nonnegative compensation and exact height integration give the full finite-label expected activity and distance inequalities | Allows infinite values until separate moment bounds prove finiteness; no expected coupling inequality or finite expected activity premise |
| `CouplingExpectation.lean`, `CoupledDistanceContinuity.lean`, `DeterministicEnvironmentCoupling.lean` | Paper coupling hypothesis derives actual distance/activity integrability and E activity≤L(1+2K(T))(E distance+W input); genuine superlinear UI gives continuity of the paired expected distance; constructed joint law bounds output transport | The same canonical initialized processes are used throughout, with no new pair law, independence or expected-continuity assumption |
| `VolterraGronwall.lean`, `DeterministicEnvironmentVolterra.lean` | Integrating factor and FTC give the explicit forced convolution; actual extended compensation and independent moment bounds give a finite real integral inequality; fixed-time expected-distance and output-law Volterra bounds follow | Exactly the estimate needed by the Bielecki theorem; running-supremum control is supplied separately below |
| `SynchronousRunningSupremum.lean` | Actual uncountable running supremum agrees almost surely with rational observations plus the endpoint; measurability follows from that countable version; actual positive-jump compensation bounds its extended expectation | Genuine localization derives right-local constancy; no continuity of arbitrary cost functions or finite expected supremum is assumed |
| `DeterministicEnvironmentRunningSupremum.lean` | Exact manuscript exponential-convolution estimate for the expected supremum over all real times in [0,t]; actual supremum is AE measurable, has finite expectation and is almost surely finite; its real version is integrable and obeys the same estimate | Uses only the original manuscript assumptions and constructed processes. No finite-supremum or expected-coupling hypothesis is supplied |
| `NonlinearFixedPoint.lean` | Concrete Bielecki weight 2A+1; actual invariant evolution has exactly one fixed curve; canonical process has that exact marginal law and moment envelope, is jointly measurable, raw-adapted, càdlàg and nonexplosive, and satisfies its own-marginal counting equation with the true left state | Requires a genuine finite initial Ψ moment; uniqueness is within ManuscriptCurves. Self-consistency is on the selected [0,T], with endpoint-held environment afterward; full moment-bounded law uniqueness and law consistency across horizons are supplied below; arbitrary external PRM realization remains open |
| `FiniteGenerator.lean` | Exact 1/N empirical-generator identity and averaged Lyapunov drift | The empirical-law interpretation is proved in EmpiricalMeasure; Dynkin and process expectation bounds remain separate |
| `FiniteJumpForward.lean` | Probability-valued weak solution definition with explicit genuine time integrability for each finite-support tested drift; atomic continuity derived from its integral equation; finite fibers give finite generator influence | No candidate moment, continuity, Markov or uniqueness conclusion is assumed |
| `TimeDependentFrozenForward.lean`, `DeterministicEnvironmentFrozenForward.lean` | Actual singleton expectations are genuine probabilities, have the initial values and finite-mass bounds, and satisfy the finite forward system by proved Dynkin/Fubini; Lipschitz mass continuity; exact matrix leakage and self-loop cancellation; derived manuscript coefficient bounds | The closed internal system concerns targets in the finite active set; no actual law equation is supplied as input |
| `FiniteForwardComparison.lean`, `FiniteJumpRestriction.lean`, `FrozenForwardMinimality.lean` | Last-nonpositive-time comparison for genuine finite integral systems; weak-law finite restriction with derived nonnegative finite external inflow; actual frozen probability minimality inside the active set | All-subinterval inequalities come from integrable equalities; a one-sided inequality anchored only at zero is not substituted |
| `TimeDependentFrozenLawLimit.lean`, `TimeDependentForwardUniqueness.lean` | Actual horizon agreement and bounded convergence identify frozen atom limits; real atomic domination forces probability-measure equality; constructed global law equals every probability weak solution | Generic exhaustion, local rate bounds, finite jump fibers and continuous coefficients are explicit; paper assumptions discharge them below |
| `DeterministicEnvironmentFiniteSupport.lean`, `DeterministicEnvironmentForward.lean` | Finite actual predecessor sets bound the unrestricted increment and generator; derived signed compensation and sample-time integrability/Fubini; actual original-rate weak forward solution and canonical nonlinear own-law equation | Finite-support tests, no unbounded-test extension; original coefficients and self-consistency hold on [0,T] |
| `DeterministicEnvironmentGeneralForward.lean` | Actual original-rate weak forward existence for every continuous prescribed environment with uniformly bounded genuine Ψ moment; finite-support increment integrability, signed compensation and Fubini derived for the existing global process | Finite initial Ψ moment; no manuscript envelope membership or v(0)=ν hypothesis; original-rate equation on [0,T]. General output-law Wκ continuity is supplied below |
| `DeterministicEnvironmentForwardUniqueness.lean` | Actual prescribed-environment existence and linear uniqueness on [0,T] without any competing-law moment bound; nonlinear weak solution in ManuscriptCurves is the actual evolution fixed point; exactly one nonlinear weak solution in that curve space | General prescribed environment has Wκ continuity and bounded genuine Ψ moment, with finite initial Ψ moment; full-class nonlinear uniqueness is supplied below |
| `DeterministicEnvironmentGeneralLaw.lean` | Genuine actual pushforward MomentLaw for general prescribed environments, exact initial law, derived affine-exponential Ψ bounds, and Wκ-continuous outputCurve by stochastic continuity and superlinear uniform integrability | Continuous environment with bounded genuine Ψ moment and a separate finite-Ψ initial law; no v(0)=ν hypothesis; canonical product-space realization |
| `AtomicTransportContinuity.lean` | Actual finite truncation handles retained atoms and zero normalization; genuine uniform superlinear moments make truncation costs small; atomic convergence gives Wκ convergence for arbitrary filters; weak solutions are automatically Wκ-continuous | The candidate supplies no continuity or rate-regularity premise; true extended Lyapunov bounds give integrability before ordinary moments are used |
| `DeterministicEnvironmentGeneralCoupling.lean`, `NonlinearForwardUniqueness.lean` | Proved linear identification realizes general nonlinear candidates; common-noise compensation and actual endpoint moments give a finite expected-distance inequality; Gronwall proves full bounded-Ψ law uniqueness; actual existence, exact envelope and exact interval-domain unique existence | Theorem 4.3's law statement under the original manuscript hypotheses and finite initial Ψ moment; no candidate continuity, sharp envelope or stochastic comparison assumption |
| `FiniteJumpForwardRestriction.lean`, `NonlinearHorizonConsistency.lean` | Genuine weak-solution integrability and equations restrict to smaller horizons and transfer under local coefficient/law equality; actual fixed curves, deterministic environments and process marginal laws agree on overlapping construction intervals | Includes zero horizons and endpoints; pathwise consistency and the all-time realization are supplied below |
| `TimeDependentLocalUniqueness.lean` | Genuine separating-test counting equations, same initial state and locally equal rates imply equality on the closed horizon | Candidate càdlàg paths and true left limits are explicit; the actual nonlinear paths discharge these premises |
| `NonlinearPathConsistency.lean` | Actual same-input nonlinear paths agree through the smaller horizon's endpoint; one event gives simultaneous integer-horizon compatibility | No path compatibility is assumed; actual law consistency and local counting-equation uniqueness prove it |
| `NonlinearGlobalProcess.lean` | One all-time jointly measurable, raw-adapted, càdlàg nonlinear realization; true marginals, continuous environment, exact envelope and arbitrary finite-horizon agreement | Canonical initial-state/noise space; no arbitrary supplied PRM realization or usual-filtration assertion |
| `NonlinearGlobalCounting.lean` | Actual predictable left limits, all-time own-marginal counting equation, genuine increment integrability, initial state, finite activity and spatial localization exhaustion on every horizon | Fixed-test equation is simultaneous in all horizons; unbounded-test expectation identities are not inferred |
| `NonlinearGlobalForward.lean` | Actual global weak-law existence and unique existence on nonnegative times in the full locally Ψ-bounded class; continuity and envelope follow for candidates | Genuine finite-support tested time integrability remains explicit; negative-time extensions need not agree |
| `ParticleNoiseProjection.lean`, `ParticleInputRecords.lean` | Exact joint product law and mutual independence of whole particle input records; exact projected counting measures; raw-history projection measurability; coupled-initial-array specialization | Requires the proved initial iid marginal, rather than assuming trajectory independence |
| `NonlinearParticleArray.lean`, `NonlinearParticleContinuation.lean` | Constructed nonlinear copies on the original particle noise; full product fixed-time laws, trajectory independence, raw adaptedness, simultaneous path regularity and left limits; actual initial values and integrable all-horizon counting equations | Path independence is for the coordinate sigma algebra; nonlinear self-consistency is on [0,T], with endpoint-held rates afterward |
| `CompactIntervalIntegration.lean`, `NonlinearParticleEmpirical.lean` | Interval-subtype Lebesgue measure and exact integral/integrability transfer; actual beta_N integrability, twice-moment/envelope bounds, fixed-time convergence and genuine real time-integrated convergence | Supplies the independent-array empirical-error component of Lemma 5.2, not comparison to the interacting configuration |
| `PredictableExitMask.lean` | Raw predictability of rational strict-past survival; simultaneous pathwise identification with the inclusive genuine-exit mask; AE measurability and nonnegative compensation of the stopped counting integral | Retains the exit jump and covers initial-outside/no-exit cases; the stopped synchronous running-cost estimate remains separate |
| `DeterministicEnvironmentConfiguration.lean`, `ConfigurationTimeDependent.lean`, `NonlinearParticleConfiguration.lean` | Actual interacting/configuration constructions use the common time-dependent framework; the constructed independent nonlinear array equals the prescribed-environment configuration and its pre-states on one full-probability event | Genuine input laws and scalar equations discharge the identification; full population convergence remains separate |
| `ExitTimeMeasurability.lean`, `StoppedPathMeasurability.lean` | Actual exit attainment and AE measurability from rational observations; jointly AE measurable stopped paths and measurable running-cost versions | No usual-filtration or optional-sampling assertion |
| `SynchronousStoppedCompensation.lean`, `SynchronousStoppedRunningSupremum.lean` | Genuine joint-exit compensation and actual expected stopped supremum inequality; includes the exit jump and derives supremum measurability | Extended integrals need not yet be finite; the population specialization establishes finiteness |
| `PopulationCouplingAlgebra.lean`, `PopulationStoppedCoupling.lean`, `PopulationStoppedIntegrability.lean` | Exact averaged coupling activity with N-independent coefficient, actual stopped expected-cost inequality, finite extended expectation and genuine real integrability from initial Lyapunov hypotheses | Sharp Gronwall and convergence are supplied by the following modules |
| `GlobalLyapunovExit.lean`, `PopulationCouplingExit.lean`, `PopulationCouplingRemoval.lean` | Genuine whole-horizon joint exit tail C/R uniform in N under uniform initial moments; pointwise stopped/unstopped agreement and actual probability bound by exit plus stopped Markov term | Supplies the cutoff-removal inequality; no final convergence or focal exchangeability theorem is asserted |
| `IntegrableGronwall.lean`, `PopulationCouplingTime.lean` | Exponential comparison for integrable subsolutions; actual stopped expected-cost horizon monotonicity, measurable real version and genuine time integrability | Does not require continuity of the expected stopped cost |
| `PopulationNonlinearError.lean`, `PopulationStoppedVolterra.lean`, `PopulationStoppedGronwall.lean` | Actual configuration error equals independent-array error; genuine fixed-time and product integrability, actual sharp real Volterra inequality, and N-independent stopped Gronwall factor | Proposition 5.3's canonical stochastic estimate, without assumed comparison, error moment or candidate continuity |
| `PopulationCouplingInitialization.lean` | Full vector marginals transfer original left moments and exact iid right mean; initial-coupling theorem supplies uniform paired Lyapunov expectations and vanishing meanDistance expectation | Does not assume expected initial-error convergence |
| `PopulationCouplingProbability.lean`, `PopulationCouplingConvergence.lean` | Actual real probability bound; fixed-R stopped expectation converges to zero, then reciprocal actual exit tails give vanishing unstopped running-cost event probabilities | Family version takes genuine initial expected pairing-error convergence; final wrapper discharges it |
| `PopulationEmpiricalCoupling.lean`, `PopulationSynchronousApproximation.lean` | Actual uniform empirical discrepancy bounded by averaged coordinate running suprema; original initialization implies canonical coupled systems with both discrepancy limits and exact initial vector marginals | First two conclusions of Theorem 5.4; the focal conclusion is supplied below and Section 6 is tracked separately |
| `ParticleRelabeling.lean`, `ConfigurationRelabeling.lean`, `PopulationStoppedExchangeability.lean` | Full paired-input measure preservation and exact noise identities; counting equations and pathwise uniqueness give actual configuration relabeling; genuine common exit invariance and equal coordinate stopped expectations | Initial exchangeability is the only symmetry premise; arbitrary localization cap choices need not be equivariant. No external whole-trajectory law identification |
| `PopulationFocalProbability.lean`, `PopulationFocalConvergence.lean`, `PopulationFocalApproximation.lean` | Actual focal event probability is bounded by one C/R exit term plus k times the stopped expectation divided by the threshold; successive limits prove fixed-focal comparison; one initialization family satisfies all three canonical Theorem 5.4 conclusions | Exact first-k event when N is at least k; Section 6's canonical nonlinear-law and fixed-time chaos limits are supplied below; Skorokhod path-space chaos remains separate |
| `IndependentArrayLLN.lean` | Exact product-law transfer from a constructed infinite iid sequence yields centered scalar empirical-mean probability limits for arbitrary integrable observables, including merely AE-measurable ones | Applies to varying row spaces without any across-row premise; actual interval-variation integrability is supplied below |
| `EmpiricalTimeGrid.lean`, `RightContinuousSupremum.lean` | Actual empirical-law cell and finite-grid inequalities; exact equal mesh; right-continuous costs have rational-plus-terminal suprema and derived AE measurability | The deterministic grid bridge has explicit displacement and law-modulus premises; the actual stochastic application below discharges them |
| `NonlinearEmpiricalSupremum.lean` | Genuine nonlinear particle path regularity and continuity of the environment give simultaneous right continuity of the actual independent empirical error; its exact uncountable running supremum is AE measurable | No assumed error continuity or supremum measurability; uniform convergence is supplied below |
| `NonlinearActivityBound.lean`, `NonlinearPathVariation.lean` | Genuine integrable current activity and its marginal-moment bound; actual predictable accepted-jump variation, measurability, interval monotonicity and exact compensation | Finiteness is not assumed in compensation; its derivation follows below |
| `NonlinearVariationDisplacement.lean`, `NonlinearVariationBounds.lean` | All-time same-path displacement bound on one event, finite expected interval variation with explicit coefficient, AE finiteness, ordinary integrability and Wasserstein time modulus | Lemma 6.1 estimates for actual canonical paths; includes the right-endpoint jump and derives all integrability |
| `NonlinearEmpiricalUniform.lean` | Finite-grid error bounds and exact record-product LLN prove the true uniform independent empirical probability limit, including the zero horizon | Proposition 6.2 under the manuscript assumptions; no stochastic variation, uniform convergence or across-row independence premise |
| `PopulationEmpiricalLimit.lean` | Exact initial-record/noise projection transfers the actual paired-space limit to the canonical original-vector-law population; uniform empirical Wκ and generalized-moment errors tend to zero in probability | Theorem 6.3's canonical uniform conclusions; no external trajectory identification or J1 path-map measurability is assumed |
| `CoupledLawConvergence.lean` | Genuine measurable coupling with vanishing mismatch controls bounded continuous tests and gives weak convergence of pushforward probability laws | Countable state spaces, varying row spaces, and exact comparison marginals; no weak-limit premise |
| `PopulationFixedTimeChaos.lean` | Actual canonical fixed-k laws at each fixed time converge weakly to the product nonlinear marginal from manuscript initialization | Fixed-time Corollary 6.4 only; no joint-time or Skorokhod path-space conclusion |
| `SkorokhodJ1.lean` | Genuine time-change J1 metric and Borel structure on actual càdlàg paths; separation, triangle inequality, convergence criterion, and uniform-to-J1 convergence | Actual random path-map measurability and path-space chaos remain open; no path-space completeness claim |
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
| `TimeGridRefinement.lean`, `PoissonCoordinateSum.lean`, `MarkedBoundedAlgebraLaw.lean`, `MarkedPoissonMeasure.lean` | Finite Boolean rectangle decomposition on a monotone time grid; product-Poisson summation; exact product law and joint independence of genuine random-measure masses on any finite disjoint measurable family of finite intensity | Fixed noise label and finite target intensities; the arbitrary-intensity and cross-label extension is supplied below |
| `MarkedInfiniteIntensity.lean`, `IndependentNoiseLabels.lean`, `MarkedFullPoissonLaw.lean` | Infinite-intensity sets have genuine mass∞ almost surely; grouping disjoint strip sigma algebras proves independence of whole random counting measures; exact mixed finite/infinite product laws and full finite-label mass-array law | Arbitrary measurable planar sets, disjoint only within each label; no claim of full future-array independence from the entire marked history |
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
| `TimeDependentFrozenProcess.lean`, `TimeDependentRateLocalization.lean`, `TimeDependentFrozenExit.lean` | Actual proposal-time rate decisions; measurable finite-active recursion, confinement, càdlàg regularity, genuine finite-attained first exits; horizon-local cutoff independence and stopped compatibility through clamped rates | Finite active sets and fixed horizons; global exhaustion and cutoff removal are supplied below |
| `PredictableTime.lean`, `TimeDependentHistory.lean`, `TimeDependentPredictable.lean`, `TimeDependentInitial.lean` | Measurable deterministic time coefficients are predictable; actual observed-history reconstruction and raw adaptation; strict-past state, left-limit identification and independent initial-record extension | Finite-active construction; all-sample measurable versions retain a fixed fallback at nonpositive times |
| `TimeDependentJumpIdentity.lean`, `TimeDependentCountingIdentity.lean`, `TimeDependentInitialCounting.lean` | Actual finite-event telescoping and counting-measure identity, pathwise integrability and product initial-state lift | Time-dependent acceptance is evaluated at the proposal time; finite height cutoff remains |
| `TimeDependentIntensity.lean`, `TimeDependentInitialCompensation.lean`, `TimeDependentGeneratorIntegral.lean`, `TimeDependentPreStateTime.lean`, `TimeDependentDynkin.lean` | Finite-active/finite-box signed integrability and compensation; time-null prestate/current-state equivalence; actual initialized Dynkin change identity and sample-time Fubini | Time sections measurable and active rates nonnegative/bounded only during the horizon; separate expectations require integrability of the initial test value, but changes do not |
| `TimeDependentHistoryIntegral.lean` | All-sample terminal-history reconstruction of the actual time-dependent process and its time integrals | Raw history and countable states; total Bochner-integral measurability itself imposes no probability, moment or integrability premise |
| `TimeDependentMartingale.lean`, `TimeDependentGeneratorMartingale.lean` | Actual counting-integral compensation gives a raw-filtration martingale; exact history measurability and height integration yield the current-state generator martingale, integrability and zero expectation | All-time generator statement assumes the active rate cap at every positive time; horizon-local equality/integrability need only that horizon's bounds, and clamping supplies the all-time premise |
| `TimeDependentExpectation.lean`, `TimeDependentLyapunovBound.lean`, `TimeDependentInitialExit.lean` | Actual expectation primitive, continuity and Fubini; affine-exponential frozen Lyapunov estimate; genuine first-exit threshold identity and Markov tail bound | Derived from pointwise drift and initial integrability, without assumed stochastic expectation or exit estimates |
| `TimeDependentLocalization.lean`, `TimeDependentGlobalProcess.lean`, `TimeDependentGlobalActivity.lean` | Positive rate caps chosen on canonical finite sublevels; actual stopped compatibility and monotone exits; all-sample raw measurable/adapted limit patch; eventual finite-horizon agreement, càdlàg paths and finite proposal lists containing every change | Caps need not increase; the generic path conclusions have an explicit exhaustion premise that the next module derives |
| `TimeDependentNonexplosion.lean`, `TimeDependentGlobalMoment.lean` | Frozen drift and Markov tails give actual almost-sure exit exhaustion and global nonexplosion; finite-horizon agreement and Fatou give genuine integrability plus real and extended moment bounds | Genuine coefficient, Lyapunov and initial-integrability hypotheses; no supplied exit, expectation or exhaustion conclusion |
| `TimeDependentGlobalCounting.lean`, `TimeDependentEquationUniqueness.lean`, `TimeDependentGlobalUniqueness.lean` | Actual predictable global pre-state is the path left limit; no-cap/no-spatial-indicator counting equation and pathwise integrability; causal uniqueness from singleton or separating test equations | Counting transfer uses exhaustion, discharged in the actual environment wrapper; candidate uniqueness assumes only càdlàg paths, the same initial state and equations, not candidate moments or finite activity |
| `IntegralGronwallComparison.lean`, `TimeDependentLyapunovComparison.lean`, `TimeDependentGlobalComparison.lean` | Forced scalar comparison; pointwise time-dependent generator bounds yield frozen expected-drift inequalities; global Fatou comparison preserves a deterministic Lyapunov envelope | Coarse affine drift separately proves nonexplosion; the fine time-dependent bound yields the envelope without assuming an expected-drift inequality |
| `CommonFrozenExit.lean` | Genuine extended first-exit infimum and pre-exit membership; almost-sure finite attainment, zero/infinite boundary cases, nested-exit monotonicity, and stopped larger path equals smaller path including its exit jump | Exit probability estimates and stopping-time properties are supplied below |
| `CommonNoiseFiltration.lean` | Actual observation filtration from arrived labelled marks, independent of the process; monotonicity and ambient measurability; all-sample history factorization; measurable time evaluations and adaptedness for deterministic or time-zero-measurable initial states | No full-σ-algebra shortcut or process-generated filtration; marked-future independence and predictable compensation are proved in dedicated modules |
| `CommonFrozenStopping.lean` | Actual completed ambient probability law; minimal augmentation of each raw history by ambient null sets; exact original first exit is a stopping time, completed-measurable and raw AE-measurable; raw time-zero-measurable initial states included | Infinity uses only the supremum of finite histories; right continuity and optional sampling are not claimed; the arbitrary-initial product extension is supplied below |
| `CommonInitialNoise.lean` | Actual arbitrary initial-record/noise product law, exact full marginals and independence, including measurable initial-state maps; initial-plus-observed-noise filtration; exact process initial law; joint measurability, adaptedness, and almost-sure regularity and stopped compatibility | Accepts the paired-array laws from Lemma 5.1; frozen generator identification is supplied below, while the population comparison is supplied by the population modules |
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
| `ActualNonexplosion.lean`, `ConfigurationNonexplosion.lean` | Genuine exit bounds and exhaustion from the raw generator drift; actual nonexplosive global configuration construction with measurable adapted paths | No given moment bound or exhaustion conclusion; arbitrary initial laws and global equation uniqueness are supplied below; canonical empirical convergence is supplied by the population limit modules |
| `GlobalLyapunovMoment.lean`, `ActualGlobalMoment.lean` | Fatou gives integrability and exponential expectation control of the actual global Lyapunov value | Current-time expectation, not expected running maximum or all weighted activity bounds |
| `GlobalLocalizedCountingIdentity.lean`, `ActualGlobalCounting.lean` | Predictable global pre-state identified with its actual left limit; genuine global rate-threshold counting equation and pathwise integrability; configuration specialization from LyapunovControl | No active-set or height cutoff in the global integrand; global equation uniqueness is supplied below |
| `DiscreteCausalUniqueness.lean`, `CountingEquationUniqueness.lean`, `GlobalCountingUniqueness.lean`, `ActualGlobalUniqueness.lean` | Discrete first-disagreement uniqueness; genuine left-limit counting equations for separating tests; actual finite-coordinate particle specialization | Candidate càdlàg paths, same initial record, and same driving measure; no candidate localization or finite-activity premise |
| `ArbitraryInitialNonexplosion.lean` | One full noise event for all deterministic states yields arbitrary-initial-law exhaustion, càdlàg paths, finite activity, counting equations and coordinate uniqueness | Countable states and autonomous rates satisfying the Lyapunov drift; no initial moment for path properties, while moment estimates keep their integrability premises |
| `FiniteSupportGeometry.lean`, `FiniteSupportGlobal.lean`, `GlobalFiniteSupportDrift.lean` | Finite backward influence of configuration tests; bounded raw generator; product integrability and current-state compensator identification | Finite support is essential to this argument; unbounded-test martingales are not inferred |
| `InitialConditionalCompensation.lean`, `PredictableHistoryTruncation.lean`, `PredictableCountingMartingale.lean` | Signed compensation tested on actual past events; conditional zero for future integrals; counting-equation-to-martingale bridge | Predictability and product integrability are explicit in the generic bridge, proved for the application |
| `GlobalHistoryIntegral.lean`, `ConfigurationMartingale.lean`, `ConfigurationForwardEquation.lean` | All-sample terminal-history reconstruction; raw-adapted current-state generator martingale; weak forward equation by actual Fubini | Any independent initial probability law, finitely supported configuration tests; no initial moment; semigroup/strong Markov statements and the configuration specialization of forward-law uniqueness remain separate |
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
gives joint independence. This finite-intensity theorem has no target-law
or independence premise. `MarkedInfiniteIntensity` then proves that the actual
extended mass of every fixed measurable infinite-intensity set is infinite
almost surely, by bounding every finite lower tail with those of growing
bounded-box Poisson counts. `IndependentNoiseLabels` groups the independent
strip sigma algebras by label and proves joint independence of the entire
label records and random counting measures, without a countability assumption
on the label type. `MarkedFullPoissonLaw` combines these results: finite
intensity has the embedded Poisson law, infinite intensity has the point mass
at infinity, and any finite disjoint family has the product of these laws.
Its `countingMeasure_arrays_map` theorem gives the full nested product across
finitely many injected labels. Sets from different labels may overlap;
disjointness is required only within a label. These are genuine extended
counting-measure masses, without a natural-floor convention at infinity.

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

The autonomous shared-noise construction uses rates `J → E → ℝ` and covers
state feedback in a finite interacting configuration. The new time-dependent
frozen family uses `J → ℝ → E → ℝ`, evaluating the coefficient at each actual
proposal time. Finite-box path regularity needs no rate sign or dominance
condition; interpreting the path as the intended intensity-driven system
requires nonnegative rates and a valid rate bound. `TimeDependentRateLocalization`
freezes the time argument outside `[0,T]` and proves agreement with the original
recursion throughout that horizon. Thus rate bounds only on the chosen horizon
suffice for cutoff independence and nested compatibility, including the exit
jump. `DeterministicEnvironmentRates` discharges time measurability and
finite-active-set bounds for continuous law curves from the manuscript's
coupling and activity assumptions: diagonal coupling cost bounds each rate
difference, and continuity of the actual moment map bounds moments on compact
horizons. `TimeDependentHistory` and `TimeDependentHistoryIntegral` prove
raw history measurability by exact observed-record reconstruction, including
time integrals. Predictable strict-past states and finite-list telescoping give
the actual signed counting equation, also on an independent initial-record
product. Finite-box integrability, compensation and height integration then
prove `TimeDependentDynkin.dynkin_change` and the current-state generator
formula. The change is integrable for arbitrary initial laws; the usual
separate-expectation formula requires an integrable initial test value.
`dynkin_expectation_integral` derives the ordinary Lebesgue integral of the
expected generator by genuine product-integrability/Fubini.
`TimeDependentMartingale` derives the actual compensated martingale from
conditional compensation; `TimeDependentGeneratorMartingale` identifies the
classical current-state formula and proves its raw adaptedness by exact
terminal-history reconstruction. Its all-time rate bound is discharged for
endpoint-clamped environments; its horizon-specific identification only needs
bounds on that horizon. `DeterministicEnvironmentFrozen` supplies the complete
finite-active-set application to the paper rates. It chooses its positive cap
from the proved activity bound, derives time measurability from the diagonal
coupling estimate, and invokes the actual initialized construction and its
counting/Dynkin/martingale results. Its `dynkin_change_on_horizon` explicitly
recovers the original unclamped generator `q.generator (v s)` on `(0,t]` for
`t≤T`. Its all-time martingale concerns the clamped environment.

`TimeDependentLocalization` selects positive bounds on canonical finite
Lyapunov sublevels. Actual stopped compatibility gives monotone exits even when
the selected rate caps are not monotone. `TimeDependentExpectation`,
`TimeDependentLyapunovBound` and `TimeDependentInitialExit` derive the frozen
expectation and actual exit bounds; `TimeDependentNonexplosion` discharges
exhaustion from affine drift and an integrable initial Lyapunov value.
`TimeDependentGlobalProcess` constructs the raw jointly measurable, adapted
limit path and proves finite-horizon agreement and càdlàg regularity.
`TimeDependentGlobalActivity` bounds every horizon's changes by a finite actual
proposal list. `TimeDependentGlobalMoment` obtains genuine integrability and
ordinary/extended moment bounds by Fatou. `TimeDependentGlobalCounting`
identifies its predictable pre-state with the actual left limit and transfers
the counting equation and pathwise integrability after removing both cutoffs.
`TimeDependentGlobalUniqueness` proves same-input uniqueness from separating
test equations and càdlàg regularity, with no candidate moment, rate bound,
localization or finite-activity premise.

`DeterministicEnvironmentLyapunov` discharges the coefficient hypotheses from
the manuscript's actual coupling, activity and Lyapunov assumptions. An extended
Lyapunov moment bound first gives genuine integrability before the ordinary
moment is used in the generator estimate. `DeterministicEnvironmentProcess`
uses these bounds in the actual initialized global construction. Its definition
does not take a moment estimate as an input; its nonexplosion and moment theorems
prove the needed consequences. The manuscript curve's time-zero constraint
supplies initial integrability, while its exact pointwise envelope supplies
the time-dependent drift bound. Original environment rates are recovered on
the selected horizon; equations at all later times concern the endpoint-clamped
extension. Finite coordinate projections separate states, yielding uniqueness
from the manuscript's coordinate counting equations on the same canonical noise.

`IntegralGronwallComparison` proves the forced deterministic comparison used by
`TimeDependentLyapunovComparison`. Actual Dynkin and product integrability
derive its expected-drift inequality from pointwise generator control.
`TimeDependentGlobalComparison` uses coarse affine drift for exhaustion and
the finer time-dependent drift for the envelope before passing to the global
path by Fatou. `DeterministicEnvironmentEnvelope` proves the scalar derivative
and integral identity for the manuscript's exact exponential K(t), then obtains
actual integrability and both ordinary and extended moment bounds by K(t).
`DeterministicEnvironmentLaw` constructs the actual pushforward MomentLaw at
each time, proves its initial law, and derives its finite adapted moment and
integral identities. `TimeDependentStochasticContinuity` proves that no actual
indexed proposal occurs at a fixed deterministic time, using nonatomic arrival
laws and a countable intersection. Frozen local constancy and global horizon
agreement then give almost-sure continuity at that time. The event may depend
on the time, so this does not assert continuous sample paths.
`LawCurveContinuity` uses the actual joint pushforward coupling and derives
uniform integrability of adapted distances from the genuine superlinear
Lyapunov bound. Vitali converts fixed-time path convergence to Wκ continuity.
`DeterministicEnvironmentEvolution` combines these proved facts into the actual
prescribed-environment self-map of ManuscriptCurves, with exact pushforward
identity, initial law and envelope.

`SynchronousPositiveIncrement` integrates the actual shared-height update into
three positive activity terms, including the shared jump. The two projections
of `SynchronousFrozenCounting`'s genuine paired recursion are exactly the two
existing frozen paths. Telescoping their finite list gives positive-increment
domination; genuine exhaustion and a common maximum rate cap transfer it to the
global paths in `SynchronousGlobalCounting`, simultaneously for every prefix
of a fixed horizon. `TimeDependentGlobalPreStateTime` removes pre-state notation
from time integrals outside a null set. `SynchronousCompensation` proves
predictability and applies the actual nonnegative compensation theorem; exact
height integration then yields the extended expected-distance inequality.
Infinite values are allowed at this stage, so no expected-activity bound or
stochastic coupling inequality is an input.

`CouplingExpectation` derives genuine distance/activity integrability from the
pointwise coupling assumption and actual finite endpoint moments. Both input
moments and both output expected weights are bounded by K(T), giving exactly
`A=L(1+2K(T))`. `CoupledDistanceContinuity` proves expected-distance continuity
from the four-point metric inequality and superlinear uniform integrability.
`DeterministicEnvironmentVolterra` uses those independent bounds to convert the
extended compensation inequality into a finite real integral inequality.
`VolterraGronwall` differentiates the integrating-factor response and uses FTC
and scalar comparison to derive the exponential convolution. This proves the
fixed-time expected-distance bound and the actual output-law Volterra bound
required by Bielecki contraction.

`SynchronousRunningSupremum` also treats the actual uncountable running
supremum. The constructed paths are locally constant to the right on one full
event; hence rational observations and the terminal value determine that
supremum, giving AE measurability under the original product law. The full
prefix inequality and nonnegative compensation bound its extended expectation
by integrated expected activity without a finite-supremum premise.
`DeterministicEnvironmentRunningSupremum` then proves the exact manuscript
convolution estimate for that full expected supremum. It bounds integrated
activity using the already proved fixed-time response and the response's
integral identity, so continuity of the running supremum is unnecessary.
Finite expectation, almost-sure finiteness and genuine integrability of the
real supremum follow from the estimate before the real expectation bound is
stated.

`NonlinearFixedPoint` supplies the actual evolution and its proved Volterra
estimate to the earlier Bielecki theorem, using the concrete weight `2A+1`.
It proves exactly one fixed curve in ManuscriptCurves under genuine finite
initial Ψ integrability. Evaluating the existing process construction at that
curve gives exact marginal self-consistency, the envelope, raw adaptation,
càdlàg regularity, exhaustive exits and the no-cutoff counting equation with
its actual left state. Self-consistency is on the selected `[0,T]`; after that
interval the deterministic environment is held at its endpoint.

`DeterministicEnvironmentFiniteSupport` proves that every state affecting a
finite-support test lies in a finite set of actual jump predecessors, including
boundary rejections. The activity hypothesis gives one rate cap on that set
throughout the clamped horizon. Hence the unrestricted accepted increment
identically equals a bounded-height finite-influence integrand, and both its
counting integral and its current-state generator are genuinely integrable.
`DeterministicEnvironmentForward` combines signed predictable compensation,
the actual counting equation, the pre-state/current time-null identity and
Fubini to prove the actual weak forward equation. It then uses the proved
fixed-curve marginal identity to obtain the nonlinear weak equation.

`FiniteJumpForward.IsSolution` records the probability laws, the tested
integral equation and genuine time integrability for every finitely supported
test. Atomic continuity follows from the integral primitive; it is not a
candidate hypothesis. The uniqueness route differs from the manuscript's
last-jump iteration. `TimeDependentFrozenForward` derives the actual finite
mass system from frozen Dynkin and Fubini, with outgoing boundary loss retained
and self-jumps cancelled. `FiniteJumpRestriction` splits any full weak solution
into the same internal system and a finite external predecessor inflow. For
targets inside the active set, that omitted inflow is nonnegative.
`FiniteForwardComparison` derives inequalities on every subinterval from the
actual integrated equalities. A last-nonpositive-time argument controls the
diagonal correctly, and Gronwall gives comparison. It does not use the invalid
shortcut of a one-sided inequality anchored only at time zero.
`FrozenForwardMinimality` therefore bounds each actual frozen mass by the
candidate's atom while the target lies in the active set.

`TimeDependentFrozenLawLimit` uses genuine exit exhaustion to obtain eventual
agreement of local and global paths, then applies bounded convergence to
singleton indicators. Every state eventually belongs to the increasing active
sets. Atomic domination therefore passes to the actual global pushforward,
and probability normalization turns domination into equality.
`TimeDependentForwardUniqueness` requires no moment bound on the competing
probability weak law. `DeterministicEnvironmentForwardUniqueness` discharges
its construction and coefficient hypotheses under the paper assumptions for
any prescribed Wκ-continuous environment with a bounded genuine Ψ moment and
finite initial Ψ moment. The environment's time-zero value need not equal the
initial law. `DeterministicEnvironmentGeneralForward.isSolution` supplies the
matching existence theorem for that general environment, with all finite-test
integrability proved from the constructed process. The combined
`actualLaw_isSolution_and_unique` theorem identifies all competing laws on
`[0,T]`; it does not identify their arbitrary continuations beyond that interval.
`DeterministicEnvironmentGeneralLaw` now supplies the general actual output-law
Wκ continuity as well. It first derives genuine integrable Ψ and weight moments,
packages the exact pushforward, then combines the uniform affine-exponential
bound with diffuse proposal times and superlinear uniform integrability.
The initial value is exactly the separately supplied initial law. The arbitrary
external-space and completed right-continuous filtration formulation of
Proposition 4.2 remains outside this canonical construction.

`AtomicTransportContinuity` upgrades atomic convergence to actual Wκ convergence.
Nonzero atoms of a finite truncation are either preserved or absent, while its
collapsed zero atom follows from finite retained masses and normalization.
Both approximating and target laws have uniformly small truncation costs under
a genuine superlinear Ψ bound. This proves transport continuity of every
moment-bounded weak candidate from its tested integral equation, without a
candidate-continuity assumption.

`DeterministicEnvironmentGeneralCoupling` identifies each such candidate with
its actual prescribed-environment process by linear uniqueness. Its genuine
Ψ bound therefore controls the actual endpoint moments. The two processes
share the initial record and driving noise; predictable compensation gives the
extended distance inequality, and superlinear uniform integrability derives
continuity of their expected distance. A continuous finite dominating function
justifies conversion to the real integral inequality. The actual joint law
bounds input transport by expected distance.
`NonlinearForwardUniqueness` takes a common B bounding the two candidate moments,
sets A=L(1+2B), and applies Gronwall to m(t)≤2A∫₀ᵗm(s)ds. Thus every
moment-bounded weak solution equals the constructed fixed curve on [0,T].
The exact K(t) envelope is a consequence of that equality; no unbounded-test
forward equation is assumed or used. The canonical curve provides existence,
and `existsUnique_interval_solution` is an exact unique-existence statement
on the interval domain for arbitrary law functions with genuine tested time
integrability.

`FiniteJumpForwardRestriction` preserves genuine integrability when shrinking
a horizon and changing coefficients or laws only outside it.
`NonlinearHorizonConsistency` restricts a larger fixed curve, retaining the
same pointwise K(t) envelope, and transfers its actual weak equation. The proved
uniqueness identifies the restriction with the smaller fixed curve. Actual
process marginals and deterministic environments consequently agree on every
overlap, including endpoints and zero horizons. The subsequent
`NonlinearPathConsistency`, `NonlinearGlobalProcess`, `NonlinearGlobalCounting`
and `NonlinearGlobalForward` modules also give actual pathwise agreement, one
all-time canonical realization, its own-marginal equation and global weak-law
uniqueness. Arbitrary externally supplied PRM spaces remain outside this result.

For the autonomous configuration construction, `InitialFrozenExpectation`
supplies genuine Fubini and
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
statements, the configuration specialization of forward-law uniqueness, and
right continuity of the completed filtration remain open.


## Next connections to formalize

1. Extend bounded-rectangle independence from the whole common marked
   history to joint future windows/categories within strips. The complete
   measurable-set Poisson laws, including infinite-intensity masses and
   simultaneous distinct labels, are now proved.
   Scalar future rectangle independence already suffices for the proved
   predictable compensation theorem; this stronger law is not a prerequisite
   for the next drift argument.
2. Prove the usual right-continuous filtration, optional sampling, and required
   semigroup/strong Markov statements. Actual nonexplosion, global counting
   equations, coordinate-equation pathwise uniqueness, the finite-support
   generator martingale and weak forward equation are now proved, including
   arbitrary independent initial laws. Lyapunov expectation bounds retain their
   initial-moment assumptions.
3. Extend the actual all-time canonical nonlinear process to arbitrary externally
   supplied PRM spaces with the required usual filtration. Pathwise horizon
   compatibility, own-marginal equations, global moment-bounded law uniqueness
   and the exact envelope are already proved.
4. Prove the actual random path maps measurable for the constructed Skorokhod
   J1 Borel structure, then establish path-space chaos. The canonical uniform
   empirical and generalized-moment limits and fixed-time finite-particle chaos
   are proved from the manuscript initialization assumptions. Preserve the
   original paper's weaker initialization as a separate, unfinished target.
5. Complete the carrying-capacity application package, including unbounded-test
   justification for the closed mean ODE, the stated general Lyapunov exponents,
   and the Wp comparison of Remark 2.1. The existing scalar/quadratic checks do
   not yet constitute those application corollaries.

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
