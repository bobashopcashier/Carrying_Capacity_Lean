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
those processes and that curve remains separate. The other full stochastic
results in this table remain **not yet formalized**. Algebraic sublemmas and
pathwise frozen constructions do not prove a full stochastic proposition.

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
| `PoissonPastIndependence.lean` | Full past-count sigma algebra built from directed finite observation families; actual future increment independent of that entire past; natural-filtration identification; conditional increment expectation r·t | Raw scalar clock filtration only; the marked noise has a larger observation history and still needs its own independence proof |
| `PoissonMartingale.lean` | Actual compensated count N_t−rt is a martingale on nonnegative times; integrability, adaptedness, zero conditional increments and zero mean; deterministic-horizon stopped martingale | Does not assert random optional sampling or a compensator for the marked counting measure |
| `MarkedNoise.lean` | A single actual probability space and measurable counting-measure family from independent unit vertical strips; a common probability-one event gives local finiteness for every real time/height cutoff and no simultaneous arrivals | Full marked PRM characterization and compensation remain open |
| `MarkedIntensity.lean` | Actual mark/clock product probabilities, count expectations, translated uniform-strip decomposition, and exact expected counting measure equal to quadrant Lebesgue measure; full nonnegative deterministic Campbell identity and expected mass of every measurable set | First-moment identities do not establish the full marked Poisson law, past independence, or predictable random-integrand compensation |
| `FrozenCompatibility.lean` | Actual first-exit indices for nested frozen recursions; agreement including the exit jump; monotone exit indices; stopped larger recursion equals the permanently frozen smaller one; stopped continuous-time agreement under a common clock | Uses the same decoder and proposal sequence; cutoff-list compatibility is supplied below |
| `ChronologicalEvents.lean` | Measurable finite-set selection and chronological sorting; jointly measurable actual bounded-box event lists; exact membership and strict ordering; time-prefix and height-filter identities simultaneously for all boxes almost surely | Does not by itself identify the stochastic intensity of the counting measure |
| `RejectedProposals.lean` | Removing proposals rejected at every active state preserves the actual frozen recursion, including its accepted exit jump; height-bound specialization | Deterministic list identities, used to compare actual bounded-box paths |
| `CommonFrozenProcess.lean` | Frozen paths defined from the shared marked noise's chronological events; joint measurability and finite-range confinement; almost-sure bound independence, permanent freezing, and continuous-time nested-set agreement through the exit jump | Autonomous rates on a countable state space with finitely many directions; no PRM integral identity or generator law yet |
| `CommonFrozenRegularity.lean` | Almost-sure local right constancy and left constancy, càdlàg regularity, zero-time value and initial interval for all cutoffs and initial states | These path properties do not identify compensation or prove adaptedness |
| `CommonFrozenExit.lean` | Genuine extended first-exit infimum and pre-exit membership; almost-sure finite attainment, zero/infinite boundary cases, nested-exit monotonicity, and stopped larger path equals smaller path including its exit jump | Exit probability estimates remain open; stopping-time properties are supplied below |
| `CommonNoiseFiltration.lean` | Actual observation filtration from arrived labelled marks, independent of the process; monotonicity and ambient measurability; all-sample history factorization; measurable time evaluations and adaptedness for deterministic or time-zero-measurable initial states | No full-σ-algebra shortcut or process-generated filtration; marked-future independence and compensators remain open |
| `CommonFrozenStopping.lean` | Actual completed ambient probability law; minimal augmentation of each raw history by ambient null sets; exact original first exit is a stopping time, completed-measurable and raw AE-measurable; raw time-zero-measurable initial states included | Infinity uses only the supremum of finite histories; right continuity and optional sampling are not claimed; a separately enlarged initial/noise product filtration still needs its completion/stopping bridge |
| `CommonInitialNoise.lean` | Actual arbitrary initial-record/noise product law, exact full marginals and independence, including measurable initial-state maps; initial-plus-observed-noise filtration; exact process initial law; joint measurability, adaptedness, and almost-sure regularity and stopped compatibility | Accepts the paired-array laws from Lemma 5.1 without additional moments; completed-product stopping times and stochastic trajectory coupling estimates remain separate |
| `ThinningKernel.lean` | Finite positive bound on active rates; exact accepted-label mass; expected proposal increment times card(J) C equals the frozen generator | Requires positive C and 0≤q≤C; continuous-time generator identification still needs compensation |
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
path. The exit estimates themselves, and measurability/adaptedness of the
patched process, remain separate proof obligations.

`CommonInitialNoise.lean` supplies the independent initial-record extension.
For the coupling in Lemma 5.1, take the initial record to be the whole paired
array with its constructed joint law. The actual product keeps that full law
and makes the entire record independent of the entire noise sample. Either
coordinate projection can initialize an adapted frozen system, and the exact
initial marginal law, almost-sure regularity, and stopped compatibility are
proved. The existing completed-noise first-exit theorem has not yet been lifted
to the enlarged product filtration.

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
its values or assuming right continuity. The full marked PRM SDE and Lyapunov
exit estimates remain separate.

The shared-noise construction currently uses autonomous rates `J → E → ℝ`.
It covers state feedback in a finite interacting configuration, but has not yet
been extended to rates with a deterministic time-dependent environment. Its
finite-box path regularity needs no rate sign or dominance condition; interpreting
the path as the desired intensity-driven system still requires nonnegative rates
and a valid rate bound. The stopping identities above are pathwise statements,
not optional-stopping or martingale identities.


## Next connections to formalize

1. Prove the full marked PRM law and independence from the marked past. The
   scalar clock's full-past independence and compensated martingale are proved;
   the marked measure's intensity and deterministic Campbell formula are proved.
   Neither result alone supplies the marked predictable compensator.
2. Prove predictable compensation/Dynkin and stopped Gronwall, including the
   completed-filtration bridge on the enlarged arbitrary-initial-state space.
   Derive reciprocal exit estimates before applying the existing a.e. patching
   theorem to the actual stochastic system.
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
