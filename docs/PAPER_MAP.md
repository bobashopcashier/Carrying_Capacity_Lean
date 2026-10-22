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
| Proposition 2.4 | Exchangeability and Markov empirical process | Not formalized |
| Theorem 2.5 | Deterministic nonlinear forward law and empirical path convergence | Not formalized |
| Remark 2.6; Corollary 2.7 | Fixed-time and path-space propagation of chaos | Not formalized |
| Lemmas 3.1–3.3; Propositions 3.5, 3.7–3.9; Lemmas 3.11–3.12 | Symmetrization, domination, freezing, tightness | Not formalized |

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

All full stochastic results in this table remain **not yet formalized** unless
an independently compiled Lean declaration explicitly supplies the entire
statement with its original hypotheses. Algebraic sublemmas are not proofs of
these full propositions.

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
| `Transport.lean` | Genuine probability measures with integrable Kκ; all measure couplings with their probability property; independent/diagonal/swapped couplings; integrability of every coupling cost; the infimum Wκ with zero self-distance and symmetry; moment difference bounded by Wκ; moment convergence from Wκ convergence | Wasserstein separation, triangle inequality, gluing lemma, optimal transport, and completeness remain missing |
| `Framework.lean` | Correct birth/death/type-transition maps, boundary rates, generators; original total-variation growth/Lipschitz assumptions; extension's positive-increment coupling, activity, and Lyapunov hypotheses | These are assumption structures, not proofs that arbitrary rates satisfy them; initialization and full nonlinear forward equation are not encoded |
| `FiniteGenerator.lean` | Exact 1/N empirical-generator identity and averaged Lyapunov drift | Empirical-law interpretation, Dynkin, and expectation bounds remain separate |
| `RateControl.lean` | Admissible jumps have ρκ-length at least one; total rate ≤ weighted activity; empirical Lyapunov sublevels of N-lineage configurations are finite for N>0 | Does not yet construct a finite-strip PRM event list or derive its stochastic properties |
| `Freezing.lean` | Finite proposal recursion, retention of exit jump, permanent freezing, compatible path patching, a.e. exhaustion from reciprocal exit tails, a.e. unique pointwise patch | No PRM construction, derivation of exit bounds, or measurability/adaptedness of the patched process |
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


## Next connections to formalize

1. Construct the empirical `MomentLaw` and its integrals. Connect
   `FiniteGenerator`'s abstract environment map and averages to it.
2. Prove Wasserstein separation and triangle via gluing,
   and completeness, plus the transport topology needed for time-dependent
   moment laws. The current moment bound is already proved independently.
3. Formalize PRM local finiteness, chronological marked events, adapted frozen
   processes, compensation/Dynkin, and stopped Gronwall. Only after deriving the
   reciprocal exit estimate can the checked measure/patching results supply
   non-explosion for the actual stochastic system.
4. Continue with the nonlinear law and empirical coupling route in the
   dependency list. Preserve the original theorem's weaker initialization as a
   distinct target.
