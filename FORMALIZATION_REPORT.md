# Formalization report

## Purpose and scope

This report records coverage of the mathematical results in the accompanying
paper and substantive differences between the written and formal arguments. It
is a completion artifact for a paper-companion formalization, not a log of every
Lean edit.

- **Paper and version:** *BKT asymptotics for disordered pinning on the
  diamond hierarchical lattice*, research draft of 18 November 2026 (citation
  and presentation revision), the eight TeX files of `source/`, snapshot of
  18 November 2026, 19:24 CET; SHA-256 of every file in
  `docs/SOURCE_SHA256.txt` (main file `bkt_diamond_simplified.tex`
  `8db09790c116d6f75147c911aa40fb1bfc5defa1668dc762c4ec8aef68bff68c`). The
  TeX source is what is read; the PDF of the same snapshot is its compilation.
- **Publication status:** not distributed, as answered by the author on
  18 November 2026
- **Declared formalization scope:** the whole paper (Sections 1 to 8), with
  Theorem `th:bkt` and its dependencies first; the introduction's Gaussian
  example, resting on a cited strict-shift theorem, is out of scope (author,
  18 November 2026)
- **Lean repository and revision:** local Git repository
  `~/LeanFormalization/BKT-diamond`, no remote; revision `fbb89a8`
- **Lean/Mathlib versions:** Lean `v4.35.0`, Mathlib `v4.35.0`
  (`56a005855ea17e0b0958f73ec801ae140b0a1679`)

Within the declared scope, aim to cover every theorem, proposition, lemma,
corollary, and other substantive mathematical claim. Conjectures, questions,
and purely expository remarks should be identified rather than presented as
proved results.

Prioritize proving every main result and its required dependencies, while
retaining all other in-scope claims as completion obligations. Clearly identify
any main result that remains unproved.

A paper result is covered only by a proved Lean declaration with the same
mathematical content, or by a checked specialization of a proved, more general
declaration. A conditional helper, nearby theorem, or matching name is not by
itself coverage.

## Result correspondence

The inventory is `docs/PAPER_INVENTORY.md`; dependencies are recorded in
`docs/DEPENDENCY_GRAPH.md`. In the declaration column, `Main.bkt` abbreviates
the declaration `DiamondPinning.bkt` in `DiamondPinning/Statements/Main.lean`,
and similarly for the other modules. Declarations outside `Statements/` are
written with their module name. Route judgments follow the seal re-audits cited
in the verification section, not merely the names of the declarations.

All 24 numbered results have matching proved frozen declarations. The three
routine identities S1.4–S1.6 have related definitions and uses in proved
arguments, but no standalone declaration with the same content was found;
under the coverage rule above they are marked `Partial`, not silently counted
as proved by a nearby definition.

| ID | Paper result | Source location | Lean declaration | Coverage | Proof correspondence | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| S1.1 | $\theta\in(0,1)$ | `bkt_diamond_simplified.tex:90` | `Model.Basic.theta_pos`, `Model.Basic.theta_lt_one` | Complete | Same main strategy | Direct consequence of $B>2$ and `Model.Defs.theta`. |
| S1.2 | Annealed mean recursion and $h_a=\log(B-1)$ | `bkt_diamond_simplified.tex:82–83` | `Model.Basic.integral_lawR_zero`, `Model.Basic.integral_lawR_succ`; `Model.FreeEnergy.freeEnergy_logc_eq_zero_aux`; `FreeEnergyBounds.logShift_le_criticalPoint` | Complete | Same main strategy | The mean recursion is explicit; vanishing at the annealed shift and $h_a\le h_c$ are proved separately. |
| `th:bkt` | T1–T5: positive residues, product equivalent, both forms of $\gamma$, and the BKT limit | `bkt_diamond_simplified.tex:98–115`; `escape.tex:241–253` | `Main.bkt` | Complete | Same main strategy | Assembles `Critical.criticalProduct`, `Response.response_transversality`, `Profile.exact_critical`, `Profile.gamma_eq_limit`, `Escape.freeEnergy_upper`, and `Escape.escape_constant`. It also proves differentiability of every $H_n$ at $h_c$ and $F(h_c+u)>0$ for $u>0$. |
| S1.3 | $K=\pi\log2/\sqrt\gamma$ and all fixed tilted logarithmic moments, including $n=0$ | `bkt_diamond_simplified.tex:117–122` | `Main.bkt`, `Main.integrable_tiltedLogPower` | Complete | Same main strategy | No extra logarithmic-moment hypothesis is imposed. |
| Gaussian example | Strict shift for lognormal disorder when $B>2+\sqrt2$ | `bkt_diamond_simplified.tex:123–126` | None, by scope decision | Out of scope | Not applicable | Relies on the cited strict-shift theorem of [GLT10]. |
| S1.4 | Recursion `eq:log-model` for $X_n=\log R_n/a$ | `bkt_diamond_simplified.tex:143–147` | Related encoding: `Model.Defs.lawR`, `Model.Env.evalR`, `Env.map_evalR_envMeasure`, `Model.Scaling.rescaledMeasure` | Partial | Local adaptation | The formalization works directly in logarithmic coordinates and does not introduce the alias $X_n$. No proved declaration stating the transformed law recursion itself was found. |
| S1.5 | $R_n^\theta=2^{X_n}$ and the formulas for $H_n$ and $J_n$ | `bkt_diamond_simplified.tex:158–160` | Related encoding: `Model.Defs.theta`, `Model.Defs.tiltedLogMoment`; `Main.integrable_tiltedLogPower` | Partial | Local adaptation | Moments are defined directly using $\log R_n-a$. No standalone declaration containing the three displayed identities in the $X_n$ normalization was found. |
| S1.6 | $NT_v=\pi/\sqrt{\gamma u}$ and $2^{-NT_v}=\exp(-\pi\log2/\sqrt{\gamma u})$ | `bkt_diamond_simplified.tex:223–227` | Related scale assembly: `Escape.escape_constant`, `Main.bkt`; `Model.Profile.IsPrePoleTime` | Partial | Local adaptation | The scale substitution $N=u^{-1/2}$ is proved inside the final assembly, but no standalone declaration of these two algebraic identities was found. |
| `lem:basic-bounds` | B1–B5: floor, moments, free energy, increments, and critical point | `critical.tex:15–54` | `Main.integrable_lawR`, `Main.integrable_tiltedLogPower`, `Main.integrable_log_lawR`, `Main.freeEnergy_tendsto`, `Main.criticalPoint_isGreatest`; `FreeEnergyBounds.floor_bounds`, `finiteSize_bounds`, `freeEnergy_nonneg`, `freeEnergy_increment`, `logShift_le_criticalPoint` | Complete | Same main strategy | Includes $n=0$ for the tilted moments and $n\ge1$ for integrability of $\log R_n$ and `eq:finitesize`. `criticalPoint_isGreatest` makes the `sSup` definition genuine. |
| `lem:mellin-correction` | Holomorphy and compact-uniform bounds for $C_n$, with `eq:C` | `critical.tex:56–77` | `Critical.correction_eq`, `Critical.differentiableOn_correction`, `Critical.correction_bounded` | Complete | Same main strategy | Stated for $n\ge1$ and $\Re z<1$. |
| `prop:criticalmoments` | Critical tilted-mass and first-moment bounds; uniform absolute first moment | `critical.tex:84–155` | `Critical.criticalMoments`, `Critical.jensen_step` | Complete | Same main strategy | Favorable-block estimate, endpoint limit $q\uparrow\theta$, and logarithmic recurrence. The constant is chosen after $B$ and before the disorder law. |
| `lem:barrier` | Lower bound for $G_n(q)$, $\theta<q<1$ | `critical.tex:163–178` | `Critical.barrier` | Complete | Same main strategy | The frozen hypotheses `hshift` and `hn` are unused by the proof; see D17. |
| `th:return` | $\liminf G_n(\theta)=1$ | `critical.tex:180–250` | `Critical.returns_to_one` | Complete | Same main strategy | Expressed by an infinitely-often upper return and an eventual lower bound for every $\varepsilon>0$. Uses a uniform polynomial Picard form of the analytic-continuation argument. |
| `th:product` | P1–P5: product estimates, `eq:Hsmall`, $\ell_3$, fourth moment, and critical rates | `product.tex:20–248` | `Critical.criticalProduct`, `Critical.criticalProduct_Hsmall` | Complete | Alternative proof in two steps | P1 uses a direct Nash estimate rather than the source's separate divergence argument; P2 uses floor-centred corrections. The rates are stated with `=Θ[atTop]` and `=O[atTop]`, including eventual $A_n>1$. `Profile.exact_critical` later sharpens them to exact limits. |
| `response:ballot` | Passage estimate for independent integrable increments | `response.tex:28–60` | `Ballot.response_ballot`, `Ballot.response_ballot_uniform` | Complete | Local adaptation | Follows the stopping-time argument. Harris's inequality is proved from scratch. The second declaration makes the dependence of the constant on the data explicit; no nonmeasurable-representative trick is used. |
| `response:spine-identities` | `response:spine` and `response:mixed-spine` | `response.tex:62–96` | `Response.spine_identities`; supporting `Response.hasDerivAt_tiltedMass`, `Response.hasDerivAt_tiltedLogMoment`, `Response.integrable_spine` | Complete | Alternative proof | Proved from a bounded-test master identity by induction, logarithmic cutoffs, and dominated convergence; valid at every field and every $n$. |
| `response:linear` | $\mathcal D_n\le C(n+1)$ | `response.tex:98–132` | `Response.response_linear` | Complete | Local adaptation | Retains the ballot/Paley–Zygmund route. Summability of the positive drift is obtained directly from `Critical.criticalMoments`; see D10. |
| `th:response` | $\mathcal E_n/\Pi_n\to\kappa\in(0,\infty)$ and $\mathcal E_n\asymp n^2$ | `response.tex:140–203` | `Response.response_transversality`; derivative support in `Response.hasDerivAt_tiltedLogMoment`, `Response.differentiableAt_deriv_tiltedLogMoment_one`, `Response.differentiableAt_kernelMean` | Complete | Local adaptation | Uses a harmonic barrier dominating the logarithmic barrier and combines the two derivative recurrences to cancel leakage. The rate is `=Θ[atTop]`; the residue is then supplied to `Main.bkt`. |
| `prop:contact-moments` | Change-of-field identities, factorial moment bounds, exponential and tilted-mass increments | `response.tex:205–265` | `Response.gibbsWeight_zero`, `gibbsWeight_succ`, `gibbsWeight_isProb`, `evalR_add_eq_gibbsMean`, `hasDerivAt_log_evalR`, `contactMoments`; integrability in `Response.integrable_contactMoment`, `integrable_contactExpMoment` | Complete | Same main strategy | Uses the contact polynomial and factorial recursion. The exponential series is integrated term by term with dominated convergence; the field-increment bound follows separately. |
| `prop:window-moments` | `response:windowA`, `windowH`, `windowK`, `windowJ`, `windowSevenHalves`, and the product ratio | `response.tex:267–342` | `Response.windowMoments`, `Response.window_derivBounds`; general support in `Response.field_envelope` | Complete | Local adaptation | All error terms are explicit absolute-value bounds with one constant in the window $0\le u(n+1)^2\le\eta$. Weighted AM–GM replaces Hölder for the $7/2$ moment; the product ratio is controlled factor by factor. |
| `cont:continuation` | Uniform transform convergence and weighted weak convergence before the pole | `scaling.tex:45–54`; `continuation.tex:1–156` | `Scaling.continuation` | Complete | Same main strategy | Uses compact $I\subset(0,T_v)$, $s>0$, and $s+\inf_I b_v>0$. Local identification, projected transport, uniqueness, base-weight recovery, and extension beyond endpoints follow the source route. |
| `scaling:compactness` | Subsequential convergence, ODEs, Riccati equation, measure representation, moments, no atom, entrance data | `scaling.tex:56–118,211–296` | `Scaling.scaling_compactness`, `Scaling.rescaledMeasure_finite` | Complete | Local adaptation | `Model.Scaling.EntranceData` packages BV/Lipschitz, integral ODE, measure, Taylor, and matching claims. Small-$s$ expansion yields the ODEs; moments come from coefficient extraction. The source's sufficiently small $\lambda T^2$ is $\lambda T^2\le\eta_0$. |
| `scaling:mellin-calculus` | Defect and kernel estimates, recurrence, floor, one-sided/BV bounds, defect sum, transform difference | `scaling.tex:124–193` | `Critical.jensen_step` for the preliminary recursion; `Scaling.defectMean_lower`, `kernel_comparison`, `defectMean_sub`, `transform_recurrence`, `transform_floor`, `transform_bounded`, `transform_difference` | Complete | Local adaptation | Uses the repaired domains of D4. `defectMean_sub` uses a mean-value estimate and `kernel_comparison`; `transform_bounded` includes an $\varepsilon_N\to0$ one-sided estimate and an `ENNReal` variation bound. |
| `lem:one-sided` | Upgrade from $L^1$ convergence and one-sided increments to locally uniform convergence | `scaling.tex:195–209` | `OneSided.one_sided_compactness` | Complete | Same main strategy | Excursion argument. A.e. strong measurability is explicit; the conclusion is uniform on compact subsets of the open interval. |
| `th:profile-identification` | Identification with $f_v$ on a common initial interval, exact critical limits, second expression of $\gamma$ | `profile.tex:8–19,62–171` | `Profile.profile_identification`, `Profile.exact_critical`, `Profile.gamma_eq_limit` | Complete | Local adaptation | Main regularization, polynomial rigidity, and Riccati route retained. Exponential/characteristic-function identification replaces the final Laplace-uniqueness step. `exact_critical` includes $\Pi_n/n^2\to3a^3/(2\ell_3)$. |
| `lem:entire-bounds` | E1 matrix growth and E2 half-plane minimal-type principle | `profile.tex:26–60` | `EntireBounds.matrix_integral_solution_exists_unique`, `matrix_integral_growth_bound`, `rightHalfPlane_bounded_of_minimal_exponential_type`, `leftHalfPlane_bounded_of_minimal_exponential_type` | Complete | Local adaptation | E1 uses Picard iteration, positive polynomial approximation, and an energy estimate with a $w$-dependent constant. E2 uses Mathlib's half-plane theorem after multiplication by $e^{-\delta z}$. |
| Hard recursion and $F_d$ (definition and supporting properties) | Limit and monotonicity of $2^{-j}\mathbb EY_j$, finite-hard lower bound, real specialization | `escape.tex:45–50,145–151` | `Escape.hardFreeEnergy_tendsto`, `Escape.hardFreeEnergy_ge`, `Escape.hardFreeEnergy_real` | Complete | Local adaptation | `F_d` is an infimum in $[0,\infty]$; subtraction is truncated there. A real-valued version is proved when $\mathbb EY_0<\infty$. This row records definitions/supporting claims, not an additional numbered result. |
| `cont:freeenergyupper` | Upper free-energy asymptotic | `escape.tex:11–36` | `Escape.freeEnergy_upper` | Complete | Same main strategy | Stated in eventual form: for every $\varepsilon>0$, the upper inequality holds eventually as $u\downarrow0$. |
| `escape:pairs` | Pair-tail lower bound | `escape.tex:52–94` | `Escape.escape_pairs` | Complete | Alternative proof | Uses an ordered pair count and a second-moment induction on a recursively represented tree. Division by four recovers exactly the source's unordered-pair estimate and constant. |
| `escape:band-exit` | Band condition implies amplification, exit by $2L$, and hard-energy lower bound | `escape.tex:96–154` | `Escape.escape_bandExit`, with `Escape.hardFreeEnergy_ge` for `escape:finite-hard` | Complete | Same main strategy | Explicit thresholds $D_*=L_*=10^4$, halving recursion, and stopping at $w\ge128$. Hard means and $F_d$ remain in $[0,\infty]$. |
| `escape:comparison` | Energy transfer and diamond-exit lower bound | `escape.tex:156–189` | `Escape.escape_comparison`; finite-mean support in `Escape.hardFreeEnergy_real` | Complete | Same main strategy | Exact floor coupling and stochastic-order induction. The first conjunct proves finite initial hard mean, justifying conversion of $F_d$ to a real number. |
| `escape:constant` | Fixed-$\lambda$ lower free-energy asymptotic | `escape.tex:199–239` | `Escape.escape_constant` | Complete | Same main strategy | Eventual lower bound with margin $\varepsilon$ and explicit positivity of $F(h_c+\lambda/N^2)$. Real $N\to\infty$; $T_v=\pi/\sqrt{\gamma\lambda}$. |

## Substantive differences

The entries below distinguish changes to the mathematical route from encoding
choices and source-side repairs. Routine implementation details and the cleanup
of helper names are not included.

### D1 — Extended-valued hard free energy

- **Paper:** `escape.tex:45–50` reads $F_d=\lim_j2^{-j}\mathbb EY_j$ as a real number for an arbitrary law on $\mathbb N$.
- **Formalization:** `Model.Hard.hardFreeEnergy` is $\inf_j2^{-j}\mathbb EY_j$ in `ℝ≥0∞`, with lower-integral means; `Escape.hardFreeEnergy_tendsto` identifies the source limit, and `hardFreeEnergy_real` gives a real specialization when the initial mean is finite.
- **Reason:** An admissible infinite-mean initial law can satisfy the band hypothesis while every hard mean is infinite. A real Bochner reading would silently turn those means into zero.
- **Classification:** Imprecision.
- **Mathematical effect:** The hard statements are valid for every initial law, with truncated subtraction in `hardFreeEnergy_ge`; the floor law used by `escape:comparison` is proved integrable, so the model-facing comparison remains real.
- **Paper argument checked:** Yes, after adopting the extended-valued convention; no numbered conclusion changes.
- **Manuscript action:** Recommendation R1 recorded in `MANUSCRIPT_RECOMMENDATIONS.md`.
- **Unresolved obstruction, if any:** None.

### D2 — Constructed law-level free energy and critical point

- **Paper:** $F$ is the limit of normalized logarithmic expectations and $h_c$ is the supremum of its zero set.
- **Formalization:** `Model.Defs.lawR` constructs the law recursively; `freeEnergy` uses `limUnder`, and `criticalPoint` uses `sSup`. The environment coupling is separate, with `Env.map_evalR_envMeasure` connecting it to `lawR`.
- **Reason:** Lean's total operations need characterizations before they can be used as the source's limit and supremum.
- **Classification:** Formalization choice.
- **Mathematical effect:** None after `Main.freeEnergy_tendsto` and `Main.criticalPoint_isGreatest`: the zero set is nonempty, bounded above, and contains its greatest element. The statements construct $F$ and $h_c$ rather than postulating them.
- **Paper argument checked:** Yes; the companion theorems exclude an unspecified `limUnder` value and an empty/unbounded `sSup` artifact.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D3 — Residues as parameters in internal interfaces

- **Paper:** $\ell_3$ and $\kappa$ are limits established in Sections 3–4 and then used in Sections 5–8.
- **Formalization:** Scaling, profile, continuation, and energy statements take real $\ell_3,\kappa$ with their defining `Tendsto` hypotheses, and $\gamma$ with its defining equation. Final assembly obtains them from `criticalProduct` and `response_transversality`, proves positivity, and supplies them to `Main.bkt`.
- **Reason:** This avoids circular structure fields and separates the analytic interfaces from the finite-generation residue proofs.
- **Classification:** Formalization choice.
- **Mathematical effect:** Intermediate declarations are conditional by design; the exported frozen statements are assembled without extra assumptions. The `limsup`/`liminf` bounds are phrased eventually, and several rate claims use `Θ`/`O` rather than introducing real conditionally complete liminf/limsup values.
- **Paper argument checked:** Yes; the parameter interfaces are discharged by the frozen results, not left as hypotheses of `bkt`.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D4 — Repaired domains of the Mellin and transform estimates

- **Paper:** The display at `scaling.tex:184–188` is written for unbounded $s$; the kernel comparison does not explicitly require a measurable kernel or $n\ge1$.
- **Formalization:** `transform_floor` and `transform_difference` use compact weight ranges with $q_N(s)\ge0$ for large $N$; `kernel_comparison` requires measurability, boundedness on $[b_1^2,\infty)$, differentiability near $1$, and $n\ge1`.
- **Reason:** The unbounded-$s$ display is false in general, while $q_N(s)\ge0$ suffices for the floor argument. Without measurability and $n\ge1$, the kernel expectation or its control need not exist.
- **Classification:** Error in the paper for the unbounded display (R3); imprecision for the kernel hypotheses (R4).
- **Mathematical effect:** Corrected local domains. Every application in the paper uses a compact weight range, so no downstream statement changes.
- **Paper argument checked:** Yes on the domain actually used; the false unbounded strengthening is not claimed.
- **Manuscript action:** Recommendations R3–R4 recorded.
- **Unresolved obstruction, if any:** None.

### D5 — Matrix growth with measurable coefficients and a coefficient-dependent constant

- **Paper:** `lem:entire-bounds` names a constant $C_{\varepsilon,T}$ while using approximation of $w$, and does not explicitly assume measurability.
- **Formalization:** The two matrix declarations assume measurable $w$ with pointwise bounds on $(0,T)$. Existence and uniqueness use Picard iteration and the factorial estimate; growth uses a positive interval-polynomial $L^1$ approximation and a per-column energy estimate. The constant may depend on $w$.
- **Reason:** Measurability is needed for the integral equation, and a constant uniform over all bounded $w$ is false under the reading identified by the audit's alternating-coefficient counterexample.
- **Classification:** Error in the paper under the uniform-constant reading; imprecision about measurability (R5).
- **Mathematical effect:** Corrected dependence $C_{\varepsilon,T,w}$ and an explicit existence/uniqueness companion theorem; no change to the application with one fixed coefficient.
- **Paper argument checked:** Yes after the repair, including arbitrary endpoint values of $w$ and genuine integrability on the full interval.
- **Manuscript action:** Recommendation R5 recorded.
- **Unresolved obstruction, if any:** None.

### D6 — Half-plane Phragmén–Lindelöf through Mathlib

- **Paper:** E2 is proved by a half-disc harmonic-measure argument.
- **Formalization:** For the right half-plane, the proof multiplies $f$ by $e^{-\delta z}$, applies `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real`, and lets $\delta\downarrow0$; the left half-plane follows by reflection.
- **Reason:** Reuse of a library theorem gives a shorter proof of the same minimal-exponential-type principle.
- **Classification:** Formalization choice.
- **Mathematical effect:** Different proof route, same closed-half-plane bound.
- **Paper argument checked:** Partly: the source's half-disc construction is bypassed, while its E2 conclusion is proved independently with the growth and boundary hypotheses checked explicitly.
- **Manuscript action:** None; no gap in the source's E2 conclusion was inferred from this substitution.
- **Unresolved obstruction, if any:** None.

### D7 — Fixed-height differentiation envelope

- **Paper:** `response.tex:87–93,176–197,321–337` differentiates expectations in the field using pointwise derivative integrability.
- **Formalization:** `Response.field_envelope` proves bounds for the first two field derivatives of functions of $\log\sum_k p_k e^{kh}$ and justifies dominated differentiation. The contact polynomial and pair polynomial specialize it to the tilted moments, second derivative of $H_n$, and kernel term.
- **Reason:** Pointwise integrability of a derivative at one height alone does not justify differentiation under an integral. The finite contact degree gives $0\le x'\le2^n$ and $0\le x''\le4^n$ and integrable dominating functions at the base height.
- **Classification:** Imprecision.
- **Mathematical effect:** Adds a proof of the omitted interchange at every field, including $n=0$, without any new disorder-moment assumption.
- **Paper argument checked:** Yes, with the missing justification supplied by `field_envelope` and the separate integrability declarations.
- **Manuscript action:** Recommendation R2 recorded.
- **Unresolved obstruction, if any:** None.

### D8 — Harris's inequality proved from scratch

- **Paper:** The proof of `response:ballot` invokes the finite-product Harris inequality as an external standard fact.
- **Formalization:** `Proofs/BallotProof.lean` proves the one-coordinate inequality and then induction by Fubini on `Fin n → ℝ`. The ballot estimate itself retains stopped sums, the overshoot bound, and summable positive means; measurable modifications handle arbitrary representatives.
- **Reason:** No suitable finite-product Harris theorem was available at the pinned Mathlib revision.
- **Classification:** Formalization choice.
- **Mathematical effect:** The external probability inequality is now part of the checked development; `response_ballot_uniform` also exposes the constant's data dependencies.
- **Paper argument checked:** Yes, including independence and a.e.-measurability side conditions.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D9 — Spine identities through a master induction

- **Paper:** The spine argument derives the two identities through the intermediate formula $\mathcal D_n=\theta2^n\mathbb E[T_n^{\theta-1}R_0e^{S_n}]$.
- **Formalization:** A bounded-test identity $\mathbb E[R_n^\theta Q_n g(R_n)]=\Pi_nA_0\widehat{\mathbb E}[w_ng(T_n)]$ is proved by induction, followed by logarithmic cutoffs and dominated convergence for the two requested test functions.
- **Reason:** The master identity handles the size-biased product law and Gibbs contact factor uniformly and makes all integrability steps explicit.
- **Classification:** Formalization choice.
- **Mathematical effect:** Equivalent alternative derivation of the same two identities at every field.
- **Paper argument checked:** Partly: the displayed intermediate formula is bypassed, but the resulting spine laws, indices, weights, and logarithmic identities were independently checked in `seal-spine`.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D10 — Summable spine drift from critical moments

- **Paper:** `response:linear` estimates the spine increments and then applies Paley–Zygmund and the passage estimate.
- **Formalization:** The same route is used, but the positive part of the drift is $H_j/A_j$; after an eventual $A_j\ge1$ reduction, `criticalMoments` bounds its positive part by a geometric sequence. This directly supplies the summability premise of `response_ballot`.
- **Reason:** Reuses an already proved uniform estimate instead of reconstructing a separate drift bound.
- **Classification:** Formalization choice.
- **Mathematical effect:** Local simplification; the centered fourth-moment and quadratic lower-tail arguments, and hence the final linear derivative bound, are unchanged.
- **Paper argument checked:** Yes; the alternative derivation of the drift premise and all dominating integrals were checked in `seal-wave4`.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D11 — `eq:Hsmall` by floor-centred corrections

- **Paper:** The estimate $|H_n|\le C_B((A_n-1)^++\rho^n)$ is obtained within the product analysis.
- **Formalization:** `criticalProduct_Hsmall` is proved before `criticalProduct`: the defect recurrence is differentiated around the deterministic floor, floor-product divergence supplies the required contradiction with bounded moments above $\theta$, and a backward-summed derivative inequality gives the estimate.
- **Reason:** This isolates the estimate and avoids circular use of `returns_to_one` or the final product theorem.
- **Classification:** Formalization choice.
- **Mathematical effect:** Alternative proof of the same bound with a constant depending only on $B$, chosen before the disorder law.
- **Paper argument checked:** Partly: the source's product-route derivation is replaced; `seal-return` checked the alternative recurrence, geometric comparison, and absolute-value conclusion.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D12 — Critical-product divergence by a direct Nash estimate

- **Paper:** P1 is obtained through a separate product-divergence/Taylor argument before the residue bootstrap.
- **Formalization:** `ProductProof.lean` uses `criticalProduct_Hsmall` directly and obtains reciprocal summability and the quadratic product bounds through a direct Nash estimate; the cubic-residue bootstrap and subsequent rates then proceed with integrable moment recurrences.
- **Reason:** The direct estimate shortens the dependency chain and supplies divergence from reciprocal summability.
- **Classification:** Formalization choice.
- **Mathematical effect:** Different proof of P1; P2–P5 and the frozen quantifier order are preserved.
- **Paper argument checked:** Partly: the separate source divergence argument is bypassed; `seal-wave4` checked the Nash route and the remaining residue/rate steps.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D13 — Ordered pair count and tree-induction second moment

- **Paper:** `escape:pairs` uses an unordered pair-of-pairs count and its overlap estimate.
- **Formalization:** `EscapePairs.lean` represents the hard recursion on `HardTree`, counts each qualifying unordered pair twice at its most recent common ancestor, computes the ordered mean $2\mu$, and proves the second-moment bound by induction on the tree. Paley–Zygmund is applied in the form $2c\mathbb EZ\le\mathbb EZ^2+c^2\mathbb P(Z\ne0)$.
- **Reason:** Ordered pairs make the recursive expectation calculations and product integrations systematic.
- **Classification:** Formalization choice.
- **Mathematical effect:** After division by four, the ordered estimate is exactly the source's $\mathbb EZ^2\le\mu+\mu^2+2^{1-k}M_I\mu$, with the same final tail constant; the degenerate case $M_I=0$ is included.
- **Paper argument checked:** Partly: the source's pair-of-pairs enumeration is replaced; `seal-pairs` checked the law equivalence, count, overlap induction, and arithmetic.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D14 — Compactness by small-$s$ expansion and coefficient extraction

- **Paper:** `scaling:compactness` derives the ODEs and moments from the limiting transform and excludes an atom by a large-weight argument.
- **Formalization:** The Riccati recurrence is integrated on time intervals; its small-$s$ expansion and finite-difference coefficient extraction give the three ODEs and the drift/second/third-moment limits. Compensated-Laplace coefficient extraction yields moments 1–3. The no-atom step uses $s\to\infty$ with dominated convergence and a countable cover of $(0,T]$.
- **Reason:** This separates the formal limits from equalities of named coefficients and makes the $7/2$-moment domination and all local time integrals explicit.
- **Classification:** Formalization choice.
- **Mathematical effect:** Local alternative derivations inside the same subsequential compactness theorem. Weak convergence is genuine finite-measure convergence, and the extracted measures have zero mass only outside the source time domain.
- **Paper argument checked:** Partly: extraction, no-atom, and moment steps differ; `seal-compact` checked the two diagonal selections, local uniform convergence, measure construction, entrance bounds, and matching.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D15 — Window $7/2$ moment by weighted AM–GM

- **Paper:** The $7/2$ window moment is handled by a Hölder-type interpolation within the window-moment argument.
- **Formalization:** `WindowProof.lean` uses weighted AM–GM, contact-polynomial differentiation, mean-value bounds, and factorwise control of the product ratio.
- **Reason:** Weighted AM–GM fits the available integer contact and tilted moments and gives a direct integrable dominating bound throughout the window.
- **Classification:** Formalization choice.
- **Mathematical effect:** Local alternative proof of the $7/2$ estimate; all six source window bounds and derivative bounds are retained with explicit constants.
- **Paper argument checked:** Yes for the overall window strategy, with the interpolation step replaced; `seal-wave5` checked integrability, denominators, and derivative envelopes.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D16 — Profile measure identification through characteristic functions

- **Paper:** After regularization, polynomial rigidity, and the scalar Riccati identification, `th:profile-identification` concludes by uniqueness of Laplace transforms.
- **Formalization:** The same regularized equations and Riccati route prove that the candidate measure is exponential; an exponential/characteristic-function identification gives the final equality with the sine profile.
- **Reason:** This provides a direct uniqueness argument compatible with the complex analytic infrastructure already used for polynomial rigidity.
- **Classification:** Formalization choice.
- **Mathematical effect:** Alternative final identification step, with the same common initial interval and the same exact critical limits.
- **Paper argument checked:** Partly: the main rigidity argument is retained, while the final Laplace-uniqueness invocation is replaced. Positivity before division and the almost-everywhere finiteness/integrability domain were checked in `seal-wave5`.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D17 — Redundant hypotheses retained in frozen statements

- **Paper:** `lem:barrier` is stated at $h_c>h_a$ for $n\ge1$.
- **Formalization:** `Critical.barrier` preserves those hypotheses, but its proof uses neither `hshift` nor `hn`; the contraction argument and critical-point characterization suffice more generally. The statement was not strengthened after this was observed.
- **Reason:** Frozen source-facing interfaces were preserved rather than optimized during integration.
- **Classification:** Formalization choice.
- **Mathematical effect:** Two harmless redundant assumptions remain. Similar unused internal parameters noted by seals do not alter any conclusion; they are not treated as coverage defects.
- **Paper argument checked:** Yes; non-use of a hypothesis cannot supply a missing conclusion, and the remaining argument was independently audited.
- **Manuscript action:** None required.
- **Unresolved obstruction, if any:** None.

### D18 — Further local repairs in compactness, profile, and continuation

- **Paper:** The audit identified compressed or imprecise steps: the vector used in the left-half-plane estimate has an apparent pole at $s=0$; polynomial growth needs a split logarithmic time integral; degree reduction needs absolutely continuous coefficients and $k+2$ weights; the base-weight bound is worded circularly; first-mesh-cell entrance bounds need a different order of limits; time kernels and uniqueness measurability need justification; and an interior uniform upgrade does not itself reach the right endpoint of $I$.
- **Formalization:** The proofs respectively restrict the vector estimate away from $s=0$, split the time integral, use a.e. absolutely continuous flux equations and $k+2$ weights, close the base bound by a first-exit argument, work away from the first cell before taking limits, construct measurable kernels and use deterministic factorial envelopes for uniqueness with moving tests, and extend the continuation chain slightly beyond $\max I$.
- **Reason:** These are the precise side conditions and order-of-limit choices required by the existing arguments.
- **Classification:** Imprecisions (R6–R12); no new hypothesis on the final theorem.
- **Mathematical effect:** Local proof repairs with unchanged numbered conclusions.
- **Paper argument checked:** Yes with these repairs, as covered by the compactness, profile, continuation, and transform seals; the formalization does not claim the imprecise literal shortcuts.
- **Manuscript action:** Recommendations R6–R12 recorded; R13–R17 contain exposition/notation remarks not reproduced as mathematical differences here.
- **Unresolved obstruction, if any:** None.

## Corrections to the paper

Two localized correctness issues were confirmed within the reviewed scope at
this revision: the unbounded-weight display R3 (`scaling.tex:184–188`, D4) and
the uniform-over-$w$ reading of the matrix-growth constant R5
(`profile.tex:26–39`, D5). In both cases the intended, repaired reading is
proved and is sufficient for every application; neither affects Theorem
`th:bkt` or another numbered conclusion. They remain in
`MANUSCRIPT_RECOMMENDATIONS.md` because the manuscript is not distributed. The
source snapshot was not edited.

No other numbered result was found to be false within the reviewed scope. No
error in a cited work was confirmed within that scope, so there is no cited-work
erratum entry to report. Expository ambiguities and missing proof justifications
are distinguished from mathematical proof alternatives in D1–D18.

## Verification and assumptions

- **Checked revision:** `fbb89a8`; Lean `v4.35.0`, Mathlib `v4.35.0` at
  `56a005855ea17e0b0958f73ec801ae140b0a1679`, with the dependency revisions in
  `lake-manifest.json`.
- **Build:** **passed**, 19 November 2026, at campaign completion:
  `lake build DiamondPinning Solution` (9,124 jobs), recorded in
  `CAMPAIGN_PLAN.md` ("Resume here"). Each cleanup worker also reported a
  whole-library build. The cleanup merge at `fbb89a8` is recorded with its
  final combined build/freeze/axiom cycle **running** in the cleanup task row;
  no build was run for this documentation task.
- **Axioms:** **passed** at campaign completion for every one of the 72 closed
  frozen statements, including `DiamondPinning.bkt`: only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx`, `native_decide`, or
  `bv_decide` dependency. Evidence: `CAMPAIGN_PLAN.md` completion and task
  rows. The final post-cleanup repetition is included in the running cycle
  above.
- **Semantic dependencies:** `Model.Defs.lawR` constructs the finite-volume
  laws; `freeEnergy_tendsto` and `criticalPoint_isGreatest` characterize the
  totalized `limUnder`/`sSup` definitions. Positivity and integrability lemmas
  support every use of `Real.log`, real powers, Bochner integrals, and
  derivatives. `Model.Scaling.EntranceData` contains the source's limit ODE,
  measure, entrance, Taylor, and matching claims, rather than hypotheses that
  merely assume the desired profile. `Model.Scaling.WeakConvergence` includes
  finiteness and convergence for bounded continuous integrals.
  `Model.InstancePins` preserves the `NormedSpace ℝ ℝ` instance used by the
  frozen statements and Challenge.
- **Statement preservation:** **passed** at campaign completion for all six
  freeze records with `freeze_check.py check` and axiom checks. Statement
  batches were independently reviewed and approved by the author through the
  recorded Astra delegation. The records are local; Comparator is the public
  comparison mechanism.

| Freeze | Record path | SHA-256 | Frozen scope and record commit |
| --- | --- | --- | --- |
| 1 | `../BKT-campaign-records/freeze/record-2026-11-18.json` | `6a960f195afbca42d741fa6fd922957bc354658ae2bfe32414c9802e34e72eda` | Batch 1: `Model/Defs.lean`, `Main.lean` (6 registered holes), `Challenge.lean`, `Solution.lean`, `comparator.json`; `f0aa30c`. |
| 2 | `../BKT-campaign-records/freeze/record-2026-11-18b.json` | `d2ce898981f3e1a20c048542911374a1bf6b5bd01f4965e707df9b1c24110370` | Environment: `Model/Env.lean`; `Statements/Env.lean` (3 holes); `cdf9076`. |
| 3 | `../BKT-campaign-records/freeze/record-2026-11-19.json` | `7a78f5a706ca820504607efb196add6237c3d91877336f0065cb2941b25bf4ce` | Sections 2–3 and standalone lemmas: `Model/Moments.lean`, `Basic.lean`; `Critical.lean` (9), `Ballot.lean` (2), `OneSided.lean` (1), `EntireBounds.lean` (4); `b125e6c`. |
| 4 | `../BKT-campaign-records/freeze/record-2026-11-19b.json` | `2cea9844309a36786234e596d5800451ca720779cf17589fe83ca972fd90c037` | Sections 4 and 8: `Model/Contacts.lean`, `Spine.lean`, `Window.lean`, `Hard.lean`; `Response.lean` (21), `Escape.lean` (8); `8c3d9fa`. |
| 5 | `../BKT-campaign-records/freeze/record-2026-11-19c.json` | `31d4f8dd1f4f453185f431f95e713d65fb7d5cbba754c2dbcb5c16beb76daa39` | Sections 5–7: `Model/Profile.lean`, `Scaling.lean`; `Scaling.lean` (10), `Profile.lean` (3); `f30bef9`. |
| 6 | `../BKT-campaign-records/freeze/record-2026-11-19d.json` | `f44c64dcc0c96ca4a3036bd47d955232b3a0fcaf1393262dd557600d558076d8` | Remaining public basic bounds: `Model/LogMean.lean`; `FreeEnergyBounds.lean` (5); `92262d2`. |

- **Source-fidelity review:** **passed** for the frozen statement batches, with
  independent reviews/read-backs and the approvals recorded under
  `CAMPAIGN_PLAN.md` ("Approvals"). The completed proofs then received
  independent seal re-audits; no mathematical soundness or statement-fidelity
  finding remained open. Principal retained reports are
  `.orchestration/seal-wave1/attempt-1/result.md` through
  `seal-wave6/attempt-1/result.md`, and
  `seal-critmom`, `seal-return`, `seal-spine`, `seal-pairs`, `seal-compact`,
  `seal-ode`, `seal-n25`, and `seal-tdiff` at the same path pattern.
  `CAMPAIGN_PLAN.md` additionally records the PASS verdict of `seal-basic`.
  These audits checked proof routes against the TeX; they did not replace the
  coordinator's builds, freeze checks, or axiom queries.
- **Comparator:** **passed**, 19 November 2026 at `43e3595`, on the Open Math
  OS VM. The official sandboxed `lake comparator` exited 0 and reported that
  both the NanoDa and Lean default kernels accepted the solution ("Your
  solution is okay!"). Versions recorded: Lean 4.35.0, Lake 5.0.0, NanoDa
  0.4.19, `bwrap` 0.11.1. The run used a byte-identical copy of `nanoda_bin`
  in the VM work directory to address the sandbox symlink-bind issue.
  Evidence: `CAMPAIGN_PLAN.md` row `vm-comparator` and
  `.orchestration/vm-comparator3/run1/fetched/sandbox-analysis.md`. Comparator
  was not rerun at `fbb89a8` after the non-frozen cleanup.
- **Comparator `--paranoid`:** **unfinished**. Lean4Lean accepted 60,601
  declarations and NanoDa accepted; con-leche was still running when the VM
  task reached its input-token cap. This optional unfinished run does not
  change the ordinary Comparator PASS above.
- **Kernel replay and full deposit verification:** **not run**. Palomar's full
  preflight still requires the fresh public GitHub repository and its exact
  commit. Making that repository public, choosing its license, and submitting
  to Palomar remain separate author decisions.

Building and kernel checking show that the Lean statements are proved from the
listed axioms; they do not show that the statements say what the paper says,
and a Challenge and a Solution can share a misreading of the paper.

## How the formalization was produced

The coordinator built the source inventory and dependency graph, designed and
reviewed the shared model interfaces, and recorded the author's decisions.
Independent statement reviews and blind read-backs preceded six statement
freezes; the author delegated the approval consultations to Astra, whose
recommendations and the two batches' corrections are recorded in
`CAMPAIGN_PLAN.md`. Early research identified the extended-$F_d$ convention,
the differentiation envelope, the Mellin-domain repairs, and the measurable
coefficient/constant issue in `lem:entire-bounds`.

Proof obligations were dispatched to isolated Claude (Sonnet/Opus, principally
`high`/`xhigh`), Kimi (`high`), Sol (`medium`), and Luna (`xhigh`) workers with
owned helper modules and verbatim frozen statement templates. The coordinator
integrated only proof-text `exact` fills, then ran the freeze and axiom checks. Independent seal readers compared the resulting
routes with the TeX and audited totalization, integrability, positivity, and
quantifier-order issues. Alternative routes are recorded above rather than
being treated as verification of bypassed manuscript arguments. Four Kimi
cleanup workers subsequently removed duplication and improved public
documentation without changing frozen declarations. The Open Math OS VM was
used for the Linux sandboxed Comparator. Publication, licensing, and Palomar
submission were not delegated.

A different Lean proof can verify the result without verifying the written
argument it bypasses. In particular, an alternative proof does not silently
repair a gap in the manuscript; the affected entries D4, D5, D7, and D18 point
to the recorded manuscript recommendations.

## Unresolved coverage or correspondence obligations

### Mathematical coverage

All 24 numbered theorems, propositions, and lemmas in the inventory are matched
to proved frozen declarations and have no outstanding proof obligation. The
introduction's Gaussian example is excluded by the author's scope decision.

Three routine Section 1 identities remain only partially matched under this
report's strict declaration-level criterion:

1. **S1.4, `eq:log-model`:** add a declaration for the law of
   $\log R_n/\log B$ and its transformed recursion, using `lawR` or the
   environment bridge. Related logarithmic encodings exist, but no theorem
   stating this identity was found.
2. **S1.5:** add standalone algebraic declarations for
   $R_n^\theta=2^{X_n}$ and the $X_n$-forms of $H_n$ and $J_n$. The moments
   and their integrability are proved in the $\log R_n-a$ normalization, but
   the three displayed identities are not separately exported.
3. **S1.6:** export the two elementary pole-scale identities currently used
   only within the scale/energy assembly. `escape_constant` and `bkt` prove
   the resulting asymptotics, not these standalone equalities.

These are API/coverage gaps for three routine inventory items, not missing
dependencies of `DiamondPinning.bkt`. They can be closed in a new non-frozen
helper module without changing any frozen statement.

### Release and verification obligations

1. **Frozen statement docstrings:** stale "proofs are holes pending approval"
   text remains in frozen statement modules, and internal process labels such
   as "decision 4", "node N25", "audit F2/F3–F4", "blueprint E5", and
   "Statement N14" remain in parts of `Response.lean`, `Scaling.lean`, and
   `OneSided.lean`; `Scaling.lean` also has a "Proof of" label on a statement.
   Editing these files requires a new freeze record and the author's approval.
2. **Post-cleanup check cycle:** the cleanup task row at `fbb89a8` records the
   final combined build, six-record freeze check, and 72-declaration axiom
   check as running. Its completion should be recorded before release; this
   documentation task did not run it.
3. **Optional Comparator audit:** finish `--paranoid` if desired; con-leche is
   the unfinished component. The ordinary sandboxed Comparator has passed.
4. **Palomar release:** create the fresh publication repository with clean
   history, rerun the publication scan and full Palomar preflight at its public
   commit, and obtain the author's separate decisions on public release,
   license, and submission. These steps are not mathematical coverage
   obligations and have not been performed.
