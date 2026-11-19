# Formalization report

## Purpose and scope

This report records coverage of the mathematical results in the accompanying
paper and substantive differences between the written and formal arguments. It
is a completion record for a paper-companion formalization, not a log of every
Lean edit.

- **Paper and version:** *BKT asymptotics for the quenched free energy of
  hierarchical pinning* by Igor Kortchemski, version of 19 November 2026
  (SHA-256 of its TeX file
  `6d66491d1e04453306f33eccc523802059cdb314923593469f1b99ac96feafa4`). The
  formalization was developed against the research draft of 18 November 2026
  (SHA-256 of its main TeX file
  `8db09790c116d6f75147c911aa40fb1bfc5defa1668dc762c4ec8aef68bff68c`), then
  titled *BKT asymptotics for disordered pinning on the diamond hierarchical
  lattice*; the differences between the two versions are listed under
  [From the formalized draft to the final version](#from-the-formalized-draft-to-the-final-version).
  The paper has eight sections; results are cited below by section and by
  the paper's labels (such as `th:bkt`).
- **Publication status of the paper:** not yet distributed (19 November 2026).
- **Declared formalization scope:** the whole paper (Sections 1 to 8), with
  Theorem `th:bkt` and its dependencies first; the introduction's Gaussian
  example, resting on a cited strict-shift theorem, is out of scope (decision
  of the paper's author, 18 November 2026).
- **Lean/Mathlib versions:** Lean `v4.35.0`, Mathlib `v4.35.0`
  (`56a005855ea17e0b0958f73ec801ae140b0a1679`).

Within the declared scope, the aim is to cover every theorem, proposition,
lemma, corollary, and other substantive mathematical claim. Conjectures,
questions, and purely expository remarks are identified rather than presented
as proved results.

A paper result is covered only by a proved Lean declaration with the same
mathematical content, or by a checked specialization of a proved, more general
declaration. A conditional helper, nearby theorem, or matching name is not by
itself coverage.

## Result correspondence

In the declaration column, `Main.bkt` abbreviates the declaration
`DiamondPinning.bkt` in `DiamondPinning/Statements/Main.lean`, and similarly
for the other modules of `DiamondPinning/Statements/`. Declarations outside
`Statements/` are written with their module name. Route judgments follow the
independent re-audits listed in the verification section, not merely the
names of the declarations.

All 24 numbered results have matching proved declarations, whose statements
were fixed before their proofs were written. The three routine identities
S1.4–S1.6 have related definitions and uses in proved arguments, but no
standalone declaration with the same content; under the coverage rule above
they are marked `Partial`, not counted as proved by a nearby definition.

| ID | Paper result | Paper location | Lean declaration | Coverage | Proof correspondence | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| S1.1 | $\theta\in(0,1)$ | Section 1 | `Model.Basic.theta_pos`, `Model.Basic.theta_lt_one` | Complete | Same main strategy | Direct consequence of $B>2$ and `Model.Defs.theta`. |
| S1.2 | Annealed mean recursion and $h_a=\log(B-1)$ | Section 1 | `Model.Basic.integral_lawR_zero`, `Model.Basic.integral_lawR_succ`; `Model.FreeEnergy.freeEnergy_logc_eq_zero_aux`; `FreeEnergyBounds.logShift_le_criticalPoint` | Complete | Same main strategy | The mean recursion is explicit; vanishing at the annealed shift and $h_a\le h_c$ are proved separately. |
| `th:bkt` | T1–T5: positive residues, product equivalent, both forms of $\gamma$, and the BKT limit | Section 1; proof completed in Section 8 | `Main.bkt` | Complete | Same main strategy | Assembles `Critical.criticalProduct`, `Response.response_transversality`, `Profile.exact_critical`, `Profile.gamma_eq_limit`, `Escape.freeEnergy_upper`, and `Escape.escape_constant`. It also proves differentiability of every $H_n$ at $h_c$ and $F(h_c+u)>0$ for $u>0$. |
| S1.3 | $K=\pi\log2/\sqrt\gamma$ and all fixed tilted logarithmic moments, including $n=0$ | Section 1 | `Main.bkt`, `Main.integrable_tiltedLogPower` | Complete | Same main strategy | No extra logarithmic-moment hypothesis is imposed. |
| Gaussian example | Strict shift for lognormal disorder when $B>2+\sqrt2$ | Section 1 (introduction) | None, by scope decision | Out of scope | Not applicable | Relies on the cited strict-shift theorem of [GLT10]. |
| S1.4 | Recursion `eq:log-model` for $X_n=\log R_n/a$ | Section 1 | Related encoding: `Model.Defs.lawR`, `Model.Env.evalR`, `Env.map_evalR_envMeasure`, `Model.Scaling.rescaledMeasure` | Partial | Local adaptation | The formalization works directly in logarithmic coordinates and does not introduce the alias $X_n$. No proved declaration stating the transformed law recursion itself exists. |
| S1.5 | $R_n^\theta=2^{X_n}$ and the formulas for $H_n$ and $J_n$ | Section 1 | Related encoding: `Model.Defs.theta`, `Model.Defs.tiltedLogMoment`; `Main.integrable_tiltedLogPower` | Partial | Local adaptation | Moments are defined directly using $\log R_n-a$. No standalone declaration contains the three displayed identities in the $X_n$ normalization. |
| S1.6 | $NT_v=\pi/\sqrt{\gamma u}$ and $2^{-NT_v}=\exp(-\pi\log2/\sqrt{\gamma u})$ | Section 1 | Related scale assembly: `Escape.escape_constant`, `Main.bkt`; `Model.Profile.IsPrePoleTime` | Partial | Local adaptation | The scale substitution $N=u^{-1/2}$ is proved inside the final assembly, but no standalone declaration of these two algebraic identities exists. |
| `lem:basic-bounds` | B1–B5: floor, moments, free energy, increments, and critical point | Section 2 | `Main.integrable_lawR`, `Main.integrable_tiltedLogPower`, `Main.integrable_log_lawR`, `Main.freeEnergy_tendsto`, `Main.criticalPoint_isGreatest`; `FreeEnergyBounds.floor_bounds`, `finiteSize_bounds`, `freeEnergy_nonneg`, `freeEnergy_increment`, `logShift_le_criticalPoint` | Complete | Same main strategy | Includes $n=0$ for the tilted moments and $n\ge1$ for integrability of $\log R_n$ and `eq:finitesize`. `criticalPoint_isGreatest` makes the `sSup` definition genuine. |
| `lem:mellin-correction` | Holomorphy and compact-uniform bounds for $C_n$, with `eq:C` | Section 2 | `Critical.correction_eq`, `Critical.differentiableOn_correction`, `Critical.correction_bounded` | Complete | Same main strategy | Stated for $n\ge1$ and $\Re z<1$. |
| `prop:criticalmoments` | Critical tilted-mass and first-moment bounds; uniform absolute first moment | Section 2 | `Critical.criticalMoments`, `Critical.jensen_step` | Complete | Same main strategy | Favorable-block estimate, endpoint limit $q\uparrow\theta$, and logarithmic recurrence. The constant is chosen after $B$ and before the disorder law. |
| `lem:barrier` | Lower bound for $G_n(q)$, $\theta<q<1$ | Section 2 | `Critical.barrier` | Complete | Same main strategy | The hypotheses `hshift` and `hn` are unused by the proof; see D17. |
| `th:return` | $\liminf G_n(\theta)=1$ | Section 2 | `Critical.returns_to_one` | Complete | Same main strategy | Expressed by an infinitely-often upper return and an eventual lower bound for every $\varepsilon>0$. Uses a uniform polynomial Picard form of the analytic-continuation argument. |
| `th:product` | P1–P5: product estimates, `eq:Hsmall`, $\ell_3$, fourth moment, and critical rates | Section 3 | `Critical.criticalProduct`, `Critical.criticalProduct_Hsmall` | Complete | Alternative proof in two steps | P1 uses a direct Nash estimate rather than the paper's separate divergence argument; P2 uses floor-centred corrections. The rates are stated with `=Θ[atTop]` and `=O[atTop]`, including eventual $A_n>1$. `Profile.exact_critical` later sharpens them to exact limits. |
| `response:ballot` | Passage estimate for independent integrable increments | Section 4 | `Ballot.response_ballot`, `Ballot.response_ballot_uniform` | Complete | Local adaptation | Follows the stopping-time argument. Harris's inequality is proved from scratch. The second declaration makes the dependence of the constant on the data explicit; no nonmeasurable-representative trick is used. |
| `response:spine-identities` | `response:spine` and `response:mixed-spine` | Section 4 | `Response.spine_identities`; supporting `Response.hasDerivAt_tiltedMass`, `Response.hasDerivAt_tiltedLogMoment`, `Response.integrable_spine` | Complete | Alternative proof | Proved from a bounded-test master identity by induction, logarithmic cutoffs, and dominated convergence; valid at every field and every $n$. |
| `response:linear` | $\mathcal D_n\le C(n+1)$ | Section 4 | `Response.response_linear` | Complete | Local adaptation | Retains the ballot/Paley–Zygmund route. Summability of the positive drift is obtained directly from `Critical.criticalMoments`; see D10. |
| `th:response` | $\mathcal E_n/\Pi_n\to\kappa\in(0,\infty)$ and $\mathcal E_n\asymp n^2$ | Section 4 | `Response.response_transversality`; derivative support in `Response.hasDerivAt_tiltedLogMoment`, `Response.differentiableAt_deriv_tiltedLogMoment_one`, `Response.differentiableAt_kernelMean` | Complete | Local adaptation | Uses a harmonic barrier dominating the logarithmic barrier and combines the two derivative recurrences to cancel leakage. The rate is `=Θ[atTop]`; the residue is then supplied to `Main.bkt`. |
| `prop:contact-moments` | Change-of-field identities, factorial moment bounds, exponential and tilted-mass increments | Section 4 | `Response.gibbsWeight_zero`, `gibbsWeight_succ`, `gibbsWeight_isProb`, `evalR_add_eq_gibbsMean`, `hasDerivAt_log_evalR`, `contactMoments`; integrability in `Response.integrable_contactMoment`, `integrable_contactExpMoment` | Complete | Same main strategy | Uses the contact polynomial and factorial recursion. The exponential series is integrated term by term with dominated convergence; the field-increment bound follows separately. |
| `prop:window-moments` | `response:windowA`, `windowH`, `windowK`, `windowJ`, `windowSevenHalves`, and the product ratio | Section 4 | `Response.windowMoments`, `Response.window_derivBounds`; general support in `Response.field_envelope` | Complete | Local adaptation | All error terms are explicit absolute-value bounds with one constant in the window $0\le u(n+1)^2\le\eta$. Weighted AM–GM replaces Hölder for the $7/2$ moment; the product ratio is controlled factor by factor. |
| `cont:continuation` | Uniform transform convergence and weighted weak convergence before the pole | Section 5 (statement); Section 7 (proof) | `Scaling.continuation` | Complete | Same main strategy | Uses compact $I\subset(0,T_v)$, $s>0$, and $s+\inf_I b_v>0$. Local identification, projected transport, uniqueness, base-weight recovery, and extension beyond endpoints follow the paper's route. |
| `scaling:compactness` | Subsequential convergence, ODEs, Riccati equation, measure representation, moments, no atom, entrance data | Section 5 | `Scaling.scaling_compactness`, `Scaling.rescaledMeasure_finite` | Complete | Local adaptation | `Model.Scaling.EntranceData` packages BV/Lipschitz, integral ODE, measure, Taylor, and matching claims. Small-$s$ expansion yields the ODEs; moments come from coefficient extraction. The paper's sufficiently small $\lambda T^2$ is $\lambda T^2\le\eta_0$. |
| `scaling:mellin-calculus` | Defect and kernel estimates, recurrence, floor, one-sided/BV bounds, defect sum, transform difference | Section 5 | `Critical.jensen_step` for the preliminary recursion; `Scaling.defectMean_lower`, `kernel_comparison`, `defectMean_sub`, `transform_recurrence`, `transform_floor`, `transform_bounded`, `transform_difference` | Complete | Local adaptation | Uses the repaired domains of D4. `defectMean_sub` uses a mean-value estimate and `kernel_comparison`; `transform_bounded` includes an $\varepsilon_N\to0$ one-sided estimate and an `ENNReal` variation bound. |
| `lem:one-sided` | Upgrade from $L^1$ convergence and one-sided increments to locally uniform convergence | Section 5 | `OneSided.one_sided_compactness` | Complete | Same main strategy | Excursion argument. A.e. strong measurability is explicit; the conclusion is uniform on compact subsets of the open interval. |
| `th:profile-identification` | Identification with $f_v$ on a common initial interval, exact critical limits, second expression of $\gamma$ | Section 6 | `Profile.profile_identification`, `Profile.exact_critical`, `Profile.gamma_eq_limit` | Complete | Local adaptation | Main regularization, polynomial rigidity, and Riccati route retained. Exponential/characteristic-function identification replaces the final Laplace-uniqueness step. `exact_critical` includes $\Pi_n/n^2\to3a^3/(2\ell_3)$. |
| `lem:entire-bounds` | E1 matrix growth and E2 half-plane minimal-type principle | Section 6 | `EntireBounds.matrix_integral_solution_exists_unique`, `matrix_integral_growth_bound`, `rightHalfPlane_bounded_of_minimal_exponential_type`, `leftHalfPlane_bounded_of_minimal_exponential_type` | Complete | Local adaptation | E1 uses Picard iteration, positive polynomial approximation, and an energy estimate with a $w$-dependent constant. E2 uses Mathlib's half-plane theorem after multiplication by $e^{-\delta z}$. |
| Hard recursion and $F_d$ (definition and supporting properties) | Limit and monotonicity of $2^{-j}\mathbb EY_j$, finite-hard lower bound, real specialization | Section 8 | `Escape.hardFreeEnergy_tendsto`, `Escape.hardFreeEnergy_ge`, `Escape.hardFreeEnergy_real` | Complete | Local adaptation | `F_d` is an infimum in $[0,\infty]$; subtraction is truncated there. A real-valued version is proved when $\mathbb EY_0<\infty$. This row records definitions/supporting claims, not an additional numbered result. |
| `cont:freeenergyupper` | Upper free-energy asymptotic | Section 8 | `Escape.freeEnergy_upper` | Complete | Same main strategy | Stated in eventual form: for every $\varepsilon>0$, the upper inequality holds eventually as $u\downarrow0$. |
| `escape:pairs` | Pair-tail lower bound | Section 8 | `Escape.escape_pairs` | Complete | Alternative proof | Uses an ordered pair count and a second-moment induction on a recursively represented tree. Division by four recovers exactly the paper's unordered-pair estimate and constant. |
| `escape:band-exit` | Band condition implies amplification, exit by $2L$, and hard-energy lower bound | Section 8 | `Escape.escape_bandExit`, with `Escape.hardFreeEnergy_ge` for `escape:finite-hard` | Complete | Same main strategy | Explicit thresholds $D_*=L_*=10^4$, halving recursion, and stopping at $w\ge128$. Hard means and $F_d$ remain in $[0,\infty]$. |
| `escape:comparison` | Energy transfer and diamond-exit lower bound | Section 8 | `Escape.escape_comparison`; finite-mean support in `Escape.hardFreeEnergy_real` | Complete | Same main strategy | Exact floor coupling and stochastic-order induction. The first conjunct proves finite initial hard mean, justifying conversion of $F_d$ to a real number. |
| `escape:constant` | Fixed-$\lambda$ lower free-energy asymptotic | Section 8 | `Escape.escape_constant` | Complete | Same main strategy | Eventual lower bound with margin $\varepsilon$ and explicit positivity of $F(h_c+\lambda/N^2)$. Real $N\to\infty$; $T_v=\pi/\sqrt{\gamma\lambda}$. |

## Substantive differences

The entries below distinguish changes to the mathematical route from encoding
choices and repairs of the paper. Routine implementation details and the
renaming of helper lemmas are not included.

### D1 — Extended-valued hard free energy

- **Paper:** Section 8 reads $F_d=\lim_j2^{-j}\mathbb EY_j$ as a real number for an arbitrary law on $\mathbb N$.
- **Formalization:** `Model.Hard.hardFreeEnergy` is $\inf_j2^{-j}\mathbb EY_j$ in `ℝ≥0∞`, with lower-integral means; `Escape.hardFreeEnergy_tendsto` identifies the paper's limit, and `hardFreeEnergy_real` gives a real specialization when the initial mean is finite.
- **Reason:** An admissible infinite-mean initial law can satisfy the band hypothesis while every hard mean is infinite. A real Bochner reading would silently turn those means into zero.
- **Classification:** Imprecision.
- **Mathematical effect:** The hard statements are valid for every initial law, with truncated subtraction in `hardFreeEnergy_ge`; the floor law used by `escape:comparison` is proved integrable, so the model-facing comparison remains real.
- **Paper argument checked:** Yes, after adopting the extended-valued convention; no numbered conclusion changes.
- **Manuscript action:** A clarification is recommended for the manuscript.
- **Unresolved obstruction, if any:** None.

### D2 — Constructed law-level free energy and critical point

- **Paper:** $F$ is the limit of normalized logarithmic expectations and $h_c$ is the supremum of its zero set.
- **Formalization:** `Model.Defs.lawR` constructs the law recursively; `freeEnergy` uses `limUnder`, and `criticalPoint` uses `sSup`. The environment coupling is separate, with `Env.map_evalR_envMeasure` connecting it to `lawR`.
- **Reason:** Lean's total operations need characterizations before they can be used as the paper's limit and supremum.
- **Classification:** Formalization choice.
- **Mathematical effect:** None after `Main.freeEnergy_tendsto` and `Main.criticalPoint_isGreatest`: the zero set is nonempty, bounded above, and contains its greatest element. The statements construct $F$ and $h_c$ rather than postulating them.
- **Paper argument checked:** Yes; the companion theorems exclude an unspecified `limUnder` value and an empty/unbounded `sSup` artifact.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D3 — Residues as parameters in internal interfaces

- **Paper:** $\ell_3$ and $\kappa$ are limits established in Sections 3–4 and then used in Sections 5–8.
- **Formalization:** Scaling, profile, continuation, and energy statements take real $\ell_3,\kappa$ with their defining `Tendsto` hypotheses, and $\gamma$ with its defining equation. The final assembly obtains them from `criticalProduct` and `response_transversality`, proves positivity, and supplies them to `Main.bkt`.
- **Reason:** This avoids circular structure fields and separates the analytic interfaces from the finite-generation residue proofs.
- **Classification:** Formalization choice.
- **Mathematical effect:** Intermediate declarations are conditional by design; the main theorem is assembled without extra assumptions. The `limsup`/`liminf` bounds are phrased eventually, and several rate claims use `Θ`/`O` rather than introducing real conditionally complete liminf/limsup values.
- **Paper argument checked:** Yes; the parameter interfaces are discharged by proved results, not left as hypotheses of `bkt`.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D4 — Repaired domains of the Mellin and transform estimates

- **Paper:** One display of the Mellin calculus of Section 5 (`scaling:mellin-calculus`) is written for unbounded $s$; the kernel comparison does not explicitly require a measurable kernel or $n\ge1$.
- **Formalization:** `transform_floor` and `transform_difference` use compact weight ranges with $q_N(s)\ge0$ for large $N$; `kernel_comparison` requires measurability, boundedness on $[b_1^2,\infty)$, differentiability near $1$, and $n\ge1$.
- **Reason:** The unbounded-$s$ display is false in general, while $q_N(s)\ge0$ suffices for the floor argument. Without measurability and $n\ge1$, the kernel expectation or its control need not exist.
- **Classification:** Error in the paper for the unbounded display; imprecision for the kernel hypotheses.
- **Mathematical effect:** Corrected local domains. Every application in the paper uses a compact weight range, so no downstream statement changes.
- **Paper argument checked:** Yes on the domain actually used; the false unbounded strengthening is not claimed.
- **Manuscript action:** Incorporated in the final version of 19 November 2026: the weights are restricted to $0\le s\le N\log2$ (equivalently $q_N(s)\ge0$) in `scaling:measure` and `scaling:unshifted`, the transform-difference estimate is stated for $s$ in a compact set, and the kernel comparison assumes $n\ge1$ and a Borel measurable $F$ differentiable in a neighbourhood of $1$, as in Lean.
- **Unresolved obstruction, if any:** None.

### D5 — Matrix growth with measurable coefficients and a coefficient-dependent constant

- **Paper:** `lem:entire-bounds` names a constant $C_{\varepsilon,T}$ while using approximation of $w$, and does not explicitly assume measurability.
- **Formalization:** The two matrix declarations assume measurable $w$ with pointwise bounds on $(0,T)$. Existence and uniqueness use Picard iteration and the factorial estimate; growth uses a positive interval-polynomial $L^1$ approximation and a per-column energy estimate. The constant may depend on $w$.
- **Reason:** Measurability is needed for the integral equation, and a constant uniform over all bounded $w$ is false under that reading, as an alternating-coefficient counterexample shows.
- **Classification:** Error in the paper under the uniform-constant reading; imprecision about measurability.
- **Mathematical effect:** Corrected dependence $C_{\varepsilon,T,w}$ and an explicit existence/uniqueness companion theorem; no change to the application with one fixed coefficient.
- **Paper argument checked:** Yes after the repair, including arbitrary endpoint values of $w$ and genuine integrability on the full interval.
- **Manuscript action:** Incorporated in the final version of 19 November 2026: `lem:entire-bounds` fixes a measurable $w$ with $w$ and $1/w$ bounded, normalizes $M(0,z)=I$, and names the constant $C_{\varepsilon,T,w}$, as in Lean.
- **Unresolved obstruction, if any:** None.

### D6 — Half-plane Phragmén–Lindelöf through Mathlib

- **Paper:** E2 is proved by a half-disc harmonic-measure argument.
- **Formalization:** For the right half-plane, the proof multiplies $f$ by $e^{-\delta z}$, applies `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real`, and lets $\delta\downarrow0$; the left half-plane follows by reflection.
- **Reason:** Reuse of a library theorem gives a shorter proof of the same minimal-exponential-type principle.
- **Classification:** Formalization choice.
- **Mathematical effect:** Different proof route, same closed-half-plane bound.
- **Paper argument checked:** Partly: the paper's half-disc construction is bypassed, while its E2 conclusion is proved independently with the growth and boundary hypotheses checked explicitly.
- **Manuscript action:** None; no gap in the paper's E2 conclusion was inferred from this substitution.
- **Unresolved obstruction, if any:** None.

### D7 — Fixed-height differentiation envelope

- **Paper:** Section 4 (the spine identities, the proof of `th:response`, and the window moments) differentiates expectations in the field using pointwise derivative integrability.
- **Formalization:** `Response.field_envelope` proves bounds for the first two field derivatives of functions of $\log\sum_k p_k e^{kh}$ and justifies dominated differentiation. The contact polynomial and pair polynomial specialize it to the tilted moments, second derivative of $H_n$, and kernel term.
- **Reason:** Pointwise integrability of a derivative at one height alone does not justify differentiation under an integral. The finite contact degree gives $0\le x'\le2^n$ and $0\le x''\le4^n$ and integrable dominating functions at the base height.
- **Classification:** Imprecision.
- **Mathematical effect:** Adds a proof of the omitted interchange at every field, including $n=0$, without any new disorder-moment assumption.
- **Paper argument checked:** Yes, with the missing justification supplied by `field_envelope` and the separate integrability declarations.
- **Manuscript action:** A clarification is recommended for the manuscript.
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
- **Paper argument checked:** Partly: the displayed intermediate formula is bypassed, but the resulting spine laws, indices, weights, and logarithmic identities were checked in the independent re-audit of this proof.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D10 — Summable spine drift from critical moments

- **Paper:** `response:linear` estimates the spine increments and then applies Paley–Zygmund and the passage estimate.
- **Formalization:** The same route is used, but the positive part of the drift is $H_j/A_j$; after an eventual $A_j\ge1$ reduction, `criticalMoments` bounds its positive part by a geometric sequence. This directly supplies the summability premise of `response_ballot`.
- **Reason:** Reuses an already proved uniform estimate instead of reconstructing a separate drift bound.
- **Classification:** Formalization choice.
- **Mathematical effect:** Local simplification; the centered fourth-moment and quadratic lower-tail arguments, and hence the final linear derivative bound, are unchanged.
- **Paper argument checked:** Yes; the alternative derivation of the drift premise and all dominating integrals were checked in the independent re-audit.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D11 — `eq:Hsmall` by floor-centred corrections

- **Paper:** The estimate $|H_n|\le C_B((A_n-1)^++\rho^n)$ is obtained within the product analysis.
- **Formalization:** `criticalProduct_Hsmall` is proved before `criticalProduct`: the defect recurrence is differentiated around the deterministic floor, floor-product divergence supplies the required contradiction with bounded moments above $\theta$, and a backward-summed derivative inequality gives the estimate.
- **Reason:** This isolates the estimate and avoids circular use of `returns_to_one` or the final product theorem.
- **Classification:** Formalization choice.
- **Mathematical effect:** Alternative proof of the same bound with a constant depending only on $B$, chosen before the disorder law.
- **Paper argument checked:** Partly: the paper's product-route derivation is replaced; the independent re-audit checked the alternative recurrence, geometric comparison, and absolute-value conclusion.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D12 — Critical-product divergence by a direct Nash estimate

- **Paper:** P1 is obtained through a separate product-divergence/Taylor argument before the residue bootstrap.
- **Formalization:** `Proofs/ProductProof.lean` uses `criticalProduct_Hsmall` directly and obtains reciprocal summability and the quadratic product bounds through a direct Nash estimate; the cubic-residue bootstrap and subsequent rates then proceed with integrable moment recurrences.
- **Reason:** The direct estimate shortens the dependency chain and supplies divergence from reciprocal summability.
- **Classification:** Formalization choice.
- **Mathematical effect:** Different proof of P1; P2–P5 and the quantifier order of the statement are preserved.
- **Paper argument checked:** Partly: the separate divergence argument of the paper is bypassed; the independent re-audit checked the Nash route and the remaining residue/rate steps.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D13 — Ordered pair count and tree-induction second moment

- **Paper:** `escape:pairs` uses an unordered pair-of-pairs count and its overlap estimate.
- **Formalization:** `Proofs/EscapePairs.lean` represents the hard recursion on `HardTree`, counts each qualifying unordered pair twice at its most recent common ancestor, computes the ordered mean $2\mu$, and proves the second-moment bound by induction on the tree. Paley–Zygmund is applied in the form $2c\mathbb EZ\le\mathbb EZ^2+c^2\mathbb P(Z\ne0)$.
- **Reason:** Ordered pairs make the recursive expectation calculations and product integrations systematic.
- **Classification:** Formalization choice.
- **Mathematical effect:** After division by four, the ordered estimate is exactly the paper's $\mathbb EZ^2\le\mu+\mu^2+2^{1-k}M_I\mu$, with the same final tail constant; the degenerate case $M_I=0$ is included.
- **Paper argument checked:** Partly: the paper's pair-of-pairs enumeration is replaced; the independent re-audit checked the law equivalence, count, overlap induction, and arithmetic.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D14 — Compactness by small-$s$ expansion and coefficient extraction

- **Paper:** `scaling:compactness` derives the ODEs and moments from the limiting transform and excludes an atom by a large-weight argument.
- **Formalization:** The Riccati recurrence is integrated on time intervals; its small-$s$ expansion and finite-difference coefficient extraction give the three ODEs and the drift/second/third-moment limits. Compensated-Laplace coefficient extraction yields moments 1–3. The no-atom step uses $s\to\infty$ with dominated convergence and a countable cover of $(0,T]$.
- **Reason:** This separates the formal limits from equalities of named coefficients and makes the $7/2$-moment domination and all local time integrals explicit.
- **Classification:** Formalization choice.
- **Mathematical effect:** Local alternative derivations inside the same subsequential compactness theorem. Weak convergence is genuine finite-measure convergence, and the extracted measures have zero mass only outside the paper's time domain.
- **Paper argument checked:** Partly: extraction, no-atom, and moment steps differ; the independent re-audit checked the two diagonal selections, local uniform convergence, measure construction, entrance bounds, and matching.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D15 — Window $7/2$ moment by weighted AM–GM

- **Paper:** The $7/2$ window moment is handled by a Hölder-type interpolation within the window-moment argument.
- **Formalization:** `Proofs/WindowProof.lean` uses weighted AM–GM, contact-polynomial differentiation, mean-value bounds, and factorwise control of the product ratio.
- **Reason:** Weighted AM–GM fits the available integer contact and tilted moments and gives a direct integrable dominating bound throughout the window.
- **Classification:** Formalization choice.
- **Mathematical effect:** Local alternative proof of the $7/2$ estimate; all six window bounds of the paper and the derivative bounds are retained with explicit constants.
- **Paper argument checked:** Yes for the overall window strategy, with the interpolation step replaced; the independent re-audit checked integrability, denominators, and derivative envelopes.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D16 — Profile measure identification through characteristic functions

- **Paper:** After regularization, polynomial rigidity, and the scalar Riccati identification, `th:profile-identification` concludes by uniqueness of Laplace transforms.
- **Formalization:** The same regularized equations and Riccati route prove that the candidate measure is exponential; an exponential/characteristic-function identification gives the final equality with the sine profile.
- **Reason:** This provides a direct uniqueness argument compatible with the complex analytic infrastructure already used for polynomial rigidity.
- **Classification:** Formalization choice.
- **Mathematical effect:** Alternative final identification step, with the same common initial interval and the same exact critical limits.
- **Paper argument checked:** Partly: the main rigidity argument is retained, while the final Laplace-uniqueness invocation is replaced. Positivity before division and the almost-everywhere finiteness/integrability domain were checked in the independent re-audit.
- **Manuscript action:** None.
- **Unresolved obstruction, if any:** None.

### D17 — Redundant hypotheses retained in statements

- **Paper:** `lem:barrier` is stated at $h_c>h_a$ for $n\ge1$.
- **Formalization:** `Critical.barrier` preserves those hypotheses, but its proof uses neither `hshift` nor `hn`; the contraction argument and critical-point characterization suffice more generally. The statement was not strengthened after this was observed.
- **Reason:** Statements fixed before their proofs were preserved rather than optimized afterwards.
- **Classification:** Formalization choice.
- **Mathematical effect:** Two harmless redundant assumptions remain. Similar unused parameters of internal interfaces noted by the re-audits do not alter any conclusion; they are not treated as coverage defects.
- **Paper argument checked:** Yes; non-use of a hypothesis cannot supply a missing conclusion, and the remaining argument was independently audited.
- **Manuscript action:** None required.
- **Unresolved obstruction, if any:** None.

### D18 — Further local repairs in compactness, profile, and continuation

- **Paper:** The formalization identified compressed or imprecise steps: the vector used in the left-half-plane estimate has an apparent pole at $s=0$; polynomial growth needs a split logarithmic time integral; degree reduction needs absolutely continuous coefficients and $k+2$ weights; the base-weight bound is worded circularly; first-mesh-cell entrance bounds need a different order of limits; time kernels and uniqueness measurability need justification; and an interior uniform upgrade does not itself reach the right endpoint of $I$.
- **Formalization:** The proofs respectively restrict the vector estimate away from $s=0$, split the time integral, use a.e. absolutely continuous flux equations and $k+2$ weights, close the base bound by a first-exit argument, work away from the first cell before taking limits, construct measurable kernels and use deterministic factorial envelopes for uniqueness with moving tests, and extend the continuation chain slightly beyond $\max I$.
- **Reason:** These are the precise side conditions and order-of-limit choices required by the existing arguments.
- **Classification:** Imprecisions; no new hypothesis on the final theorem.
- **Mathematical effect:** Local proof repairs with unchanged numbered conclusions.
- **Paper argument checked:** Yes with these repairs, as covered by the re-audits of the compactness, profile, continuation, and transform proofs; the formalization does not claim the imprecise literal shortcuts.
- **Manuscript action:** Clarifications are recommended for the manuscript, together with expository and notational remarks not reproduced here as mathematical differences.
- **Unresolved obstruction, if any:** None.

## Corrections to the paper

Two localized correctness issues were confirmed within the reviewed scope in
the research draft of 18 November 2026: a display of the Mellin calculus of
Section 5 that is false for unbounded weights $s$ (D4), and the reading of the
matrix-growth constant of `lem:entire-bounds` (Section 6) as uniform over the
coefficient $w$ (D5). In both cases the intended, repaired reading is proved
and is sufficient for every application; neither affects Theorem `th:bkt` or
another numbered conclusion. Both corrections are incorporated in the final
version of 19 November 2026.

No other numbered result was found to be false within the reviewed scope. No
error in a cited work was confirmed within that scope, so there is no
cited-work erratum to report. Expository ambiguities and missing proof
justifications are distinguished from mathematical proof alternatives in
D1–D18.

## From the formalized draft to the final version

The formalization was developed against the research draft of 18 November
2026; this record cites the final version of 19 November 2026. The two were
compared mechanically on all theorem-like environments (24 in each) and all
labelled displays (92 in each):

- 20 of the 24 numbered results are unchanged, word for word.
- `response:ballot`: the quantifiers "for some $b\ge0$ and $\eta,\delta>0$"
  moved into the hypothesis; same content, as in Lean.
- `scaling:mellin-calculus`: $n\ge1$, a Borel measurable $F$ and
  differentiability in a neighbourhood of $1$ are now assumed, and the
  transform-difference estimate is stated for $s$ in a compact set; the
  displays `scaling:measure` and `scaling:unshifted` restrict the weights to
  $0\le s\le N\log2$. These are the Lean hypotheses (correction D4).
- `lem:entire-bounds`: a measurable $w$ with $w$ and $1/w$ bounded,
  $M(0,z)=I$, and the constant $C_{\varepsilon,T,w}$, as in Lean (correction
  D5).
- `escape:pairs`, with the displays `escape:first-pair-moment` and
  `escape:pair-tail`: the band moment $M_I$ is renamed $W$; same content.

No statement of the final version goes beyond its Lean counterpart. The
paper's prose and proofs also changed elsewhere (about 600 lines); the
proof-correspondence column above was established against the draft of
18 November 2026 and has not been re-reviewed against these changes.

## Verification and assumptions

All checks below were run on 19 November 2026 on the development tree from
which this repository was exported. The export removed private working
material and an unused draft library, and the documentation in the Lean files
is revised for publication (prose only). **None of these checks has yet been
repeated on this repository's published commit**; they must be before any
claim about that commit.

- **Build:** **passed** after the final proof cleanup:
  `lake build DiamondPinning Solution` (3,420 jobs), with Lean `v4.35.0` and
  Mathlib `v4.35.0` at `56a005855ea17e0b0958f73ec801ae140b0a1679` and the
  dependency revisions of `lake-manifest.json`.
- **Axioms:** **passed** after the final proof cleanup for every one of the
  72 theorems of `DiamondPinning/Statements/`, including `DiamondPinning.bkt`:
  only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, no
  `native_decide` or `bv_decide` dependency. The development contains no
  `sorry`; `Challenge.lean` contains six by design.
- **Semantic dependencies:** `Model.Defs.lawR` constructs the finite-volume
  laws; `freeEnergy_tendsto` and `criticalPoint_isGreatest` characterize the
  totalized `limUnder`/`sSup` definitions. Positivity and integrability lemmas
  support every use of `Real.log`, real powers, Bochner integrals, and
  derivatives. `Model.Scaling.EntranceData` contains the paper's limit ODE,
  measure, entrance, Taylor, and matching claims, rather than hypotheses that
  merely assume the desired profile. `Model.Scaling.WeakConvergence` includes
  finiteness and convergence for bounded continuous integrals.
  `Model.InstancePins` preserves the `NormedSpace ℝ ℝ` instance used by the
  statements and the Challenge.
- **Statement preservation:** **passed** after the final proof cleanup. The
  statements were fixed in six groups before their proofs were written, and
  each group's recorded declaration fingerprints were checked unchanged at
  completion:

| Group | Fixed on | Paper | Definitions and statements (number of theorems) |
| --- | --- | --- | --- |
| 1 | 18 Nov 2026 | `th:bkt`, part of `lem:basic-bounds` | `Model/Defs.lean`; `Statements/Main.lean` (6); `Challenge.lean`, `Solution.lean`, `comparator.json` |
| 2 | 18 Nov 2026 | Disorder environment | `Model/Env.lean`; `Statements/Env.lean` (3) |
| 3 | 19 Nov 2026 | Sections 2–3 and standalone lemmas | `Model/Moments.lean`, `Model/Basic.lean`; `Statements/Critical.lean` (9), `Ballot.lean` (2), `OneSided.lean` (1), `EntireBounds.lean` (4) |
| 4 | 19 Nov 2026 | Sections 4 and 8 | `Model/Contacts.lean`, `Spine.lean`, `Window.lean`, `Hard.lean`; `Statements/Response.lean` (21), `Escape.lean` (8) |
| 5 | 19 Nov 2026 | Sections 5–7 | `Model/Profile.lean`, `Model/Scaling.lean`; `Statements/Scaling.lean` (10), `Profile.lean` (3) |
| 6 | 19 Nov 2026 | Remaining parts of `lem:basic-bounds` | `Model/LogMean.lean`; `Statements/FreeEnergyBounds.lean` (5) |

- **Statement review:** before being fixed, each group was reviewed against
  the paper by models that did not write it: Claude Sonnet 5.5 for groups
  1–5, with GPT‑6.2 Sol also auditing group 1 and blind read-backs of
  groups 1 and 3; GPT‑6.2 Astra for group 6. The author delegated the approval
  of each group to a read-only consultation of GPT‑6.2 Astra, which
  recommended approval, in some cases after corrections that were applied
  before fixing. No human line-by-line review of the statements is claimed.
- **Proof re-audits:** **passed**, with no open mathematical-soundness or
  statement-fidelity finding. Every proof was re-audited read-only against
  the paper by a model other than its author, checking the route,
  totalization (`limUnder`, `sSup`, Bochner integrals of non-integrable
  functions, division by zero), integrability, positivity and quantifier
  order; these audits did not replace the builds, statement checks or axiom
  queries.

| Results | Proof written by | Re-audited by |
| --- | --- | --- |
| `integrable_lawR`, `integrable_tiltedLogPower`, `integrable_log_lawR`; disorder environment | Kimi K3.1 Pro; GPT‑6 Luna | Claude Sonnet 5.5 |
| `freeEnergy_tendsto`, `criticalPoint_isGreatest` | GPT‑6 Luna | Kimi K3.1 Pro |
| Remaining parts of `lem:basic-bounds` | Claude Opus 5.5 | Claude Sonnet 5.5 |
| `lem:mellin-correction`, `eq:jensen`, `lem:barrier`, hard recursion | Kimi K3.1 Pro | Claude Sonnet 5.5 |
| `prop:criticalmoments`; `th:return`, `eq:Hsmall`; `lem:entire-bounds` E1 | GPT‑6.2 Sol | Kimi K3.1 Pro |
| `lem:one-sided`, `response:ballot`, contact representation, integrability, field envelope, field derivatives, `response:spine-identities`, `lem:entire-bounds` E2, `scaling:mellin-calculus`, `escape:band-exit`, `escape:comparison` | Kimi K3.1 Pro | Claude Sonnet 5.5 |
| `escape:pairs`, `prop:window-moments`, `scaling:compactness`, final assembly of `th:bkt` | Claude Opus 5.5 | Kimi K3.1 Pro |
| `th:product`, `th:response`, `th:profile-identification`, `cont:continuation` | GPT‑6.2 Sol | Kimi K3.1 Pro |
| `response:linear`, `prop:contact-moments` | Kimi K3.1 Pro, completed by Claude Opus 5.5 | Kimi K3.1 Pro |
| `cont:freeenergyupper`, `escape:constant`, exact critical limits | GPT‑6 Luna, GPT‑6.2 Sol | Kimi K3.1 Pro |

  The re-auditor belongs to a different model family from the proof's author
  except in two rows: the remaining parts of `lem:basic-bounds` (Claude
  re-audited by Claude) and `response:linear` with `prop:contact-moments`
  (begun by Kimi, re-audited by Kimi). After the re-audits, a cleanup pass by
  Kimi K3.1 Pro removed duplicated lemmas, replaced broad imports and
  improved documentation in proof modules without changing any statement;
  it was checked by the build, statement-preservation and axiom checks above,
  not re-audited.
- **Comparator:** **passed**, 19 November 2026, on a Linux virtual machine,
  at commit `eafa34c` of this repository (its content, file by file). The
  sandboxed `lake comparator` exited 0 for the six theorems of
  `comparator.json`: the statement comparison and the axiom check passed,
  and both the NanoDa and Lean default kernels accepted the solution ("Your
  solution is okay!"). `lake comparator --paranoid` also exited 0: NanoDa
  (configured and bundled), Lean's paranoid kernel, Lean4Lean, con-leche,
  con-ron and Lean's default kernel all accepted. Versions: Lean 4.35.0,
  Lake 5.0.0, NanoDa 0.4.19, `bwrap` 0.11.1. Because the toolchain directory
  was reached through a symbolic link, which the sandbox's bind of
  `nanoda_bin` did not follow, a byte-identical copy of `nanoda_bin` (SHA-256
  `cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5`) in a
  project-local directory first on `PATH` was used; the sandbox and the
  configuration were unchanged. The same check had passed earlier at a
  development revision before the final proof cleanup.
- **Full deposit verification (Palomar preflight):** **not run**; it needs
  the public repository and its exact commit.

Building and kernel checking show that the Lean statements are proved from the
listed axioms; they do not show that the statements say what the paper says,
and a Challenge and a Solution can share a misreading of the paper.

## How the formalization was produced

The work was done by AI models between the evening of 18 November and the
morning of 19 November 2026, orchestrated by Claude Code running Claude
Opus 5.5, which built the inventory of the paper's results and their
dependency graph, wrote the shared definitions and the main statements,
integrated the proofs, wrote the assembly proofs, and ran the build,
statement-preservation and axiom checks. Before any statement was written,
GPT‑6.2 Astra researched Sections 2–7 and the hard recursion of Section 8,
and Claude Opus 5.5 audited that research. This research identified the
extended-valued $F_d$ convention, the differentiation envelope, the
Mellin-domain repairs, and the measurable-coefficient and constant issue in
`lem:entire-bounds`. Claude Sonnet 5.5 wrote a proof blueprint. Routine
statements were drafted by Kimi K3.1 Pro, and the definitions and statements
of Sections 4–8 by Claude Opus 5.5 workers, before review.

Proofs were written by isolated workers: Kimi K3.1 Pro (effort `high`),
GPT‑6.2 Sol (`medium`), GPT‑6 Luna (`xhigh`) and Claude Opus 5.5 (`high` or
`xhigh`), the GPT models through the Codex CLI. Each worker owned its helper
modules and received the fixed statement verbatim; integration only filled
each fixed statement with a call to a proved helper, after which the
statement-preservation and axiom checks were rerun. Independent re-auditors
then compared the routes with the paper (see the table above). Alternative
routes are recorded above rather than being treated as verification of
bypassed arguments of the paper. The sandboxed Comparator ran on a Linux
virtual machine.

The paper's author decided the scope and was consulted on interface choices,
for which the author delegated the decisions, including the approval of
statements, to GPT‑6.2 Astra consultations. Publication, licensing, and
submission to Palomar were not delegated.

A different Lean proof can verify the result without verifying the written
argument it bypasses. In particular, an alternative proof does not silently
repair a gap in the manuscript; the affected entries D4, D5, D7, and D18
correspond to recommended changes to the manuscript.

## Unresolved coverage or correspondence obligations

### Mathematical coverage

All 24 numbered theorems, propositions, and lemmas are matched to proved
declarations and have no outstanding proof obligation. The introduction's
Gaussian example is excluded by the author's scope decision.

Three routine Section 1 identities remain only partially matched under this
report's strict declaration-level criterion:

1. **S1.4, `eq:log-model`:** add a declaration for the law of
   $\log R_n/\log B$ and its transformed recursion, using `lawR` or the
   environment bridge. Related logarithmic encodings exist, but no theorem
   stating this identity.
2. **S1.5:** add standalone algebraic declarations for
   $R_n^\theta=2^{X_n}$ and the $X_n$-forms of $H_n$ and $J_n$. The moments
   and their integrability are proved in the $\log R_n-a$ normalization, but
   the three displayed identities are not separately exported.
3. **S1.6:** export the two elementary pole-scale identities currently used
   only within the scale/energy assembly. `escape_constant` and `bkt` prove
   the resulting asymptotics, not these standalone equalities.

These are coverage gaps for three routine items, not missing dependencies of
`DiamondPinning.bkt`. They can be closed in a new helper module without
changing any existing statement.

### Release and verification obligations

1. **Checks on the published commit:** the build, the axiom check and the
   sandboxed `lake comparator` (with `--paranoid`) passed at `eafa34c`; a
   later commit that changes Lean code needs them again, and the Palomar
   full preflight checks the commit submitted.
2. **Independent re-audit of the cleanup pass:** the final cleanup of proof
   modules was checked mechanically (build, statement preservation, axioms,
   Comparator), not re-audited by a model.
3. **Publication:** the license, the public repository, the full Palomar
   preflight at its public commit and the submission are the author's
   decisions and have not been carried out.
