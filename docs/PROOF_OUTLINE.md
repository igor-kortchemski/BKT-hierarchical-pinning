# Proof outline

This outline follows *BKT asymptotics for the quenched free energy of
hierarchical pinning* by Igor Kortchemski (version of 19 November 2026).
Labels such as `th:product` are the paper's; Lean links point to the proved
statements in [`DiamondPinning/Statements/`](../DiamondPinning/Statements/),
and D-entries to the
[formalization report](../FORMALIZATION_REPORT.md#substantive-differences).

## The model and the main theorem

Fix $B>2$, $c=B-1$ and a disorder $W>0$ with $\mathbb E W=1$. The diamond
hierarchical pinning model [DHV92, Section 4.2, (4.10)], in the framework of
[GLT10], has partition functions $R_0(h)=e^hW$ and
$R_{n+1}(h)=(R_n^{(1)}(h)R_n^{(2)}(h)+c)/B$ in law, with independent copies on
the right. Its quenched free energy is $F(h)=\lim_n2^{-n}\mathbb E\log R_n(h)$,
with critical point $h_c=\sup\{h:F(h)=0\}$; the annealed critical point is
$h_a=\log c$ [GLT10, Theorem 1.2]. Write $a=\log B$, $\theta=\log2/a$,
$\rho=2/B$, $Z_n=\log R_n-a$ and, at $h_c$, $A_n=\mathbb E R_n^\theta$,
$\Pi_n=\prod_{j<n}A_j$ and $(H_n,K_n,J_n)=\mathbb E[R_n^\theta(Z_n,Z_n^2,Z_n^3)]$.
Theorem `th:bkt` ([`DiamondPinning.bkt`](../DiamondPinning/Statements/Main.lean#L92)):
if $h_c>h_a$, then $\ell_3=\lim J_n/\Pi_n$ and
$\kappa=\lim\partial_hH_n(h_c)/\Pi_n$ exist in $(0,\infty)$,
$\Pi_n\sim3a^3n^2/(2\ell_3)$, and, with $\gamma=3a^2\kappa/(2\ell_3)$,

$$
\lim_{u\downarrow0}\sqrt u\,\log F(h_c+u)=-\frac{\pi\log2}{\sqrt\gamma}.
$$

This is the Berezinskii–Kosterlitz–Thouless law predicted in [TC01] and
[DR14]. In the coordinates $X_n=\log R_n/a$, for which $R_n^\theta=2^{X_n}$,
the recursion is a smooth analogue of the hard recursion
$Y_{j+1}=(Y_j^{(1)}+Y_j^{(2)}-1)^+$ studied in [CEGM84a, CEGM84b].

## 1. Free energy and critical point (Section 2)

**Proved** (`lem:basic-bounds`). With $b_0=0$ and $b_{n+1}=(b_n^2+c)/B$:
$R_n\ge b_n\uparrow1$ and $1-b_n=O(\rho^n)$; all tilted logarithmic moments
are finite; $F\ge0$ exists and
$2^{-n}(\mathbb E\log R_n-a)\le F(h)\le2^{-n}(\mathbb E\log R_n-\log b_n)$ for
$n\ge1$; $0\le F(h+u)-F(h)\le u$ for $u\ge0$; $h_a\le h_c<\infty$ and
$F(h_c)=0$.

**Idea.** The finite-volume argument of [GLT10, Theorem 1.1 and Appendix A.1]
with the floor kept explicit: $\log R_n-a$ is superadditive and $R_n/b_n$
submultiplicative along the recursion, so the two bounds are monotone in $n$.
Multiaffinity in the $2^n$ leaf weights gives the Lipschitz bound, and
Jensen's inequality at $h_a$, where $\mathbb E R_n=c$, gives $F(h_a)=0$.

**Lean.** [`integrable_lawR`](../DiamondPinning/Statements/Main.lean#L33),
[`integrable_tiltedLogPower`](../DiamondPinning/Statements/Main.lean#L42),
[`integrable_log_lawR`](../DiamondPinning/Statements/Main.lean#L52),
[`freeEnergy_tendsto`](../DiamondPinning/Statements/Main.lean#L60),
[`criticalPoint_isGreatest`](../DiamondPinning/Statements/Main.lean#L70),
[`floor_bounds`](../DiamondPinning/Statements/FreeEnergyBounds.lean#L33),
[`finiteSize_bounds`](../DiamondPinning/Statements/FreeEnergyBounds.lean#L41),
[`freeEnergy_nonneg`](../DiamondPinning/Statements/FreeEnergyBounds.lean#L50),
[`freeEnergy_increment`](../DiamondPinning/Statements/FreeEnergyBounds.lean#L57),
[`logShift_le_criticalPoint`](../DiamondPinning/Statements/FreeEnergyBounds.lean#L67).
The law of $R_n$, $F$ and $h_c$ are constructed in
[`Model/Defs.lean`](../DiamondPinning/Model/Defs.lean), and the companion
theorems identify them with the paper's limit and supremum
([D2](../FORMALIZATION_REPORT.md#d2--constructed-law-level-free-energy-and-critical-point)).

## 2. Critical moments and returns to one (Section 2)

**Proved.** `prop:criticalmoments`: if $F(h)=0$, then
$\mathbb E R_n^\theta\le c^\theta$, $H_n\le C_B\rho^n$ and
$\sup_n\mathbb E[R_n^\theta|Z_n|]<\infty$. `lem:mellin-correction`: holomorphy
of the correction $C_n(z)=\mathbb E[(S_n+c)^z-S_n^z]$,
$S_n=R_n^{(1)}R_n^{(2)}$, on $\Re z<1$. `lem:barrier`: at $h_c>h_a$,
$\mathbb E R_n^q\ge b_n^q+B^q-2$ for $\theta<q<1$. `th:return`:
$\liminf_nA_n=1$.

**Idea.** A favourable-block argument adapted from [LT09, proof of Theorem
3.1, (3.7)–(3.10)] turns $F=0$ into the tail bound
$\mathbb P(R_n\ge t)\le4(b_n/t)^{\theta_n}$, $\theta_n\uparrow\theta$, and
convexity then bounds $\mathbb E R_n^q$ by $c^q$ for $q<\theta$. The barrier is
a floor-centred form of [GLT10, Proposition 4.1, (4.1)–(4.3)]. For the return,
$G_n(z)=\mathbb E R_n^z$ satisfies $G_n(z)^2=B^zG_{n+1}(z)-C_n(z)$. If
$G_n(\theta)\ge1+\delta$ for all large $n$, then, as $B^\theta=2$, the backward
map $v\mapsto(\sqrt{B^zv_{n+1}-C_n(z)})_n$ is a contraction in $\ell^\infty$
near $z=\theta$, and its holomorphic fixed point gives uniform moments above
$\theta$. These are excluded: they would extend to $q=1$, contradicting the
growth of $\mathbb E R_n$ from $\mathbb E R_0=e^{h_c}>c$ (compare [DR14,
Appendix B]).

**Lean.** [`criticalMoments`](../DiamondPinning/Statements/Critical.lean#L67),
[`jensen_step`](../DiamondPinning/Statements/Critical.lean#L56),
[`correction_eq`](../DiamondPinning/Statements/Critical.lean#L32),
[`differentiableOn_correction`](../DiamondPinning/Statements/Critical.lean#L40),
[`correction_bounded`](../DiamondPinning/Statements/Critical.lean#L48),
[`barrier`](../DiamondPinning/Statements/Critical.lean#L78),
[`returns_to_one`](../DiamondPinning/Statements/Critical.lean#L88). Same
route, with the continuation written as a uniform Picard iteration.

## 3. The critical product (Section 3)

**Proved** (`th:product`). $\Pi_n\asymp n^2$, $\sum_n\Pi_n^{-1}<\infty$,
$|H_n|\le C_B((A_n-1)^++\rho^n)$, $\ell_3=\lim J_n/\Pi_n\in(0,\infty)$,
$L_n=\mathbb E[R_n^\theta Z_n^4]\le C(n+1)^3$, $A_n-1\asymp n^{-1}$,
$K_n\asymp n$, $H_n=O(n^{-1})$ and $R_n\to1$ in probability.

**Idea.** Critical product bounds and the cubic-moment method go back to
[CEGM84b, Appendix III of the 1983 archival version] for the binary hard
recursion; see [CDHLS19, Section 2] for general branching. Here the tilted
moments obey exact recurrences with bounded soft correction kernels, such as
$J_{n+1}=A_nJ_n+3H_nK_n+\frac12\mathbb E\,\omega_3(R_n^{(1)}R_n^{(2)})$, so
that $K_n/\Pi_n$ and $J_n/\Pi_n$ are almost monotone. Cauchy–Schwarz gives a
Nash-type inequality $A_n/b_n^\theta-1\ge c_0/(K_n+1)$, which makes
$\sqrt{\Pi_n}$ grow linearly. If $\ell_3$ vanished, a bootstrap would bound
$K_n$, and the Nash inequality would keep $A_n$ away from $1$, contrary to
`th:return`. Finally $J_n^2\le K_nL_n$ and $L_n\le C(n+1)\Pi_n$ give
$\Pi_n\le Cn^2$.

**Lean.** [`criticalProduct_Hsmall`](../DiamondPinning/Statements/Critical.lean#L98),
[`criticalProduct`](../DiamondPinning/Statements/Critical.lean#L113). The bound
on $|H_n|$ is proved first, from floor-centred corrections
([D11](../FORMALIZATION_REPORT.md#d11--eqhsmall-by-floor-centred-corrections)),
and the divergence of $\Pi_n$ comes directly from the Nash estimate rather than
from the paper's separate argument
([D12](../FORMALIZATION_REPORT.md#d12--critical-product-divergence-by-a-direct-nash-estimate)).

## 4. Field response and strict transversality (Section 4)

**Proved.** `th:response`: $\partial_hH_n(h_c)/\Pi_n\to\kappa\in(0,\infty)$.
On the way: the passage estimate `response:ballot`,
`response:spine-identities`, `response:linear`
($\partial_h\mathbb E R_n(h)^\theta|_{h_c}\le C(n+1)$), and the contact and
window estimates `prop:contact-moments`, `prop:window-moments` for
$0\le(h-h_c)(n+1)^2\le\eta$.

**Idea.** Distinguish one leaf, as in the spine method of [LPP95, Section 2],
applied to the hard recursion in [HS18, Section 4, (4.1)–(4.3)]. Under the
tilted laws $r^\theta\mathbb P(R_j\in dr)/A_j$ of the sibling subtrees, field
derivatives become expectations along a walk $S_k=\sum_{j<k}(\log U_j-a)$ with
independent increments, for instance

$$
\frac{\partial_h\mathbb E R_n(h)^\theta|_{h_c}}{\Pi_n}
=\theta A_0\,\widehat{\mathbb E}\Bigl[\Bigl(1+\frac{c}{BR_0^{\ast}}\sum_{k=1}^ne^{-S_k}\Bigr)^{\theta-1}\Bigr].
$$

By Step 3 the walk has summable positive drift and variance of order $n^2$; a
ballot estimate, from stopping times and Harris's inequality [Harris60, Lemma
4.1], gives $\widehat{\mathbb P}(\min_{k\le n}S_k\ge-z)\le C(z+1)/(n+1)$. Walks
kept above a logarithmic barrier give $\liminf_n\partial_hH_n(h_c)/\Pi_n>0$,
and differentiating the recurrence for $H_n$ shows that this ratio has summable
positive variations, hence converges. The Gibbs contact count $\mathcal C_n$
of [GLT10, Section 1.2 and Appendix A, (A.11)] satisfies
$R_n(h_c+u)=R_n(h_c)\langle e^{u\mathcal C_n}\rangle_n$, and factorial bounds
$\mathbb E[R_n^\theta\langle\mathcal C_n^k\rangle_n]\le k!\,ML^{k-1}(n+1)^{2k-1}$
give Taylor expansions of $A_n,H_n,K_n,J_n$ in the window.

**Lean.** [`response_ballot`](../DiamondPinning/Statements/Ballot.lean#L36),
[`response_ballot_uniform`](../DiamondPinning/Statements/Ballot.lean#L55),
[`spine_identities`](../DiamondPinning/Statements/Response.lean#L145),
[`response_linear`](../DiamondPinning/Statements/Response.lean#L157),
[`response_transversality`](../DiamondPinning/Statements/Response.lean#L169),
[`contactMoments`](../DiamondPinning/Statements/Response.lean#L187),
[`windowMoments`](../DiamondPinning/Statements/Response.lean#L212),
[`window_derivBounds`](../DiamondPinning/Statements/Response.lean#L238),
[`field_envelope`](../DiamondPinning/Statements/Response.lean#L309). The spine
identities come from a bounded-test identity proved by induction
([D9](../FORMALIZATION_REPORT.md#d9--spine-identities-through-a-master-induction)),
Harris's inequality is proved in Lean
([D8](../FORMALIZATION_REPORT.md#d8--harriss-inequality-proved-from-scratch)),
the drift bound reuses `prop:criticalmoments`
([D10](../FORMALIZATION_REPORT.md#d10--summable-spine-drift-from-critical-moments)),
the $7/2$ window moment uses weighted AM–GM instead of Hölder
([D15](../FORMALIZATION_REPORT.md#d15--window-72-moment-by-weighted-amgm)), and
differentiation under the expectation is justified by an explicit envelope
([D7](../FORMALIZATION_REPORT.md#d7--fixed-height-differentiation-envelope)).

## 5. The near-critical scaling limit (Sections 5–7)

**Proved.** Fix $\lambda\ge0$, work at $h_c+\lambda/N^2$ and generation
$n=\lfloor Nt\rfloor$, and let
$\nu_N(t,dx)=N\,\mathbb E[(R_n^\theta-1)\mathbf 1_{\{R_n\ge1\}}\delta_{\log R_n/(aN)}(dx)]$
and $L_N(t,s)=N(\mathbb E R_n^{\theta-s/(aN)}-1)$. With $v=\gamma\lambda$ and
$u_v(t)=\sin(\sqrt v\,t)/\sqrt v$, the profile is

$$
f_v(t,x)=a_v(t)e^{-b_v(t)x},\qquad a_v=\frac4{u_v^2},\qquad b_v=\frac{2u_v'}{u_v},\qquad T_v=\frac{\pi}{\sqrt v}.
$$

`scaling:compactness`: subsequential limits with limit equations and entrance
data. `th:profile-identification`: every limit is $f_v$ on an initial
interval; at criticality $n(A_n-1)\to2$, $K_n/(a^2n)\to1$,
$J_n/(a^3n^2)\to3/2$ and $\Pi_n/n^2\to3a^3/(2\ell_3)$, so
$\gamma=\lim\partial_hH_n(h_c)/(an^2)$. `cont:continuation`: for $\lambda>0$,
compact $I\subset(0,T_v)$ and $s>0$ with $s+\inf_Ib_v>0$,
$L_N(t,s)\to a_v(t)/(s+b_v(t))$ uniformly on $I$, and
$e^{-sx}\nu_N(t,dx)\to e^{-sx}f_v(t,x)\,dx$ weakly.

**Idea.** *Compactness.* The transforms obey an exact recurrence whose defect
sums to $O(N^{-1})$ over a time window (`scaling:mellin-calculus`). With the
window estimates of Step 4, Helly's and Arzelà–Ascoli's theorems give limits
$S,d,K,P$ of the rescaled $A_n,H_n,K_n,J_n$ with $d'=Sd$, $K'=SK+d^2-1$,
$P'=SP+3dK$, a Riccati equation for the Laplace transform of the limit
measures, and entrance data $d(t)/P(t)\to\lambda\kappa a^2/\ell_3$ as
$t\downarrow0$. *Identification.* For each $t$, a regularized transform is an
entire function of the weight: positivity bounds it on the right, and a growth
bound for a canonical system with the Phragmén–Lindelöf principle [PL08,
Section II, no. 5] on the left (`lem:entire-bounds`). It is therefore a
polynomial, of degree at most one, which reduces the problem to $r'=v+r^2$,
$r(0)=0$, with $v=3\lambda\kappa a^2/(2\ell_3)=\gamma\lambda$. The exponential
family and its sine parametrization are those of [DR14, Section 3.2] and
[CDDS20, Section 2, (24)–(29)]. *Continuation.* The mass $a_v/b_v$ of $f_v$ is
infinite once $b_v\le0$, that is for $t\ge T_v/2$, so convergence is carried
in exponential weights: a first-exit bound at a base weight, the mild form of
$\partial_tf=\partial_xf+\frac12f\ast f$ with uniqueness in weighted norms,
and finitely many short intervals covering $I$.

**Lean.** [`transform_recurrence`](../DiamondPinning/Statements/Scaling.lean#L96),
[`transform_difference`](../DiamondPinning/Statements/Scaling.lean#L160),
[`scaling_compactness`](../DiamondPinning/Statements/Scaling.lean#L188),
[`continuation`](../DiamondPinning/Statements/Scaling.lean#L228) and the other
estimates of [`Scaling.lean`](../DiamondPinning/Statements/Scaling.lean);
[`one_sided_compactness`](../DiamondPinning/Statements/OneSided.lean#L33)
(`lem:one-sided`);
[`matrix_integral_growth_bound`](../DiamondPinning/Statements/EntireBounds.lean#L54),
[`rightHalfPlane_bounded_of_minimal_exponential_type`](../DiamondPinning/Statements/EntireBounds.lean#L73)
and their companions in
[`EntireBounds.lean`](../DiamondPinning/Statements/EntireBounds.lean);
[`profile_identification`](../DiamondPinning/Statements/Profile.lean#L39),
[`exact_critical`](../DiamondPinning/Statements/Profile.lean#L57),
[`gamma_eq_limit`](../DiamondPinning/Statements/Profile.lean#L76). The limit
equations and moments come from small-weight expansion and coefficient
extraction
([D14](../FORMALIZATION_REPORT.md#d14--compactness-by-small-s-expansion-and-coefficient-extraction)),
the last identification step uses characteristic functions instead of Laplace
uniqueness
([D16](../FORMALIZATION_REPORT.md#d16--profile-measure-identification-through-characteristic-functions)),
and Phragmén–Lindelöf comes from Mathlib's half-plane theorem
([D6](../FORMALIZATION_REPORT.md#d6--half-plane-phragménlindelöf-through-mathlib)).
Two local statements of these sections were corrected, without effect on
`th:bkt`; the cited version includes the corrections
([Corrections to the paper](../FORMALIZATION_REPORT.md#corrections-to-the-paper)).

## 6. Free-energy bounds and the BKT constant (Section 8)

**Proved.** `cont:freeenergyupper`:
$\limsup_{u\downarrow0}\sqrt u\log F(h_c+u)\le-\pi\log2/\sqrt\gamma$.
`escape:pairs`, `escape:band-exit`, `escape:comparison`, `escape:constant`:
$\liminf_NN^{-1}\log F(h_c+\lambda/N^2)\ge-T_v\log2$ for every $\lambda>0$.
Together they prove `th:bkt`.

**Idea.** *Upper bound.* For $t<T_v$, Step 5 gives
$\mathbb E R_n^{\theta-s/(aN)}=1+O(N^{-1})$ at $n=\lfloor Nt\rfloor$, hence
$\mathbb E\log R_n=O(N^{-1})$, and the finite-size bound of Step 1 gives
$F(h_c+\lambda/N^2)\le C2^{-\lfloor Nt\rfloor}$. *Lower bound.* With
$a_n=\log(B/b_n)$ and $Y_0=\lfloor\log(R_n/b_n)/a_n\rfloor$, an exact coupling
at the floor places the hard recursion below the diamond model, so
$F(h)\ge2^{-n}a_nF_{\mathrm d}$, where $F_{\mathrm d}=\lim_j2^{-j}\mathbb EY_j$.
Counting pairs of leaves in a band, with a second-moment bound, as in the
two-leaf amplification method of [HS18, Section 4.1, Lemma 4.1], gives the
band criterion: if $L\ge L_*$ and
$L\,\mathbb E[2^{Y_0}\mathbf 1_{\{\lceil3L/4\rceil\le Y_0\le L\}}]\ge D_*$,
then $F_{\mathrm d}\ge\frac12 2^{-2L}$, with $D_*=L_*=10^4$. For
$L=\lfloor\varepsilon N\rfloor$, Step 5 bounds the left side from below, in the
limit, by $\frac\varepsilon2\int_{4\varepsilon/5}^{9\varepsilon/10}f_v(t,x)\,dx$,
which diverges as $t\uparrow T_v$; hence
$F(h_c+\lambda/N^2)\ge2^{-N(T_v+2\varepsilon)+o(N)}$. Setting
$N=\sqrt{\lambda/u}$ turns the pole into the BKT scale, as identified in [DR14,
Section 3.2] and [CDDS20, (27)–(29)]:

$$
NT_v=\frac{\pi}{\sqrt{\gamma u}},\qquad
2^{-NT_v}=\exp\Bigl(-\frac{\pi\log2}{\sqrt{\gamma u}}\Bigr).
$$

**Lean.** [`freeEnergy_upper`](../DiamondPinning/Statements/Escape.lean#L123),
[`escape_pairs`](../DiamondPinning/Statements/Escape.lean#L74),
[`escape_bandExit`](../DiamondPinning/Statements/Escape.lean#L86),
[`escape_comparison`](../DiamondPinning/Statements/Escape.lean#L101),
[`escape_constant`](../DiamondPinning/Statements/Escape.lean#L142),
[`hardFreeEnergy_tendsto`](../DiamondPinning/Statements/Escape.lean#L45),
[`hardFreeEnergy_ge`](../DiamondPinning/Statements/Escape.lean#L54),
[`hardFreeEnergy_real`](../DiamondPinning/Statements/Escape.lean#L61), and
[`bkt`](../DiamondPinning/Statements/Main.lean#L92). The pair count is ordered,
with a second moment proved by induction on the tree; dividing by four
recovers the paper's estimate
([D13](../FORMALIZATION_REPORT.md#d13--ordered-pair-count-and-tree-induction-second-moment)).
$F_{\mathrm d}$ takes values in $[0,\infty]$, to cover initial laws of
infinite mean
([D1](../FORMALIZATION_REPORT.md#d1--extended-valued-hard-free-energy)).

## Dependencies

Step 1 is used throughout. Step 2 feeds Step 3: its bounds start the moment
recurrences, and `th:return` excludes $\ell_3=0$. Step 3 feeds Step 4:
$\Pi_n\asymp n^2$, $K_n\asymp n$ and the fourth-moment bound control the spine
walk and the contact moments. Steps 3 and 4 feed Step 5: the window estimates
give compactness, and $\ell_3,\kappa$ fix the entrance data, hence
$v=\gamma\lambda$; conversely, Step 5 at $\lambda=0$ sharpens Step 3 to exact
limits, including $\Pi_n\sim3a^3n^2/(2\ell_3)$. Step 5, with the finite-size
bounds of Step 1, feeds both bounds of Step 6. The proof of `th:bkt` combines
Steps 3–6. In Lean, the statements of Steps 5–6 take $\ell_3$, $\kappa$ and
$\gamma$ as parameters with their defining limits, supplied in `bkt`
([D3](../FORMALIZATION_REPORT.md#d3--residues-as-parameters-in-internal-interfaces)).

## References

Entries and locators are those of the paper's bibliography.

- [CDDS20] X. Chen, V. Dagard, B. Derrida and Z. Shi. The critical behaviors
  and the scaling functions of a coalescence equation. *J. Phys. A: Math.
  Theor.* **53** (2020), article 195202.
  [doi:10.1088/1751-8121/ab8134](https://doi.org/10.1088/1751-8121/ab8134).
- [CDHLS19] X. Chen, B. Derrida, Y. Hu, M. Lifshits and Z. Shi. A max-type
  recursive model: some properties and open questions. In V. Sidoravicius
  (ed.), *Sojourns in Probability Theory and Statistical Physics–III*,
  Springer Proceedings in Mathematics & Statistics **300**, Springer,
  Singapore, 2019, pp. 166–186.
  [doi:10.1007/978-981-15-0302-3_6](https://doi.org/10.1007/978-981-15-0302-3_6).
- [CEGM84a] P. Collet, J.-P. Eckmann, V. Glaser and A. Martin. A spin glass
  with random couplings. *J. Stat. Phys.* **36** (1984), 89–106.
  [doi:10.1007/BF01015728](https://doi.org/10.1007/BF01015728).
- [CEGM84b] P. Collet, J.-P. Eckmann, V. Glaser and A. Martin. Study of the
  iterations of a mapping associated to a spin glass model. *Comm. Math.
  Phys.* **94** (1984), 353–370.
  [doi:10.1007/BF01224830](https://doi.org/10.1007/BF01224830). Archival
  version: *Les rencontres physiciens-mathématiciens de Strasbourg–RCP25*
  **33** (1983), exposé 6, 117–142.
  [Numdam](https://www.numdam.org/item/RCP25_1983__33__117_0/).
- [DHV92] B. Derrida, V. Hakim and J. Vannimenus. Effect of disorder on
  two-dimensional wetting. *J. Stat. Phys.* **66** (1992), 1189–1213.
  [doi:10.1007/BF01054419](https://doi.org/10.1007/BF01054419).
- [DR14] B. Derrida and M. Retaux. The depinning transition in presence of
  disorder: a toy model. *J. Stat. Phys.* **156** (2014), 268–290.
  [doi:10.1007/s10955-014-1006-y](https://doi.org/10.1007/s10955-014-1006-y).
  Author version: [arXiv:1401.6919v1](https://arxiv.org/abs/1401.6919v1).
- [GLT10] G. Giacomin, H. Lacoin and F. L. Toninelli. Hierarchical pinning
  models, quadratic maps and quenched disorder. *Probab. Theory Related
  Fields* **147** (2010), 185–216.
  [doi:10.1007/s00440-009-0205-y](https://doi.org/10.1007/s00440-009-0205-y).
- [Harris60] T. E. Harris. A lower bound for the critical probability in a
  certain percolation process. *Proc. Cambridge Philos. Soc.* **56** (1960),
  13–20.
  [doi:10.1017/S0305004100034241](https://doi.org/10.1017/S0305004100034241).
- [HS18] Y. Hu and Z. Shi. The free energy in the Derrida–Retaux recursive
  model. *J. Stat. Phys.* **172** (2018), 718–741.
  [doi:10.1007/s10955-018-2066-1](https://doi.org/10.1007/s10955-018-2066-1).
- [LT09] H. Lacoin and F. L. Toninelli. A smoothing inequality for
  hierarchical pinning models. In A. Boutet de Monvel and A. Bovier (eds.),
  *Spin Glasses: Statics and Dynamics*, Progress in Probability **62**,
  Birkhäuser, Basel, 2009, pp. 271–278.
  [doi:10.1007/978-3-7643-9891-0_12](https://doi.org/10.1007/978-3-7643-9891-0_12).
  Author version dated 16 May 2008.
- [LPP95] R. Lyons, R. Pemantle and Y. Peres. Conceptual proofs of
  $L\log L$ criteria for mean behavior of branching processes. *Ann. Probab.*
  **23** (1995), 1125–1138.
  [doi:10.1214/aop/1176988176](https://doi.org/10.1214/aop/1176988176).
- [PL08] E. Phragmén and E. Lindelöf. Sur une extension d'un principe
  classique de l'analyse et sur quelques propriétés des fonctions monogènes
  dans le voisinage d'un point singulier. *Acta Math.* **31** (1908),
  381–406. [doi:10.1007/BF02415450](https://doi.org/10.1007/BF02415450).
- [TC01] L.-H. Tang and H. Chaté. Rare-event induced binding transition of
  heteropolymers. *Phys. Rev. Lett.* **86** (2001), 830–833.
  [doi:10.1103/PhysRevLett.86.830](https://doi.org/10.1103/PhysRevLett.86.830).
