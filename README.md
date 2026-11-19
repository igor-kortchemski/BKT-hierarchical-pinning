# BKT asymptotics for the quenched free energy of hierarchical pinning

*Status, 19 November 2026, at commit `eafa34c`: build, axiom check and
sandboxed `lake comparator` (including `--paranoid`: NanoDa, Lean4Lean,
con-leche, con-ron and Lean's kernels) passed, checked locally on a Linux
machine (see [Verify](#verify)). No CI yet.*

Lean 4 and Mathlib formalization of *BKT asymptotics for the quenched free energy of hierarchical pinning* by Igor Kortchemski (version of
19 November 2026).
**All 24 numbered results of the paper within the declared scope are proved in
Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound` and
no `sorry` outside `Challenge.lean`.**
Links: [statements](DiamondPinning/Statements/) ·
[correspondence record](FORMALIZATION_REPORT.md) ·
[verification](FORMALIZATION_REPORT.md#verification-and-assumptions) ·
[proof outline](docs/PROOF_OUTLINE.md).

The model: for $B>2$, a disorder $W>0$ with $\mathbb E W=1$ and a field $h$,
$R_0=e^hW$ and $R_{n+1}=(R_n^{(1)}R_n^{(2)}+B-1)/B$ with independent copies;
$F(h)=\lim_n 2^{-n}\mathbb E\log R_n(h)$, $h_c=\sup\{h: F(h)=0\}$,
$\theta=\log2/\log B$, $a=\log B$, $A_n=\mathbb E R_n^\theta$,
$\Pi_n=\prod_{j<n}A_j$, $H_n=\mathbb E[R_n^\theta(\log R_n-a)]$ and
$J_n=\mathbb E[R_n^\theta(\log R_n-a)^3]$ at $h_c$. Under a strict shift
$h_c>h_a=\log(B-1)$, the paper proves the Berezinskii–Kosterlitz–Thouless law
$\log F(h_c+u)\sim -K/\sqrt u$ with an explicit constant $K$.

## Main results

| Paper | Lean declaration | Statement |
| --- | --- | --- |
| Theorem `th:bkt` | [`DiamondPinning.bkt`](DiamondPinning/Statements/Main.lean) | If $h_c>h_a$: residues $\ell_3,\kappa>0$, $\Pi_n\sim 3a^3n^2/(2\ell_3)$, $\gamma=3a^2\kappa/(2\ell_3)$, and $\sqrt u\,\log F(h_c+u)\to-\pi\log2/\sqrt\gamma$ as $u\downarrow0$ |
| Lemma `lem:basic-bounds` | [`integrable_lawR`, `freeEnergy_tendsto`, `criticalPoint_isGreatest`, …](DiamondPinning/Statements/Main.lean); [`floor_bounds`, `finiteSize_bounds`, …](DiamondPinning/Statements/FreeEnergyBounds.lean) | Integrability, existence of $F$, $h_c$ is the greatest zero of $F$, floor and finite-size bounds, $0\le F(h+u)-F(h)\le u$, $h_a\le h_c$ |
| Proposition `prop:criticalmoments` | [`criticalMoments`](DiamondPinning/Statements/Critical.lean) | If $F(h)=0$: $\mathbb E R_n^\theta\le (B-1)^\theta$, $H_n\le C_B(2/B)^n$, bounded absolute first tilted moment |
| Theorem `th:return` | [`returns_to_one`](DiamondPinning/Statements/Critical.lean) | $\liminf_n \mathbb E R_n(h_c)^\theta=1$ |
| Theorem `th:product` | [`criticalProduct`, `criticalProduct_Hsmall`](DiamondPinning/Statements/Critical.lean) | $\Pi_n\asymp n^2$, $\sum\Pi_n^{-1}<\infty$, $J_n/\Pi_n\to\ell_3>0$, $A_n-1\asymp n^{-1}$, $R_n(h_c)\to1$ in probability |
| Theorem `th:response` | [`response_transversality`](DiamondPinning/Statements/Response.lean) | $\partial_hH_n(h_c)/\Pi_n\to\kappa\in(0,\infty)$ |
| `scaling:compactness` | [`scaling_compactness`](DiamondPinning/Statements/Scaling.lean) | Subsequential scaling limits solving the limit ODEs and a Riccati equation, with measure representation and entrance data |
| Theorem `th:profile-identification` | [`profile_identification`, `exact_critical`, `gamma_eq_limit`](DiamondPinning/Statements/Profile.lean) | The limit is the explicit profile $f_v$; exact critical limits; $\gamma=\lim\partial_hH_n(h_c)/(an^2)$ |
| `cont:continuation` | [`continuation`](DiamondPinning/Statements/Scaling.lean) | Convergence of the rescaled transforms before the pole time $T_v=\pi/\sqrt v$ |
| Upper bound and escape bounds (Section 8) | [`freeEnergy_upper`, `escape_constant`, `escape_pairs`, …](DiamondPinning/Statements/Escape.lean) | Upper bound on $\log F(h_c+u)$ and lower bound on $\log F(h_c+\lambda/N^2)$ with the constant of `th:bkt`, the latter via a hard integer-valued recursion |

All 24 numbered results are matched in the
[correspondence record](FORMALIZATION_REPORT.md#result-correspondence), with
their proof routes. Material choices: the hard free energy $F_d$ takes values
in $[0,\infty]$; intermediate interfaces take the residues $\ell_3,\kappa$ as
parameters, discharged in `bkt`. Two localized statements of an earlier draft
were corrected, and the corrections are part of the cited version (see
[Corrections to the paper](FORMALIZATION_REPORT.md#corrections-to-the-paper));
neither affects `th:bkt`. Not formalized: the Gaussian example of the
introduction (it rests on a cited strict-shift theorem). Three routine
identities of Section 1 are used in proofs but not exported as standalone
declarations.

## How the proof goes

1. **Free energy and critical point** (Section 2, `lem:basic-bounds`; [`Main.lean`](DiamondPinning/Statements/Main.lean), [`FreeEnergyBounds.lean`](DiamondPinning/Statements/FreeEnergyBounds.lean)). A deterministic floor $R_n\ge b_n\uparrow1$ and two monotone finite-size bounds give $F$, its Lipschitz bound, $h_a\le h_c$ and $F(h_c)=0$.
2. **Critical moments and returns to one** (Section 2, `prop:criticalmoments`, `lem:barrier`, `th:return`; [`Critical.lean`](DiamondPinning/Statements/Critical.lean)). When $F(h)=0$, $A_n=\mathbb E R_n^\theta\le(B-1)^\theta$; at $h_c>h_a$, a continuation argument for the Mellin transforms $\mathbb E R_n^z$ rules out uniform moments above $\theta$ and gives $\liminf_n A_n=1$.
3. **The critical product** (Section 3, `th:product`; [`Critical.lean`](DiamondPinning/Statements/Critical.lean)). Recurrences for the tilted logarithmic moments, a Nash-type inequality and the return to one give $\Pi_n\asymp n^2$, $A_n-1\asymp n^{-1}$ and a positive cubic residue $\ell_3=\lim J_n/\Pi_n$.
4. **Strict transversality** (Section 4, `response:spine-identities`, `response:linear`, `th:response`, `prop:window-moments`; [`Response.lean`](DiamondPinning/Statements/Response.lean), [`Ballot.lean`](DiamondPinning/Statements/Ballot.lean)). A distinguished-leaf (spine) change of measure expresses $\partial_hH_n(h_c)/\Pi_n$ through a random walk, and a ballot estimate shows that it tends to $\kappa\in(0,\infty)$; moments of the contact count control the field in the window $h-h_c=\lambda/N^2$.
5. **The near-critical scaling limit** (Sections 5–7, `scaling:compactness`, `th:profile-identification`, `cont:continuation`; [`Scaling.lean`](DiamondPinning/Statements/Scaling.lean), [`Profile.lean`](DiamondPinning/Statements/Profile.lean)). At $h_c+\lambda/N^2$ and generation $\lfloor Nt\rfloor$, the rescaled tilted measures converge, in exponential weights, to the explicit profile $f_v(t,x)=a_v(t)e^{-b_v(t)x}$ with $v=\gamma\lambda$, selected by an entire-function argument, up to its pole time $T_v=\pi/\sqrt v$.
6. **Matching free-energy bounds** (Section 8, `cont:freeenergyupper`, `escape:comparison`, `escape:constant`; [`Escape.lean`](DiamondPinning/Statements/Escape.lean), [`Main.lean`](DiamondPinning/Statements/Main.lean)). Convergence up to $T_v$ gives $F(h_c+\lambda/N^2)\le2^{-N(T_v-o(1))}$; a comparison with the integer-valued hard recursion $Y_{j+1}=(Y_j^{(1)}+Y_j^{(2)}-1)^+$ and a pair-counting bound give the matching lower bound, and $N=\sqrt{\lambda/u}$ yields $K=\pi\log2/\sqrt\gamma$.

A longer outline, with the Lean declarations of each step and the places where the Lean proof takes another route, is in [`docs/PROOF_OUTLINE.md`](docs/PROOF_OUTLINE.md).

## Where to start

- [`Challenge.lean`](Challenge.lean): the main theorem, the companion
  statements of `lem:basic-bounds` and their definitions, importing only
  Mathlib (proofs are `sorry` there by design).
- [`DiamondPinning/Statements/Main.lean`](DiamondPinning/Statements/Main.lean):
  the same statements, proved.
- [`DiamondPinning/Model/Defs.lean`](DiamondPinning/Model/Defs.lean): the law
  of $R_n$, $F$, $h_c$ and the tilted moments.
- [`Critical.lean`](DiamondPinning/Statements/Critical.lean),
  [`Response.lean`](DiamondPinning/Statements/Response.lean),
  [`Profile.lean`](DiamondPinning/Statements/Profile.lean),
  [`Escape.lean`](DiamondPinning/Statements/Escape.lean): Sections 2–3, 4, 6
  and 8. Proofs are in `DiamondPinning/Proofs/`.

## Verify

Pins: Lean `v4.35.0` ([`lean-toolchain`](lean-toolchain)), Mathlib `v4.35.0`
at `56a005855ea17e0b0958f73ec801ae140b0a1679` ([`lake-manifest.json`](lake-manifest.json)).
Install Lean with the
[setup guide](https://leanprover-community.github.io/install/project.html),
then:

```sh
git clone https://github.com/igor-kortchemski/BKT-hierarchical-pinning
cd BKT-hierarchical-pinning
lake exe cache get
lake build
```

`lake build` builds the library, `Challenge` (expect `declaration uses 'sorry'`
warnings from it only) and `Solution`. To browse, open the folder in VS Code
with the Lean 4 extension; `#print axioms DiamondPinning.bkt` after
`import Solution` lists the axioms.

On Linux with `bwrap` installed and `nanoda_bin` on `PATH`, run
`lake comparator`. It reads [`comparator.json`](comparator.json), checks that
the six theorems of `Challenge.lean` (`bkt` and the five companion statements)
are proved in `Solution` with the same statements and definitions, with only
the three permitted axioms, and has both Lean's kernel and NanoDa check the
proofs. On 19 November 2026 it accepted this repository at commit `eafa34c`
(later commits change only documentation), and `lake comparator --paranoid`
was accepted by every bundled checker; see the
[verification record](FORMALIZATION_REPORT.md#verification-and-assumptions).

## How it was made

The formalization was produced by AI models over about thirteen hours on
18–19 November 2026. Claude Code (Claude Opus 5.5) orchestrated the work,
wrote the shared definitions and main statements, and assembled the proofs.
Proofs were written by Claude Opus 5.5, GPT‑6.2 Sol, GPT‑6 Luna and Kimi K3.1
Pro; GPT‑6.2 Astra did the preliminary research and was consulted on
interface and statement decisions. Each group of statements was reviewed by
models that did not write it (Claude Sonnet 5.5 or GPT‑6.2 Astra; also
GPT‑6.2 Sol and a blind read-back for the main results) and fixed before its
proofs were written. Every proof was then
re-audited against the paper, read-only, by another model, of a different
family from the proof's author in all but two cases (see the
[report](FORMALIZATION_REPORT.md#how-the-formalization-was-produced)). The
paper's author chose the scope. **Not claimed:** any human line-by-line review
of the Lean statements or proofs.

## License and citation

License: [Apache-2.0](LICENSE). It covers the Lean code and documentation, not
the paper. Maintainer: Igor Kortchemski. Cite the
paper for the mathematics and this repository for the formalization; citation
metadata is in [`CITATION.cff`](CITATION.cff). Questions and corrections are
welcome as issues.
