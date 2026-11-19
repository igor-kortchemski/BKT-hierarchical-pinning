module

public import DiamondPinning.Model.Moments
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Contacts
public import DiamondPinning.Model.Spine
public import DiamondPinning.Model.Window
public import DiamondPinning.Proofs.Response
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # Field response and contact moments

Section 4 of the paper (`source/response.tex`): the contact representation
and `prop:contact-moments` (lines 205–265), the field-differentiation
envelope justifying the interchange of derivative and expectation used at
lines 87–93, 176–197 and 321–337, `response:spine-identities` (lines 62–96),
`response:linear` (lines 98–132), `th:response` (lines 140–203) and
`prop:window-moments` (lines 267–342). The passage estimate `response:ballot`
is in `DiamondPinning.Statements.Ballot`.

Standing assumptions: `μ` is the law of `W` (a probability measure with
`W > 0` a.s. and `E W = 1`), `B > 2`, `c = B - 1`, `a = log B`,
`θ = log 2 / log B`. "Unless a field is specified, all quantities are
evaluated at `h_c > h_a`" (line 4): the statements at `h_c` assume
`h_c > h_a = log c`. The algebraic contact representation, the
differentiation envelope and the spine identities hold at every field and
are stated so (their proofs use no property of `h_c`).

Notation: `A_n(h) = tiltedMass μ B h n`, `Π_n(h) = tiltedProduct μ B h n`,
`H_n, K_n, J_n = tiltedLogMoment μ B h k n` for `k = 1, 2, 3`,
`𝒟_n = ∂_h A_n(h_c)` and `ℰ_n = ∂_h H_n(h_c)` (as `deriv`, whose
differentiability is concluded by the envelope statements),
`M_{k,n} = contactMoment`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

/-! ### The contact representation (lines 205–215, 221–226, 239–242) -/

/-- Contact representation (`response.tex` lines 209–213): at a leaf with
positive weight, the contact count is `C_0 = 1`. -/
theorem gibbsWeight_zero {B : ℝ} (h : ℝ) {w : Env 0} (hw : Env.Pos 0 w) (k : ℕ) :
    gibbsWeight B h 0 w k = if k = 1 then 1 else 0 := by
  exact gibbsWeight_zero_aux h hw k

/-- Contact representation, the root choice (`response.tex` lines 209–212): at
an environment `e = (e₁, e₂)` with positive leaf weights and
`S = R_n(h)(e₁) R_n(h)(e₂)`, the Gibbs measure chooses the product term with
probability `S/(S + c)`, and then the count is the sum of the independent
counts of the two subtrees; otherwise (probability `c/(S + c)`) the count is
zero. -/
theorem gibbsWeight_succ {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} {e : Env (n + 1)}
    (he : Env.Pos (n + 1) e) (k : ℕ) :
    gibbsWeight B h (n + 1) e k =
      evalR B h n e.1 * evalR B h n e.2 / (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) *
        ∑ ij ∈ Finset.antidiagonal k, gibbsWeight B h n e.1 ij.1 * gibbsWeight B h n e.2 ij.2 +
      if k = 0 then
        (B - 1) / (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) else 0 := by
  exact gibbsWeight_succ_aux hB h he k

/-- Contact representation (`response.tex` lines 209–213): for almost every
environment, the Gibbs weights form a probability law on `{0, …, 2^n}`. -/
theorem gibbsWeight_isProb {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ e ∂(envMeasure μ n),
      (∀ k, 0 ≤ gibbsWeight B h n e k) ∧ (∀ k, 2 ^ n < k → gibbsWeight B h n e k = 0) ∧
        ∑ k ∈ Finset.range (2 ^ n + 1), gibbsWeight B h n e k = 1 := by
  exact gibbsWeight_isProb_aux hpos hB h n

/-- `prop:contact-moments`, second identity of `contacts:change-field`
(`response.tex` line 225): almost surely, simultaneously for every `u`,
`R_n(h + u) = R_n(h) ⟨e^{u C_n}⟩_n`. Stated at every base field `h` (the
paper uses `h = h_c`). -/
theorem evalR_add_eq_gibbsMean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ e ∂(envMeasure μ n), ∀ u : ℝ,
      evalR B (h + u) n e = evalR B h n e * gibbsMean B h n e (fun j => Real.exp (u * j)) := by
  exact evalR_add_eq_gibbsMean_aux hpos hB h n

/-- `prop:contact-moments`, first identity of `contacts:change-field`
(`response.tex` line 225): almost surely, `Q_n = ∂_h log R_n(h) = ⟨C_n⟩_n`, the
derivative existing. Stated at every field `h` (the paper uses `h = h_c`). -/
theorem hasDerivAt_log_evalR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ e ∂(envMeasure μ n),
      HasDerivAt (fun h' => Real.log (evalR B h' n e)) (gibbsMean B h n e (fun j => (j : ℝ))) h := by
  exact hasDerivAt_log_evalR_aux hpos hB h n

/-! ### The differentiation envelope -/

/-- Field-differentiation envelope for the interchange used at
`response.tex` lines 87–93 and 321–326: at every field `h` and every `n`, the
tilted logarithmic moment `E[R_n(h)^θ (log R_n(h) - a)^k]` is differentiable
in the field, with derivative `E[R_n(h)^θ ⟨C_n⟩_n (θ Z_n^k + k Z_n^{k-1})]`.
Stated for every `k` (the paper uses `k ≤ 4`). -/
theorem hasDerivAt_tiltedLogMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (k n : ℕ) :
    HasDerivAt (fun h' => tiltedLogMoment μ B h' k n) (tiltedLogMomentDeriv μ B h k n) h := by
  exact hasDerivAt_tiltedLogMoment_aux hpos hmean hB h k n

/-- Field-differentiation envelope for `A_n(h) = E R_n(h)^θ`
(`response.tex` lines 87–88 and 244): at every field `h` and every
`n`, `∂_h A_n(h) = θ E[R_n(h)^θ ⟨C_n⟩_n] = θ M_{1,n}(h)`. -/
theorem hasDerivAt_tiltedMass {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    HasDerivAt (fun h' => tiltedMass μ B h' n) (theta B * contactMoment μ B h 1 n) h := by
  exact hasDerivAt_tiltedMass_aux hpos hmean hB h n

/-- Field-differentiation envelope, second derivative of `H_n`
(`response.tex` lines 325–330): at every field `h` and every `n`,
`∂_h H_n` is differentiable at `h`. -/
theorem differentiableAt_deriv_tiltedLogMoment_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    DifferentiableAt ℝ (deriv fun h' => tiltedLogMoment μ B h' 1 n) h := by
  exact differentiableAt_deriv_tiltedLogMoment_one_aux hpos hmean hB h n

/-- Field-differentiation envelope for the kernel term
(`response.tex` lines 184–197, where `H_{n+1} = A_n H_n + ½ E ψ(S)` is
differentiated): at every field `h` and every `n`, `h ↦ E ψ(S_n(h))` is
differentiable at `h`. -/
theorem differentiableAt_kernelMean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    DifferentiableAt ℝ (fun h' => kernelMean μ B h' n) h := by
  exact differentiableAt_kernelMean_aux hpos hmean hB h n

/-! ### The spine (lines 62–132) -/

/-- `response:spine-identities` (`response.tex` lines 62–77, `response:spine`
and `response:mixed-spine`): with `R_0^*, U_0, …, U_{n-1}` independent with the
size-biased laws `r^θ P(R_j ∈ dr)/A_j`, `S_k = ∑_{j<k} (log U_j - a)`,
`p = 1 - θ` and `d_0 = 1/θ - a > 0`,
`𝒟_n / Π_n = θ A_0 Ê w_n` and `ℰ_n / Π_n = θ A_0 Ê[w_n (log T_n + d_0)]`.
Stated at every field `h` (the paper uses `h = h_c`), for every `n ≥ 0`. -/
theorem spine_identities {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    0 < 1 / theta B - Real.log B ∧
      deriv (fun h' => tiltedMass μ B h' n) h / tiltedProduct μ B h n =
        theta B * tiltedMass μ B h 0 * spineMeanW μ B h n ∧
      deriv (fun h' => tiltedLogMoment μ B h' 1 n) h / tiltedProduct μ B h n =
        theta B * tiltedMass μ B h 0 * spineMeanWLog μ B h n := by
  exact spine_identities_aux hpos hmean hB h n

/-- `response:linear` (`response.tex` lines 98–99): at `h_c > h_a`, there is a
constant `C` with `𝒟_n ≤ C (n + 1)` for all `n`. -/
theorem response_linear {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ C : ℝ, ∀ n : ℕ,
      deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B) ≤ C * ((n : ℝ) + 1) := by
  exact response_linear_aux hpos hmean hB hshift

/-! ### Strict transversality (lines 140–203) -/

/-- `th:response` (`response.tex` lines 140–146, `response:transversality`): at
`h_c > h_a`, there is `κ ∈ (0, ∞)` with `ℰ_n / Π_n → κ`; in particular
`ℰ_n ≍ n²`. -/
theorem response_transversality {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) ∧
      (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)) =Θ[atTop]
        fun n : ℕ => (n : ℝ) ^ 2 := by
  exact response_transversality_aux hpos hmean hB hshift

/-! ### Contact moments (lines 221–265) -/

/-- `prop:contact-moments` (`response.tex` lines 227–237): at `h_c > h_a`,
there are `M, L < ∞`, chosen before `k` and `n`, with
`M_{k,n} = E[R_n^θ ⟨C_n^k⟩_n] ≤ k! M L^{k-1} (n+1)^{2k-1}` for `k ≥ 1`, `n ≥ 0`
(`contacts:all-moments`); consequently, for `n ≥ 0`, `u ≥ 0` and
`L u (n+1)² < 1`, both `E[R_n^θ ⟨e^{u C_n} - 1⟩_n]` (`contacts:exponential`)
and `E R_n(h_c + u)^θ - A_n` are at most `M u (n+1) / (1 - L u (n+1)²)`. -/
theorem contactMoments {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ M L : ℝ,
      (∀ k n : ℕ, 1 ≤ k →
        contactMoment μ B (criticalPoint μ B) k n ≤
          (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1)) ∧
      ∀ (n : ℕ) (u : ℝ), 0 ≤ u → L * u * ((n : ℝ) + 1) ^ 2 < 1 →
        contactExpMoment μ B (criticalPoint μ B) u n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) ∧
          tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) := by
  exact contactMoments_aux hpos hmean hB hshift

/-! ### Uniform field estimates (lines 267–342) -/

/-- `prop:window-moments` (`response.tex` lines 273–284): at `h_c > h_a`, there
are `η, C > 0` such that for `n ≥ 1` and `0 ≤ u (n+1)² ≤ η` (with `u ≥ 0`):
`A_n(h_c+u) = A_n + O(u(n+1))` (`response:windowA`),
`H_n(h_c+u) = H_n + u ℰ_n + O(u²(n+1)⁴)` (`response:windowH`),
`K_n(h_c+u) = K_n + O(u(n+1)³)` (`response:windowK`),
`J_n(h_c+u) = J_n + O(u(n+1)⁴)` (`response:windowJ`),
`E[R_n(h_c+u)^θ |log R_n(h_c+u) - a|^{7/2}] ≤ C (n+1)^{5/2}`
(`response:windowSevenHalves`), and `Π_n(h_c+u)/Π_n(h_c) = 1 + O(u(n+1)²)`.
The `O` constants are the single constant `C`. -/
theorem windowMoments {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, 0 ≤ u →
      u * ((n : ℝ) + 1) ^ 2 ≤ η →
      |tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n| ≤
          C * u * ((n : ℝ) + 1) ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
            tiltedLogMoment μ B (criticalPoint μ B) 1 n -
            u * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)| ≤
          C * u ^ 2 * ((n : ℝ) + 1) ^ 4 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 2 n -
            tiltedLogMoment μ B (criticalPoint μ B) 2 n| ≤ C * u * ((n : ℝ) + 1) ^ 3 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 3 n -
            tiltedLogMoment μ B (criticalPoint μ B) 3 n| ≤ C * u * ((n : ℝ) + 1) ^ 4 ∧
        absTiltedLogRpowMoment μ B (criticalPoint μ B + u) (7 / 2) n ≤
          C * ((n : ℝ) + 1) ^ ((5 : ℝ) / 2) ∧
        |tiltedProduct μ B (criticalPoint μ B + u) n /
            tiltedProduct μ B (criticalPoint μ B) n - 1| ≤ C * u * ((n : ℝ) + 1) ^ 2 := by
  exact windowMoments_aux hpos hmean hB hshift

/-- Proof of `prop:window-moments`, the derivative bounds (`response.tex` lines
323–326): at `h_c > h_a`, there are `η, C > 0` such that throughout the window
(`n ≥ 1`, `v ≥ 0`, `v (n+1)² ≤ η`), at the field `h_c + v`:
`|A_n'| ≤ C (n+1)`, `|H_n''| ≤ C (n+1)⁴`, `|K_n'| ≤ C (n+1)³` and
`|J_n'| ≤ C (n+1)⁴`. -/
theorem window_derivBounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ v : ℝ, 0 ≤ v →
      v * ((n : ℝ) + 1) ^ 2 ≤ η →
      |deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B + v)| ≤ C * ((n : ℝ) + 1) ∧
        |deriv (deriv fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4 ∧
        |deriv (fun h => tiltedLogMoment μ B h 2 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 3 ∧
        |deriv (fun h => tiltedLogMoment μ B h 3 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4 := by
  exact window_derivBounds_aux hpos hmean hB hshift

/-! ### Integrability of the integrands (`response.tex` lines 90–93 and 272)

These make the expectations defined in `DiamondPinning.Model.Contacts`,
`DiamondPinning.Model.Spine` and `DiamondPinning.Model.Window` genuine (a
Bochner integral of a non-integrable function is `0`), so that the bounds of
this file are not satisfied by junk values. -/

/-- At every field, `e ↦ R_n(h)^θ ⟨𝒞_n^k⟩` is integrable for the environment
law. -/
theorem integrable_contactMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (k n : ℕ) :
    Integrable (fun e => evalR B h n e ^ theta B * gibbsMean B h n e (fun j => (j : ℝ) ^ k))
      (envMeasure μ n) := by
  exact integrable_contactMoment_aux hpos hmean hB h k n

/-- At every field and every real `u`, `e ↦ R_n(h)^θ ⟨e^{u 𝒞_n} - 1⟩` is
integrable for the environment law. -/
theorem integrable_contactExpMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h u : ℝ) (n : ℕ) :
    Integrable (fun e => evalR B h n e ^ theta B *
      gibbsMean B h n e (fun j => Real.exp (u * j) - 1)) (envMeasure μ n) := by
  exact integrable_contactExpMoment_aux hpos hmean hB h u n

/-- The spine integrands `w_n` and `w_n (log T_n + d_0)` are integrable for
the spine law, at every field. -/
theorem integrable_spine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ × (Fin n → ℝ) => spineW B n x.1 x.2) (spineMeasure μ B h n) ∧
    Integrable (fun x : ℝ × (Fin n → ℝ) => spineW B n x.1 x.2 *
      (Real.log (spineT B n x.1 x.2) + (1 / theta B - Real.log B))) (spineMeasure μ B h n) := by
  exact integrable_spine_aux hpos hmean hB h n

/-- At every field, for every real `s ≥ 0` and every `n`,
`R_n(h)^θ |log R_n(h) - a|^s` is integrable (the `7/2` moment of
`prop:window-moments` among them). -/
theorem integrable_absTiltedLogRpow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x : ℝ => x ^ theta B * |Real.log x - Real.log B| ^ s) (lawR μ B h n) := by
  exact integrable_absTiltedLogRpow_aux hpos hmean hB h n hs

/-- At every field and for `n ≥ 1`, the kernel `ψ` is integrable for the law
of `S_n`. -/
theorem integrable_kernelPsi {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (kernelPsi B) (productLaw μ B h n) := by
  exact integrable_kernelPsi_aux hpos hmean hB h hn

/-! ### The fixed-height differentiation envelope

`response.tex` lines 87–93, 176–197 and 321–337 differentiate expectations in
the field; this envelope justifies those interchanges. For a random
polynomial `Σ_k p_k e^{k h}` with nonnegative integrable coefficients (the
contact polynomial of `R_n`, or of `S` or `S + c`), `x(h) = log Σ_k p_k e^{k h}`
has `0 ≤ x' ≤ m` and `0 ≤ x'' ≤ m²`, so the first two field derivatives of
`φ(x(h))` are dominated near `h₀` by the integrable `g`. -/

/-- The fixed-height differentiation envelope. -/
theorem field_envelope {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {m : ℕ} (p : Fin (m + 1) → Ω → ℝ) (hp : ∀ k, Integrable (p k) ν)
    (hp0 : ∀ᵐ e ∂ν, (∀ k, 0 ≤ p k e) ∧ 0 < ∑ k, p k e)
    {θ a s h₀ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hs : 0 ≤ s) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ)
    (hg : ∃ K : ℝ, ∀ i ≤ (3 : ℕ), ∀ x : ℝ,
      |iteratedDeriv i φ x| ≤ K * Real.exp (θ * x) * (1 + |x - a|) ^ s) :
    let x := fun (e : Ω) (h : ℝ) => Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h))
    let f := fun (e : Ω) (h : ℝ) => φ (x e h)
    let g := fun e => Real.exp (θ * x e h₀) * (1 + |x e h₀ - a|) ^ s
    Integrable g ν ∧
      (∃ C : ℝ, ∀ᵐ e ∂ν, ∀ h : ℝ, |h - h₀| ≤ 1 →
        |deriv (f e) h| + |iteratedDeriv 2 (f e) h| ≤ C * g e) ∧
      ∀ i < (2 : ℕ), HasDerivAt (fieldMean ν (fun e => iteratedDeriv i (f e)))
        (fieldMean ν (fun e => iteratedDeriv (i + 1) (f e)) h₀) h₀ := by
  exact field_envelope_aux ν p hp hp0 hθ hθ1 hs φ hφ hg

end DiamondPinning
