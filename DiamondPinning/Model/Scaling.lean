module

public import DiamondPinning.Model.Moments
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The near-critical scaling objects (Section 5)

Definitions of `source/scaling.tex`, at the level of laws.

*Scaling* (lines 9–22). For a real scale `N > 0` and `λ ≥ 0`, the field is
`h_N = h_c + λ/N²` (`scalingField`) and the generation at time `t` is
`n = ⌊N t⌋` (`Nat.floor`). With `a = log B`:

* `weightExponent B N s = q_N(s) = θ - s/(aN)` (`scaling:unshifted`);
* `transformAt μ B h N n s = L_{n,N}(s) = N (G_n(q_N(s)) - 1)` at the field
  `h` (`scaling:unshifted`), and `scaledTransform μ B λ N t s = L_N(t, s)`, the
  same at `h_N` and `n = ⌊N t⌋` (line 22);
* `rescaledMeasure μ B h N n`, the positive, unnormalized measure
  `N E[(R_n^θ - 1) 1{R_n ≥ 1} δ_{log R_n/(aN)}(dx)]` at the field `h`, and
  `scalingMeasure μ B λ N t = ν_N(t, ·)`, the same at `h_N` and `n = ⌊N t⌋`
  (`scaling:measure`).

*Rescaled moments* (lines 58–72), at `h_N` and `n = ⌊N t⌋`:
`scaledMass = S_N(t) = N(A_n - 1)`, `scaledDrift = d_N(t) = H_n/a`,
`scaledSecond = 𝒦_N(t) = K_n/(a²N)`, `scaledThird = 𝒫_N(t) = J_n/(a³N²)`
(`scaling:moments`) and `scaledCompensated = ℋ_N(t, s) = s + L_{n,N}(s) - L_{n,N}(0)`
(`scaling:transform`).

*Mellin defects* (lines 124–167), at an arbitrary field `h`:
`defectKernel B q r = d_q(r) = B^q - 1 - (r + c)^q + r^q`,
`defectMean μ B h n q = D_n(q) = E d_q(r_n)` with `r_n = R_n^{(1)} R_n^{(2)}`,
`kernelExpectation μ B h n F = E F(r_n)`, `psiS s z = Ψ_s(z) = s z + z²/2`, and
`transformError μ B h N n s s₀ = e_{n,N}(s)`, defined by
`scaling:transform-difference`.

*Measures and integrals.* Every integral of the Section 5–6 statements is
taken here: `timeIntegral f r t = ∫_r^t f`, `measureMoment ν k = ∫ x^k dν`,
`compensatedLaplace ν s = ∫ (e^{-sx} - 1) dν` and its complex version,
`weightedMeasure ν s = e^{-sx} ν(dx)`, and `WeakConvergence`, the weak
convergence of finite measures (convergence of the integrals of bounded
continuous functions, with finiteness included so that the Bochner integrals
are the intended ones).

*Entrance data.* `EntranceData T λ α C` records the limit objects
`S, d, K, P, ℋ, ν_t` of `scaling:compactness` on `(0, T]` and their properties
(lines 80–117): the integral form of `scaling:odes` and `scaling:riccati`, the
measure representation `scaling:laplace`–`scaling:noatom`, the entrance bounds
`scaling:entrancebounds` with constant `C`, the expansion `scaling:taylor` and
the matching `scaling:matching` with limit `α`. It is produced by
`scaling:compactness` and consumed by `th:profile-identification`.

All quantities are Mathlib's total operations; the statements give them their
intended meaning only where the source does (`N > 0`, `n ≥ 1`, admissible
weights).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

/-! ### Scaling -/

/-- The near-critical field `h_N = h_c + λ/N²` (`scaling.tex` line 9). -/
noncomputable def scalingField (μ : Measure ℝ) (B lam N : ℝ) : ℝ :=
  criticalPoint μ B + lam / N ^ 2

/-- The exponent `q_N(s) = θ - s/(aN)`, `a = log B` (`scaling:unshifted`,
`scaling.tex` line 18). -/
noncomputable def weightExponent (B N s : ℝ) : ℝ :=
  theta B - s / (Real.log B * N)

/-- The transform `L_{n,N}(s) = N (G_n(q_N(s)) - 1)`, with
`G_n(q) = E R_n(h)^q`, at the field `h` (`scaling:unshifted`, `scaling.tex`
line 19). -/
noncomputable def transformAt (μ : Measure ℝ) (B h N : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  N * (realMoment μ B h n (weightExponent B N s) - 1)

/-- `L_N(t, s) = L_{⌊Nt⌋,N}(s)` at the field `h_N = h_c + λ/N²`
(`scaling.tex` line 22). -/
noncomputable def scaledTransform (μ : Measure ℝ) (B lam N t s : ℝ) : ℝ :=
  transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s

/-- The rescaled tilted measure at the field `h`, scale `N` and generation `n`:
`N E[(R_n^θ - 1) 1{R_n ≥ 1} δ_{log R_n/(aN)}(dx)]`, `a = log B`
(`scaling:measure`): the image under `x ↦ log x/(aN)` of the law of `R_n(h)`
restricted to `[1, ∞)` with density `N (x^θ - 1)`. Positive and not
normalized. -/
noncomputable def rescaledMeasure (μ : Measure ℝ) (B h N : ℝ) (n : ℕ) : Measure ℝ :=
  (((lawR μ B h n).restrict (Set.Ici 1)).withDensity
      fun x => ENNReal.ofReal (N * (x ^ theta B - 1))).map
    fun x => Real.log x / (Real.log B * N)

/-- `ν_N(t, ·)`, the rescaled tilted measure at `h_N = h_c + λ/N²` and
`n = ⌊N t⌋` (`scaling:measure`, `scaling.tex` lines 12–17). -/
noncomputable def scalingMeasure (μ : Measure ℝ) (B lam N t : ℝ) : Measure ℝ :=
  rescaledMeasure μ B (scalingField μ B lam N) N ⌊N * t⌋₊

/-! ### Rescaled moments (`scaling:moments`, `scaling:transform`) -/

/-- `S_N(t) = N (A_n - 1)` at `h_N`, `n = ⌊N t⌋` (`scaling:moments`). -/
noncomputable def scaledMass (μ : Measure ℝ) (B lam N t : ℝ) : ℝ :=
  N * (tiltedMass μ B (scalingField μ B lam N) ⌊N * t⌋₊ - 1)

/-- `d_N(t) = H_n / a` at `h_N`, `n = ⌊N t⌋` (`scaling:moments`). -/
noncomputable def scaledDrift (μ : Measure ℝ) (B lam N t : ℝ) : ℝ :=
  tiltedLogMoment μ B (scalingField μ B lam N) 1 ⌊N * t⌋₊ / Real.log B

/-- `𝒦_N(t) = K_n / (a² N)` at `h_N`, `n = ⌊N t⌋` (`scaling:moments`). -/
noncomputable def scaledSecond (μ : Measure ℝ) (B lam N t : ℝ) : ℝ :=
  tiltedLogMoment μ B (scalingField μ B lam N) 2 ⌊N * t⌋₊ / (Real.log B ^ 2 * N)

/-- `𝒫_N(t) = J_n / (a³ N²)` at `h_N`, `n = ⌊N t⌋` (`scaling:moments`). -/
noncomputable def scaledThird (μ : Measure ℝ) (B lam N t : ℝ) : ℝ :=
  tiltedLogMoment μ B (scalingField μ B lam N) 3 ⌊N * t⌋₊ / (Real.log B ^ 3 * N ^ 2)

/-- `ℋ_N(t, s) = s + L_{n,N}(s) - L_{n,N}(0)` at `h_N`, `n = ⌊N t⌋`
(`scaling:transform`). -/
noncomputable def scaledCompensated (μ : Measure ℝ) (B lam N t s : ℝ) : ℝ :=
  s + transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s -
    transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ 0

/-! ### Mellin defects (`scaling:mellin-calculus`) -/

/-- The defect kernel `d_q(r) = B^q - 1 - (r + c)^q + r^q`, `c = B - 1`
(`scaling.tex` line 128). -/
noncomputable def defectKernel (B q r : ℝ) : ℝ :=
  B ^ q - 1 - (r + (B - 1)) ^ q + r ^ q

/-- The defect `D_n(q) = E d_q(r_n)`, `r_n = R_n^{(1)}(h) R_n^{(2)}(h)` for two
independent copies (`scaling.tex` lines 126–128). -/
noncomputable def defectMean (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  ∫ r, defectKernel B q r ∂(productLaw μ B h n)

/-- The kernel expectation `E F(r_n)`, `r_n = R_n^{(1)}(h) R_n^{(2)}(h)`
(`scaling:kernel`). -/
noncomputable def kernelExpectation (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∫ r, F r ∂(productLaw μ B h n)

/-- `Ψ_s(z) = s z + z²/2` (`cont:onesided`). -/
noncomputable def psiS (s z : ℝ) : ℝ :=
  s * z + z ^ 2 / 2

/-- The error `e_{n,N}(s)` of `scaling:transform-difference`, at the field `h`:
`Δ(L_{n,N}(s) - L_{n,N}(s₀)) - (Ψ_s(L_{n,N}(s)) - Ψ_{s₀}(L_{n,N}(s₀)))/N`, with
`Δ x_n = x_{n+1} - x_n`. -/
noncomputable def transformError (μ : Measure ℝ) (B h N : ℝ) (n : ℕ) (s s₀ : ℝ) : ℝ :=
  (transformAt μ B h N (n + 1) s - transformAt μ B h N (n + 1) s₀) -
      (transformAt μ B h N n s - transformAt μ B h N n s₀) -
    (psiS s (transformAt μ B h N n s) - psiS s₀ (transformAt μ B h N n s₀)) / N

/-! ### Integrals, weighted measures and weak convergence -/

/-- The time integral `∫_r^t f(τ) dτ` (interval integral). -/
noncomputable def timeIntegral (f : ℝ → ℝ) (r t : ℝ) : ℝ :=
  ∫ τ in r..t, f τ

/-- The moment `∫ x^k ν(dx)` of a measure on `ℝ`. -/
noncomputable def measureMoment (ν : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, x ^ k ∂ν

/-- The compensated Laplace transform `∫ (e^{-sx} - 1) ν(dx)`
(`scaling:laplace`). -/
noncomputable def compensatedLaplace (ν : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ x, (Real.exp (-(s * x)) - 1) ∂ν

/-- The compensated Laplace transform at a complex weight,
`∫ (e^{-sx} - 1) ν(dx)`, `s ∈ ℂ` (the analytic extension of
`scaling:laplace`, `scaling.tex` lines 115–117). -/
noncomputable def complexCompensatedLaplace (ν : Measure ℝ) (s : ℂ) : ℂ :=
  ∫ x, (Complex.exp (-(s * (x : ℂ))) - 1) ∂ν

/-- The weighted measure `e^{-sx} ν(dx)`. -/
noncomputable def weightedMeasure (ν : Measure ℝ) (s : ℝ) : Measure ℝ :=
  ν.withDensity fun x => ENNReal.ofReal (Real.exp (-(s * x)))

/-- Weak convergence of finite measures on `ℝ` along a filter: the limit is
finite, the measures are eventually finite, and `∫ f dν_i → ∫ f dν` for every
bounded continuous `f`. -/
def WeakConvergence {ι : Type*} (ν : ι → Measure ℝ) (l : Filter ι) (ν' : Measure ℝ) :
    Prop :=
  IsFiniteMeasure ν' ∧ (∀ᶠ i in l, IsFiniteMeasure (ν i)) ∧
    ∀ f : ℝ →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(ν i)) l (𝓝 (∫ x, f x ∂ν'))

/-! ### Entrance data (`scaling:compactness`) -/

/-- The entrance data of `scaling:compactness` (`scaling.tex` lines 74–117) on
the time interval `(0, T]`, with entrance constant `C` and matching limit `α`
(in the theorem `α = λ κ a²/ℓ₃`): the limit objects `S, d, K, P, ℋ` and the
measures `ν_t`, with

* `S` locally of bounded variation and `d, K, P` locally Lipschitz on `(0, T]`
  (lines 75–79);
* `scaling:odes` and `scaling:riccati` (lines 83–89) in integral form between
  any two times of `(0, T]`;
* a measurable kernel `t ↦ ν_t` such that for almost every `t ∈ (0, T]`,
  `ν_t` is a finite positive measure on `[0, ∞)` with `scaling:laplace`,
  `scaling:momentslimit` and `scaling:noatom` (lines 90–101);
* `scaling:entrancebounds` (line 104) with the constant `C`: `S ≍ t⁻¹`
  (almost everywhere), `|d| ≤ C λ t²`, `K ≍ t`, `P ≍ t²` on `(0, T]`;
* `scaling:taylor` (lines 107–110) with a remainder uniform on compact sets
  of real weights `s ≥ 0`, and, after the analytic extension given by
  `scaling:laplace`, on compact subsets of `{Re s ≥ 0}` (lines 115–117);
* `scaling:matching` (lines 111–113): `d(t)/P(t) → α` as `t ↓ 0`. -/
structure EntranceData (T lam α C : ℝ) where
  /-- The limit `S` of `S_N`. -/
  S : ℝ → ℝ
  /-- The limit `d` of `d_N`. -/
  d : ℝ → ℝ
  /-- The limit `K` of `𝒦_N`. -/
  K : ℝ → ℝ
  /-- The limit `P` of `𝒫_N`. -/
  P : ℝ → ℝ
  /-- The limit `ℋ(t, s)` of `ℋ_N(t, s)`. -/
  H : ℝ → ℝ → ℝ
  /-- The limit measures `ν_t`. -/
  ν : ℝ → Measure ℝ
  /-- `S ∈ BV_loc((0, T])` (line 77). -/
  bv_S : LocallyBoundedVariationOn S (Set.Ioc 0 T)
  /-- `d, K, P` are Lipschitz on every `[r, T]`, `r > 0` (lines 78–79). -/
  lipschitz : ∀ r : ℝ, 0 < r → ∃ L : NNReal,
    LipschitzOnWith L d (Set.Icc r T) ∧ LipschitzOnWith L K (Set.Icc r T) ∧
      LipschitzOnWith L P (Set.Icc r T)
  /-- `d' = S d` (`scaling:odes`), in integral form. -/
  ode_d : ∀ r t : ℝ, 0 < r → r ≤ t → t ≤ T →
    d t - d r = timeIntegral (fun τ => S τ * d τ) r t
  /-- `K' = S K + d² - 1` (`scaling:odes`), in integral form. -/
  ode_K : ∀ r t : ℝ, 0 < r → r ≤ t → t ≤ T →
    K t - K r = timeIntegral (fun τ => S τ * K τ + d τ ^ 2 - 1) r t
  /-- `P' = S P + 3 d K` (`scaling:odes`), in integral form. -/
  ode_P : ∀ r t : ℝ, 0 < r → r ≤ t → t ≤ T →
    P t - P r = timeIntegral (fun τ => S τ * P τ + 3 * d τ * K τ) r t
  /-- `∂_t ℋ = S ℋ + ℋ²/2 - s²/2` for `s ≥ 0` (`scaling:riccati`), in integral
  form. -/
  riccati : ∀ s : ℝ, 0 ≤ s → ∀ r t : ℝ, 0 < r → r ≤ t → t ≤ T →
    H t s - H r s = timeIntegral (fun τ => S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2) r t
  /-- The kernel `t ↦ ν_t` is measurable. -/
  measurable_ν : Measurable ν
  /-- For almost every `t ∈ (0, T]`, `ν_t` is a finite positive measure on
  `[0, ∞)` with finite third moment, `ℋ(t, s) = s + ∫ (e^{-sx} - 1) ν_t(dx)` for
  `s ≥ 0` (`scaling:laplace`), `∫ (1, x, x², x³) dν_t = (S, 1 + d, K, P)(t)`
  (`scaling:momentslimit`) and `ν_t({0}) = 0` (`scaling:noatom`). -/
  representation : ∀ᵐ t, t ∈ Set.Ioc 0 T →
    IsFiniteMeasure (ν t) ∧ ν t (Set.Iio 0) = 0 ∧ Integrable (fun x : ℝ => x ^ 3) (ν t) ∧
      (∀ s : ℝ, 0 ≤ s → H t s = s + compensatedLaplace (ν t) s) ∧
      measureMoment (ν t) 0 = S t ∧ measureMoment (ν t) 1 = 1 + d t ∧
      measureMoment (ν t) 2 = K t ∧ measureMoment (ν t) 3 = P t ∧
      ν t {0} = 0
  /-- `S(t) ≍ t⁻¹` (`scaling:entrancebounds`), almost everywhere on `(0, T]`. -/
  bounds_S : ∀ᵐ t, t ∈ Set.Ioc 0 T → C⁻¹ * t⁻¹ ≤ S t ∧ S t ≤ C * t⁻¹
  /-- `|d(t)| ≤ C λ t²`, `K(t) ≍ t`, `P(t) ≍ t²` on `(0, T]`
  (`scaling:entrancebounds`). -/
  bounds : ∀ t ∈ Set.Ioc 0 T,
    |d t| ≤ C * lam * t ^ 2 ∧ C⁻¹ * t ≤ K t ∧ K t ≤ C * t ∧
      C⁻¹ * t ^ 2 ≤ P t ∧ P t ≤ C * t ^ 2
  /-- `ℋ(t, s) = -s d + s² K/2 - s³ P/6 + O(s^{7/2} t^{5/2})` (`scaling:taylor`),
  uniformly for `t ∈ (0, T]` and `s` in compact sets of `[0, ∞)`. -/
  taylor : ∀ s₁ : ℝ, ∃ C' : ℝ, ∀ t ∈ Set.Ioc 0 T, ∀ s ∈ Set.Icc 0 s₁,
    |H t s - (-(s * d t) + s ^ 2 * K t / 2 - s ^ 3 * P t / 6)| ≤
      C' * s ^ ((7 : ℝ) / 2) * t ^ ((5 : ℝ) / 2)
  /-- The analytic extension given by `scaling:laplace` (lines 115–117,
  260–263): for almost every `t ∈ (0, T]`, `s ↦ ∫ (e^{-sx} - 1) ν_t(dx)` is
  holomorphic on `{Re s > 0}` and continuous on `{Re s ≥ 0}`. -/
  laplace_extension : ∀ᵐ t, t ∈ Set.Ioc 0 T →
    DifferentiableOn ℂ (complexCompensatedLaplace (ν t)) {z : ℂ | 0 < z.re} ∧
      ContinuousOn (complexCompensatedLaplace (ν t)) {z : ℂ | 0 ≤ z.re}
  /-- `scaling:taylor` after the analytic extension (lines 115–117): the
  remainder is `O(|s|^{7/2} t^{5/2})` uniformly on compact subsets of
  `{Re s ≥ 0}`, for almost every `t ∈ (0, T]`. -/
  taylor_complex : ∀ Kc : Set ℂ, IsCompact Kc → Kc ⊆ {z : ℂ | 0 ≤ z.re} →
    ∃ C' : ℝ, ∀ᵐ t, t ∈ Set.Ioc 0 T → ∀ s ∈ Kc,
      ‖s + complexCompensatedLaplace (ν t) s -
          (-(s * (d t : ℂ)) + s ^ 2 * (K t : ℂ) / 2 - s ^ 3 * (P t : ℂ) / 6)‖ ≤
        C' * ‖s‖ ^ ((7 : ℝ) / 2) * t ^ ((5 : ℝ) / 2)
  /-- `d(t)/P(t) → α` as `t ↓ 0` (`scaling:matching`). -/
  matching : Tendsto (fun t => d t / P t) (𝓝[>] 0) (𝓝 α)

end DiamondPinning
