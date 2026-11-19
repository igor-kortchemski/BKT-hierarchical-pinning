module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Scaling
public import DiamondPinning.Model.Profile
public import DiamondPinning.Proofs.OneSidedProof
public import DiamondPinning.Proofs.ProductAssembly
public import DiamondPinning.Proofs.ResponseAssembly
public import DiamondPinning.Proofs.ScalingCalculus4
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Exact critical asymptotics and the second formula for `γ`

This module evaluates the moments of the critical entrance profile, upgrades
subsequential scaling limits to full limits, and derives the four asymptotics
in `eq:exact-critical` (`source/profile.tex` lines 13–18 and 162–170). It then
combines the product asymptotic with the response residue to prove the second
identity in `eq:gamma` (`source/bkt_diamond_simplified.tex` lines 106–109).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

private theorem profileMeasure_moment_formula (t : ℝ) (ht : 0 < t) (k : ℕ) :
    measureMoment (profileMeasure 0 t) k =
      (2 / t) ^ 2 * (1 / (2 / t)) ^ (k + 1) * (k.factorial : ℝ) := by
  let b : ℝ := 2 / t
  have hb : 0 < b := by dsimp [b]; positivity
  have hA : profileA 0 t = 4 / t ^ 2 := by
    simp [profileA, profileU]
  have hB0 : profileB 0 t = 2 / t := by
    have hU : profileU 0 = fun x : ℝ => x := by
      funext x
      simp [profileU]
    simp [profileB, hU]
  have hdens (x : ℝ) : profileDensity 0 t x = b ^ 2 * Real.exp (-(b * x)) := by
    simp [profileDensity, hA, hB0, b]
    ring
  have hnonneg (x : ℝ) : 0 ≤ profileDensity 0 t x := by
    rw [hdens]
    positivity
  have htop : ∀ᵐ x ∂volume.restrict (Set.Ici 0),
      ENNReal.ofReal (profileDensity 0 t x) < ⊤ := by
    filter_upwards with x
    simp
  have hmeas : Measurable (fun x => ENNReal.ofReal (profileDensity 0 t x)) := by
    have hfun : (fun x => ENNReal.ofReal (profileDensity 0 t x)) =
        (fun x => ENNReal.ofReal (b ^ 2 * Real.exp (-(b * x)))) := by
      funext x
      rw [hdens]
    rw [hfun]
    fun_prop
  rw [measureMoment, profileMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul hmeas htop]
  simp_rw [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, hdens]
  change (∫ x in Set.Ici 0, b ^ 2 * Real.exp (-(b * x)) * x ^ k ∂volume) = _
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := b) (by positivity) hb
  calc
    (∫ x in Set.Ioi 0, b ^ 2 * Real.exp (-(b * x)) * x ^ k ∂volume) =
        b ^ 2 * (∫ x in Set.Ioi 0, x ^ k * Real.exp (-(b * x)) ∂volume) := by
      calc
        _ = ∫ x in Set.Ioi 0, b ^ 2 * (x ^ k * Real.exp (-(b * x))) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          ring
        _ = _ := by rw [integral_const_mul]
    _ = b ^ 2 * ((1 / b) ^ (k + 1) * (k.factorial : ℝ)) := by
      congr 1
      calc
        (∫ x in Set.Ioi 0, x ^ k * Real.exp (-(b * x)) ∂volume) =
            ∫ x in Set.Ioi 0, x ^ ((k : ℝ) + 1 - 1) * Real.exp (-(b * x)) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          rw [show (k : ℝ) + 1 - 1 = (k : ℝ) by ring]
          simp only [Real.rpow_natCast]
        _ = (1 / b) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := hgamma
        _ = (1 / b) ^ (k + 1) * (k.factorial : ℝ) := by
          have hG : Real.Gamma ((k + 1 : ℕ) : ℝ) = (k.factorial : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one] using
              (Real.Gamma_nat_eq_factorial k)
          rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_cast,
            Real.rpow_natCast, hG]
  dsimp [b]
  ring

private theorem profileMeasure_mass (t : ℝ) (ht : 0 < t) :
    measureMoment (profileMeasure 0 t) 0 = 2 / t := by
  rw [profileMeasure_moment_formula t ht 0]
  norm_num [Nat.factorial]
  field_simp [ht.ne']

private theorem profileMeasure_second (t : ℝ) (ht : 0 < t) :
    measureMoment (profileMeasure 0 t) 2 = t := by
  rw [profileMeasure_moment_formula t ht 2]
  norm_num [Nat.factorial]
  field_simp [ht.ne']

private theorem profileMeasure_third (t : ℝ) (ht : 0 < t) :
    measureMoment (profileMeasure 0 t) 3 = 3 / 2 * t ^ 2 := by
  rw [profileMeasure_moment_formula t ht 3]
  norm_num [Nat.factorial]
  field_simp [ht.ne']
  ring

private theorem scaledMass_eq_transformAt_zero {μ : Measure ℝ} {B N t : ℝ} :
    scaledMass μ B 0 N t =
      transformAt μ B (criticalPoint μ B) N ⌊N * t⌋₊ 0 := by
  simp [scaledMass, transformAt, scalingField, weightExponent, tiltedMass, realMoment]

private theorem scaledMass_measurable (μ : Measure ℝ) (B N : ℝ) :
    Measurable (fun t : ℝ => scaledMass μ B 0 N t) := by
  unfold scaledMass
  fun_prop

private theorem scaledMass_eventually_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {B A U D : ℝ} {n₀ : ℕ} (hA : 0 < A) (hD : 0 ≤ D)
    (hMass : ∀ n : ℕ, n₀ ≤ n →
      |tiltedMass μ B (criticalPoint μ B) n - 1| ≤ D / (n : ℝ)) :
    ∀ᶠ N : ℝ in atTop, ∀ t ∈ Set.Icc A U,
      |scaledMass μ B 0 N t| ≤ 2 * D / A := by
  filter_upwards [eventually_ge_atTop (((n₀ : ℝ) + 2) / A)] with N hN
  have hNpos : 0 < N := by
    have : 0 < ((n₀ : ℝ) + 2) / A := by positivity
    linarith
  have hNA : (n₀ : ℝ) + 2 ≤ N * A := by
    exact (div_le_iff₀ hA).1 hN
  intro t ht
  let m : ℕ := ⌊N * t⌋₊
  have hNt : N * A ≤ N * t := mul_le_mul_of_nonneg_left ht.1 hNpos.le
  have hcastm : (n₀ : ℝ) ≤ (m : ℝ) := by
    have hn : n₀ ≤ ⌊N * t⌋₊ := Nat.le_floor (show (n₀ : ℝ) ≤ N * t by
      linarith)
    exact_mod_cast hn
  have hmn : n₀ ≤ m := by exact_mod_cast hcastm
  have hmpos : 0 < (m : ℝ) := by
    have hNAtwo : 2 ≤ N * A := by linarith
    have hfloor : N * t < (m : ℝ) + 1 := by
      dsimp [m]
      exact Nat.lt_floor_add_one (N * t)
    have hhalf : N * A / 2 ≤ (m : ℝ) := by linarith
    have : 0 < N * A / 2 := by positivity
    linarith
  have hfloorlower : N * A / 2 ≤ (m : ℝ) := by
    have hfloor : N * t < (m : ℝ) + 1 := by
      dsimp [m]
      exact Nat.lt_floor_add_one (N * t)
    linarith
  have hratio : N ≤ 2 * (m : ℝ) / A := by
    apply (le_div_iff₀ hA).2
    nlinarith
  have hmass := hMass m hmn
  have hscaled : |scaledMass μ B 0 N t| =
      N * |tiltedMass μ B (criticalPoint μ B) m - 1| := by
    rw [scaledMass, show ⌊N * t⌋₊ = m from rfl, abs_mul, abs_of_pos hNpos]
    congr 1
    simp [scalingField]
  rw [hscaled]
  calc
    N * |tiltedMass μ B (criticalPoint μ B) m - 1| ≤ N * (D / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass hNpos.le
    _ ≤ (2 * (m : ℝ) / A) * (D / (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg hD hmpos.le)
    _ = 2 * D / A := by field_simp [ne_of_gt hA, ne_of_gt hmpos]

private theorem tendsto_of_subseq_tendsto {f : ℕ → ℝ} {y : ℝ}
    (hsub : ∀ m : ℕ → ℕ, Tendsto m atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun j => f (m (φ j))) atTop (𝓝 y)) :
    Tendsto f atTop (𝓝 y) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n : ℕ in atTop, ε ≤ dist (f n) y := by
    change ¬ ∀ᶠ n : ℕ in atTop, ¬ (ε ≤ dist (f n) y)
    simpa [Filter.eventually_atTop, not_le] using hnot
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, hψ, hconv⟩ := hsub φ hφ.tendsto_atTop
  have hev := (Metric.tendsto_atTop.1 hconv) ε hε
  obtain ⟨J, hJ⟩ := hev
  have hbadJ := hbad (ψ J)
  have hgoodJ := hJ J le_rfl
  exact (not_lt_of_ge hbadJ) hgoodJ

private theorem entrance_profile_zero_moments {T Tstar α C : ℝ}
    (hTle : Tstar ≤ T)
    (E : EntranceData T 0 α C)
    (hprofile : ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure 0 t) :
    ∀ᵐ t, t ∈ Set.Ioo 0 Tstar →
      E.S t = 2 / t ∧ E.K t = t ∧ E.P t = 3 / 2 * t ^ 2 := by
  filter_upwards [E.representation, hprofile] with t hrep hprof
  intro ht
  have htT : t ∈ Set.Ioc 0 T := ⟨ht.1, le_trans ht.2.le hTle⟩
  rcases hrep htT with ⟨_, _, _, _, hS, _, hK, hP, _⟩
  have hν := hprof ht
  rw [hν, profileMeasure_mass t ht.1] at hS
  rw [hν, profileMeasure_second t ht.1] at hK
  rw [hν, profileMeasure_third t ht.1] at hP
  exact ⟨hS.symm, hK.symm, hP.symm⟩

private theorem exact_subsequence_limits {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n)
      (criticalPoint μ B) / tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hCompact : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ lam T : ℝ, 0 ≤ lam → 0 < T →
      lam * T ^ 2 ≤ η₀ → ∃ C : ℝ, 0 < C ∧ ∀ Nseq : ℕ → ℝ,
        Tendsto Nseq atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            (∀ r : ℝ, 0 < r → r < T →
              Tendsto (fun j => timeIntegral
                (fun t => |scaledMass μ B lam (Nseq (φ j)) t - E.S t|) r T)
                atTop (𝓝 0)) ∧
            (∀ r : ℝ, 0 < r → TendstoUniformlyOn
              (fun j t => scaledDrift μ B lam (Nseq (φ j)) t) E.d atTop
              (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r → TendstoUniformlyOn
              (fun j t => scaledSecond μ B lam (Nseq (φ j)) t) E.K atTop
              (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r → TendstoUniformlyOn
              (fun j t => scaledThird μ B lam (Nseq (φ j)) t) E.P atTop
              (Set.Icc r T)) ∧
            (∀ r M : ℝ, 0 < r → TendstoUniformlyOn
              (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Nseq (φ j)) p.1 p.2)
              (fun p => E.H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)) ∧
            (∀ᵐ t, t ∈ Set.Ioc 0 T →
              WeakConvergence (fun j => scalingMeasure μ B lam (Nseq (φ j)) t)
                atTop (E.ν t)))
    (hProfile : ∀ γ : ℝ, γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃) →
      ∀ lam T C : ℝ, 0 ≤ lam → 0 < T → 0 < C →
        ∃ Tstar : ℝ, 0 < Tstar ∧ Tstar ≤ T ∧
          ∀ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure (γ * lam) t)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun j => (m (ψ j) : ℝ) *
        (tiltedMass μ B (criticalPoint μ B) (m (ψ j)) - 1)) atTop (𝓝 2) ∧
      Tendsto (fun j => tiltedLogMoment μ B (criticalPoint μ B) 2 (m (ψ j)) /
        (Real.log B ^ 2 * (m (ψ j) : ℝ))) atTop (𝓝 1) ∧
      Tendsto (fun j => tiltedLogMoment μ B (criticalPoint μ B) 3 (m (ψ j)) /
        (Real.log B ^ 3 * (m (ψ j) : ℝ) ^ 2)) atTop (𝓝 (3 / 2)) := by
  obtain ⟨_, _, _, _, _, _, hMassTheta, _, _, _⟩ :=
    criticalProduct_aux hpos hmean hB hshift
  obtain ⟨D₀, hD₀⟩ := isBigO_iff.1 hMassTheta.isBigO
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hD₀D : D₀ ≤ D := le_max_left _ _
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hD₀.and (eventually_ge_atTop (1 : ℕ)))
  have hMassBound : ∀ n : ℕ, n₀ ≤ n →
      |tiltedMass μ B (criticalPoint μ B) n - 1| ≤ D / (n : ℝ) := by
    intro n hn
    obtain ⟨hbigO, hnpos⟩ := hn₀ n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hnorm : ‖((n : ℝ)⁻¹)‖ = 1 / (n : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnR)]
      simp
    have hfirst : |tiltedMass μ B (criticalPoint μ B) n - 1| ≤
        D₀ * ‖((n : ℝ)⁻¹)‖ := by simpa [Real.norm_eq_abs] using hbigO
    calc
      _ ≤ D₀ * ‖((n : ℝ)⁻¹)‖ := hfirst
      _ ≤ D * ‖((n : ℝ)⁻¹)‖ := mul_le_mul_of_nonneg_right hD₀D (norm_nonneg _)
      _ = D / (n : ℝ) := by rw [hnorm]; simp [div_eq_mul_inv]
  rcases hCompact with ⟨η₀, hη₀, hcomp⟩
  obtain ⟨C, hC, hcompSeq⟩ := hcomp 0 1 (by norm_num) (by norm_num)
    (by simpa using hη₀.le)
  obtain ⟨Tstar, hTstar, hTstarLe, hProfileAll⟩ :=
    hProfile (3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) rfl 0 1 C
      (by norm_num) (by norm_num) hC
  let A : ℝ := Tstar / 4
  let U : ℝ := 3 * Tstar / 4
  let t₀ : ℝ := Tstar / 2
  let δ : ℝ := Tstar / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hTstarOne : Tstar ≤ 1 := hTstarLe
  have hUle : U ≤ 1 := by dsimp [U]; linarith
  have hUstar : U < Tstar := by dsimp [U]; linarith
  have hAU : A < U := by dsimp [A, U]; linarith
  have hAone : A < 1 := lt_of_lt_of_le (by dsimp [A]; linarith) hTstarOne
  have ht₀ : 0 < t₀ := by dsimp [t₀]; positivity
  have ht₀A : A < t₀ := by dsimp [A, t₀]; linarith
  have ht₀U : t₀ < U := by dsimp [t₀, U]; linarith
  have ht₀mem : t₀ ∈ Set.Icc A 1 := ⟨ht₀A.le, le_trans ht₀U.le hUle⟩
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hAδ : A + δ = U := by dsimp [A, δ, U]; ring
  let Nseq : ℕ → ℝ := fun j => (m j : ℝ) / t₀
  have hNseq : Tendsto Nseq atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro x
    have hmR : Tendsto (fun j => (m j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hm
    have hev := (Filter.tendsto_atTop.1 hmR) (x * t₀)
    filter_upwards [hev] with j hj
    exact (le_div_iff₀ ht₀).2 (by nlinarith)
  obtain ⟨φ, hφ, E, hL1, hDrift, hSecond, hThird, _, _⟩ :=
    hcompSeq Nseq hNseq
  have hprofE : ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure 0 t := by
    simpa [mul_zero] using hProfileAll E
  have hMom := entrance_profile_zero_moments hTstarLe E hprofE
  have hKae : (fun t => E.K t) =ᵐ[volume.restrict (Set.Icc A U)] (fun t => t) := by
    change ∀ᵐ t ∂(volume.restrict (Set.Icc A U)), E.K t = t
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hMom] with t hMt
    intro ht
    have htp : t ∈ Set.Ioo 0 Tstar :=
      ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hUstar⟩
    exact (hMt htp).2.1
  have hPae : (fun t => E.P t) =ᵐ[volume.restrict (Set.Icc A U)]
      (fun t => 3 / 2 * t ^ 2) := by
    change ∀ᵐ t ∂(volume.restrict (Set.Icc A U)), E.P t = 3 / 2 * t ^ 2
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hMom] with t hMt
    intro ht
    have htp : t ∈ Set.Ioo 0 Tstar :=
      ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hUstar⟩
    exact (hMt htp).2.2
  rcases E.lipschitz A hA with ⟨L, _, hKlip, hPlip⟩
  have hKcont : ContinuousOn E.K (Set.Icc A U) :=
    hKlip.continuousOn.mono (Set.Icc_subset_Icc_right hUle)
  have hPcont : ContinuousOn E.P (Set.Icc A U) :=
    hPlip.continuousOn.mono (Set.Icc_subset_Icc_right hUle)
  have hKEq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hAU) hKae hKcont
    continuousOn_id
  have hPEq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hAU) hPae hPcont (by fun_prop)
  have ht₀AU : t₀ ∈ Set.Icc A U := ⟨ht₀A.le, ht₀U.le⟩
  have hKEval : E.K t₀ = t₀ := hKEq ht₀AU
  have hPEval : E.P t₀ = 3 / 2 * t₀ ^ 2 := hPEq ⟨ht₀A.le, ht₀U.le⟩
  have hSecondPoint : Tendsto
      (fun j => scaledSecond μ B 0 (Nseq (φ j)) t₀) atTop (𝓝 (E.K t₀)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hU := (Metric.tendstoUniformlyOn_iff.1 (hSecond A hA)) ε hε
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hU
    refine ⟨J, ?_⟩
    intro j hj
    simpa [dist_comm] using hJ j hj t₀ ht₀mem
  have hThirdPoint : Tendsto
      (fun j => scaledThird μ B 0 (Nseq (φ j)) t₀) atTop (𝓝 (E.P t₀)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hU := (Metric.tendstoUniformlyOn_iff.1 (hThird A hA)) ε hε
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hU
    refine ⟨J, ?_⟩
    intro j hj
    simpa [dist_comm] using hJ j hj t₀ ht₀mem
  have hMassEventually := scaledMass_eventually_bound hA hD hMassBound (U := 1)
  obtain ⟨Cb, hCb⟩ := transform_bounded_aux hpos hmean hB
  obtain ⟨N₁, CM, ε, hε, hTransform⟩ :=
    hCb A δ 0 (2 * D / A) hA hδpos (by norm_num)
  have hGoodSet : ∀ᶠ N : ℝ in atTop,
      N₁ ≤ N ∧ ∀ t ∈ Set.Icc A 1,
        |scaledMass μ B 0 N t| ≤ 2 * D / A :=
    (eventually_ge_atTop N₁).and hMassEventually
  have hNφ : Tendsto (fun j => Nseq (φ j)) atTop atTop := hNseq.comp hφ.tendsto_atTop
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (hNφ.eventually hGoodSet)
  let Ntail : ℕ → ℝ := fun j => Nseq (φ (j + J))
  have hGoodTail : ∀ j, N₁ ≤ Ntail j ∧
      ∀ t ∈ Set.Icc A 1, |scaledMass μ B 0 (Ntail j) t| ≤ 2 * D / A := by
    intro j
    exact hJ (j + J) (by omega)
  have hNtail : Tendsto Ntail atTop atTop := by
    exact hNφ.comp (tendsto_add_atTop_nat J)
  let f : ℕ → ℝ → ℝ := fun j t => scaledMass μ B 0 (Ntail j) t
  let g : ℝ → ℝ := fun t => 2 / t
  have hbound : ∃ M : ℝ, ∀ j t, t ∈ Set.Icc A U → |f j t| ≤ M := by
    refine ⟨2 * D / A, ?_⟩
    intro j t ht
    exact hGoodTail j |>.2 t ⟨ht.1, ht.2.trans hUle⟩
  have hmeas : ∀ j, AEStronglyMeasurable (f j)
      (volume.restrict (Set.Icc A U)) := by
    intro j
    exact (scaledMass_measurable μ B (Ntail j)).aestronglyMeasurable
  have hone : ∀ j r t, r ∈ Set.Icc A U → t ∈ Set.Icc A U → r ≤ t →
      f j t - f j r ≤ CM * (t - r) + ε (Ntail j) := by
    intro j r t hr ht hrt
    have hTf : ∀ x ∈ Set.Icc A (A + δ),
        |transformAt μ B (criticalPoint μ B) (Ntail j) ⌊Ntail j * x⌋₊ 0| ≤ 2 * D / A := by
      intro x hx
      rw [← scaledMass_eq_transformAt_zero]
      rw [hAδ] at hx
      exact hGoodTail j |>.2 x ⟨hx.1, hx.2.trans hUle⟩
    obtain ⟨_, _, _, hvar⟩ :=
      hTransform (Ntail j) (hGoodTail j).1 (criticalPoint μ B) hTf
    have hv := hvar r t hr.1 hrt (by simpa [hAδ] using ht.2)
    rw [← scaledMass_eq_transformAt_zero, ← scaledMass_eq_transformAt_zero] at hv
    simpa [f] using hv
  have hεtail : Tendsto (fun j => ε (Ntail j)) atTop (𝓝 0) := hε.comp hNtail
  have hL1orig := hL1 A hA hAone
  have hL1tail : Tendsto
      (fun j => ∫ x in A..1, |f j x - E.S x|) atTop (𝓝 0) := by
    have hshift := hL1orig.comp (tendsto_add_atTop_nat J)
    simpa [timeIntegral, Function.comp_def, f, Ntail] using hshift
  have hSae : ∀ᵐ x ∂volume, x ∈ Set.Ioo 0 Tstar → E.S x = 2 / x := by
    filter_upwards [hMom] with x hx
    intro hxt
    exact (hx hxt).1
  have hBV := E.bv_S A 1 ⟨hA, le_of_lt hAone⟩ ⟨by norm_num, le_rfl⟩
  have hEint : IntervalIntegrable E.S volume A 1 :=
    hBV.intervalIntegrable (by
      rw [Set.uIcc_of_le (le_of_lt hAone)]
      intro x hx
      exact ⟨⟨lt_of_lt_of_le hA hx.1, hx.2⟩, hx⟩)
  have hmeasOne (j : ℕ) : AEStronglyMeasurable (f j)
      (volume.restrict (Set.Icc A 1)) :=
    (scaledMass_measurable μ B (Ntail j)).aestronglyMeasurable
  have hMnonneg : 0 ≤ 2 * D / A := div_nonneg (by positivity) hA.le
  have hfintOne (j : ℕ) : IntervalIntegrable (f j) volume A 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hAone)]
    refine (integrable_const (2 * D / A)).mono (hmeasOne j) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hD, abs_of_pos hA, f] using
      (hGoodTail j).2 x hx
  have hgcont : ContinuousOn g (Set.Icc A U) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hA ht.1)
  have hgint : IntervalIntegrable g volume A U := hgcont.intervalIntegrable_of_Icc hAU.le
  have hfint (j : ℕ) : IntervalIntegrable (f j) volume A U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAU.le]
    refine (integrable_const (2 * D / A)).mono (hmeas j) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hD, abs_of_pos hA, f] using
      (hGoodTail j).2 x ⟨hx.1, hx.2.trans hUle⟩
  have houterInt (j : ℕ) :
      IntervalIntegrable (fun x => |f j x - E.S x|) volume A 1 :=
    ((hfintOne j).sub hEint).abs
  have hinnerEq (j : ℕ) :
      ∫ x in A..U, |f j x - g x| = ∫ x in A..U, |f j x - E.S x| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hSae] with x hx
    intro hxIU
    have hxIoc : x ∈ Set.Ioc A U := by
      simpa [Set.uIoc_of_le hAU.le] using hxIU
    have hxprof : x ∈ Set.Ioo 0 Tstar :=
      ⟨hA.trans hxIoc.1, lt_of_le_of_lt hxIoc.2 hUstar⟩
    rw [hx hxprof]
  have hinnerBound (j : ℕ) :
      ∫ x in A..U, |f j x - g x| ≤ ∫ x in A..1, |f j x - E.S x| := by
    rw [hinnerEq]
    exact intervalIntegral.integral_mono_interval le_rfl hAU.le hUle
      (Filter.Eventually.of_forall (fun x => abs_nonneg (f j x - E.S x)))
      (houterInt j)
  have hL1inner : Tendsto
      (fun j => ∫ x in A..U, |f j x - g x|) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro η hη
    have hOuter := (Metric.tendsto_atTop.1 hL1tail) η hη
    obtain ⟨N, hN⟩ := hOuter
    refine ⟨N, ?_⟩
    intro j hj
    have hj := hN j hj
    have hnonneg : 0 ≤ ∫ x in A..U, |f j x - g x| :=
      intervalIntegral.integral_nonneg_of_ae_restrict hAU.le
        (Filter.Eventually.of_forall (fun x => abs_nonneg (f j x - g x)))
    have hOuter' : ∫ x in A..1, |f j x - E.S x| < η := by
      simpa [Real.dist_eq, abs_of_nonneg (intervalIntegral.integral_nonneg_of_ae_restrict
        (le_of_lt hAone) (Filter.Eventually.of_forall (fun x => abs_nonneg _)))] using hj
    have hinnerlt := (hinnerBound j).trans_lt hOuter'
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hinnerlt
  have hUniform := one_sided_compactness_aux A U CM f g (fun j => ε (Ntail j)) hAU
    hbound hmeas hone hεtail hgcont hL1inner
  have hsingle : TendstoUniformlyOn f g atTop {t₀} :=
    hUniform {t₀} (isCompact_singleton) (by
      intro t ht
      have : t = t₀ := by simpa using ht
      subst t
      exact ⟨ht₀A, ht₀U⟩)
  have hMassPoint : Tendsto (fun j => f j t₀) atTop (𝓝 (2 / t₀)) := by
    apply Metric.tendsto_atTop.2
    intro η hη
    have hU := (Metric.tendstoUniformlyOn_iff.1 hsingle) η hη
    obtain ⟨J', hJ'⟩ := Filter.eventually_atTop.1 hU
    refine ⟨J', ?_⟩
    intro j hj
    simpa [dist_comm] using hJ' j hj t₀ (by simp)
  have hSecondTail : Tendsto (fun j => scaledSecond μ B 0 (Ntail j) t₀)
      atTop (𝓝 t₀) := by
    have h := hSecondPoint.comp (tendsto_add_atTop_nat J)
    simpa [Function.comp_def, Ntail, hKEval] using h
  have hThirdTail : Tendsto (fun j => scaledThird μ B 0 (Ntail j) t₀)
      atTop (𝓝 (3 / 2 * t₀ ^ 2)) := by
    have h := hThirdPoint.comp (tendsto_add_atTop_nat J)
    simpa [Function.comp_def, Ntail, hPEval] using h
  let mTail : ℕ → ℕ := fun j => m (φ (j + J))
  have hfloor (j : ℕ) : ⌊Ntail j * t₀⌋₊ = mTail j := by
    simp [Ntail, mTail, Nseq, ne_of_gt ht₀]
  have hmTailAt : Tendsto mTail atTop atTop := by
    dsimp [mTail]
    exact hm.comp (hφ.tendsto_atTop.comp (tendsto_add_atTop_nat J))
  have hmTailPos : ∀ᶠ j : ℕ in atTop, 0 < mTail j :=
    hmTailAt.eventually (eventually_gt_atTop 0)
  have ha : 0 < Real.log B := Real.log_pos (by linarith)
  let secondTarget := fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n /
    (Real.log B ^ 2 * (n : ℝ))
  have hSecondRel :
      (fun j => secondTarget (mTail j)) =ᶠ[atTop]
        (fun j => scaledSecond μ B 0 (Ntail j) t₀ / t₀) := by
    filter_upwards [hmTailPos] with j hj
    have hnR : (mTail j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
    simp only [secondTarget, scaledSecond, hfloor, scalingField, add_zero, zero_div]
    dsimp [Ntail, Nseq, mTail]
    field_simp [hnR, ha.ne', ne_of_gt ht₀]
  have hSecondLimit : Tendsto (fun j => secondTarget (mTail j)) atTop (𝓝 1) := by
    apply Filter.Tendsto.congr' hSecondRel.symm
    simpa [ne_of_gt ht₀] using hSecondTail.div_const t₀
  let thirdTarget := fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
    (Real.log B ^ 3 * (n : ℝ) ^ 2)
  have hThirdRel :
      (fun j => thirdTarget (mTail j)) =ᶠ[atTop]
        (fun j => scaledThird μ B 0 (Ntail j) t₀ / t₀ ^ 2) := by
    filter_upwards [hmTailPos] with j hj
    have hnR : (mTail j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
    simp only [thirdTarget, scaledThird, hfloor, scalingField, add_zero, zero_div]
    dsimp [Ntail, Nseq, mTail]
    field_simp [hnR, ha.ne', ne_of_gt ht₀]
  have hThirdLimit : Tendsto (fun j => thirdTarget (mTail j)) atTop (𝓝 (3 / 2)) := by
    apply Filter.Tendsto.congr' hThirdRel.symm
    have hdiv := hThirdTail.div_const (t₀ ^ 2)
    have hval : (3 / 2 * t₀ ^ 2) / t₀ ^ 2 = (3 / 2 : ℝ) := by
      field_simp [ne_of_gt ht₀]
    rw [hval] at hdiv
    exact hdiv
  have hMassRel (j : ℕ) :
      (mTail j : ℝ) * (tiltedMass μ B (criticalPoint μ B) (mTail j) - 1) =
        t₀ * f j t₀ := by
    simp only [f, scaledMass, hfloor, Ntail, Nseq, mTail, scalingField, add_zero,
      zero_div]
    field_simp [ne_of_gt ht₀]
  have hMassLimit : Tendsto
      (fun j => (mTail j : ℝ) *
        (tiltedMass μ B (criticalPoint μ B) (mTail j) - 1)) atTop (𝓝 2) := by
    have hconst : Tendsto (fun _ : ℕ => t₀) atTop (𝓝 t₀) := tendsto_const_nhds
    have hmul := hconst.mul hMassPoint
    have hcongr := Filter.Tendsto.congr'
      (Filter.Eventually.of_forall (fun j => (hMassRel j).symm)) hmul
    have hval : t₀ * (2 / t₀) = 2 := by field_simp [ne_of_gt ht₀]
    rw [hval] at hcongr
    exact hcongr
  have hshiftMono : StrictMono (fun j : ℕ => j + J) := by
    intro i j hij
    exact Nat.add_lt_add_right hij J
  have hψ : StrictMono (fun j : ℕ => φ (j + J)) := hφ.comp hshiftMono
  refine ⟨fun j => φ (j + J), hψ, ?_, ?_, ?_⟩
  · simpa [mTail] using hMassLimit
  · simpa [mTail, secondTarget] using hSecondLimit
  · simpa [mTail, thirdTarget] using hThirdLimit

/-- The four critical asymptotics of `eq:exact-critical`: the rescaled mass,
second and third logarithmic moments, and tilted product converge to their
respective limits. -/
theorem exact_critical_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n)
      (criticalPoint μ B) / tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hCompact : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ lam T : ℝ, 0 ≤ lam → 0 < T →
      lam * T ^ 2 ≤ η₀ → ∃ C : ℝ, 0 < C ∧ ∀ Nseq : ℕ → ℝ,
        Tendsto Nseq atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            (∀ r : ℝ, 0 < r → r < T →
              Tendsto (fun j => timeIntegral
                (fun t => |scaledMass μ B lam (Nseq (φ j)) t - E.S t|) r T)
                atTop (𝓝 0)) ∧
            (∀ r : ℝ, 0 < r → TendstoUniformlyOn
              (fun j t => scaledDrift μ B lam (Nseq (φ j)) t) E.d atTop
              (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r → TendstoUniformlyOn
              (fun j t => scaledSecond μ B lam (Nseq (φ j)) t) E.K atTop
              (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r → TendstoUniformlyOn
              (fun j t => scaledThird μ B lam (Nseq (φ j)) t) E.P atTop
              (Set.Icc r T)) ∧
            (∀ r M : ℝ, 0 < r → TendstoUniformlyOn
              (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Nseq (φ j)) p.1 p.2)
              (fun p => E.H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)) ∧
            (∀ᵐ t, t ∈ Set.Ioc 0 T →
              WeakConvergence (fun j => scalingMeasure μ B lam (Nseq (φ j)) t)
                atTop (E.ν t)))
    (hProfile : ∀ γ : ℝ, γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃) →
      ∀ lam T C : ℝ, 0 ≤ lam → 0 < T → 0 < C →
        ∃ Tstar : ℝ, 0 < Tstar ∧ Tstar ≤ T ∧
          ∀ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure (γ * lam) t) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (tiltedMass μ B (criticalPoint μ B) n - 1)) atTop (𝓝 2) ∧
    Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n /
      (Real.log B ^ 2 * (n : ℝ))) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      (Real.log B ^ 3 * (n : ℝ) ^ 2)) atTop (𝓝 (3 / 2)) ∧
    Tendsto (fun n : ℕ => tiltedProduct μ B (criticalPoint μ B) n /
      (n : ℝ) ^ 2) atTop (𝓝 (3 * Real.log B ^ 3 / (2 * ℓ₃))) := by
  let massTarget := fun n : ℕ => (n : ℝ) *
    (tiltedMass μ B (criticalPoint μ B) n - 1)
  let secondTarget := fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n /
    (Real.log B ^ 2 * (n : ℝ))
  let thirdTarget := fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
    (Real.log B ^ 3 * (n : ℝ) ^ 2)
  have hmass : Tendsto massTarget atTop (𝓝 2) :=
    tendsto_of_subseq_tendsto (f := massTarget) (y := 2) (by
      intro m hm
      obtain ⟨ψ, hψ, hm, _, _⟩ :=
        exact_subsequence_limits hpos hmean hB hshift hℓ₃ hκ hCompact hProfile m hm
      exact ⟨ψ, hψ, hm⟩)
  have hsecond : Tendsto secondTarget atTop (𝓝 1) :=
    tendsto_of_subseq_tendsto (f := secondTarget) (y := 1) (by
      intro m hm
      obtain ⟨ψ, hψ, _, hm, _⟩ :=
        exact_subsequence_limits hpos hmean hB hshift hℓ₃ hκ hCompact hProfile m hm
      exact ⟨ψ, hψ, hm⟩)
  have hthird : Tendsto thirdTarget atTop (𝓝 (3 / 2)) :=
    tendsto_of_subseq_tendsto (f := thirdTarget) (y := 3 / 2) (by
      intro m hm
      obtain ⟨ψ, hψ, _, _, hm⟩ :=
        exact_subsequence_limits hpos hmean hB hshift hℓ₃ hκ hCompact hProfile m hm
      exact ⟨ψ, hψ, hm⟩)
  obtain ⟨_, _, _, _, hEll, _, _, _, _, _⟩ :=
    criticalProduct_aux hpos hmean hB hshift
  obtain ⟨ell, hellpos, hell⟩ := hEll
  have hellEq : ell = ℓ₃ := tendsto_nhds_unique hell hℓ₃
  have hℓpos : 0 < ℓ₃ := by rw [← hellEq]; exact hellpos
  let a : ℝ := Real.log B
  have ha : 0 < a := by dsimp [a]; exact Real.log_pos (by linarith)
  have hlogne : Real.log B ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hratio := hℓ₃
  have hquot := hthird.div hratio hℓpos.ne'
  have hprodAux : Tendsto
      (fun n : ℕ => a ^ 3 *
        (tiltedLogMoment μ B (criticalPoint μ B) 3 n /
          (a ^ 3 * (n : ℝ) ^ 2)) /
          (tiltedLogMoment μ B (criticalPoint μ B) 3 n /
            tiltedProduct μ B (criticalPoint μ B) n)) atTop
      (𝓝 (a ^ 3 * ((3 / 2) / ℓ₃))) := by
    have hconst : Tendsto (fun _ : ℕ => a ^ 3) atTop (𝓝 (a ^ 3)) := tendsto_const_nhds
    have hmul := hconst.mul hquot
    have hfun :
        (fun n : ℕ => a ^ 3 *
          (tiltedLogMoment μ B (criticalPoint μ B) 3 n /
            (a ^ 3 * (n : ℝ) ^ 2)) /
            (tiltedLogMoment μ B (criticalPoint μ B) 3 n /
              tiltedProduct μ B (criticalPoint μ B) n)) =
          (fun n => a ^ 3 * (thirdTarget n /
            (tiltedLogMoment μ B (criticalPoint μ B) 3 n /
              tiltedProduct μ B (criticalPoint μ B) n))) := by
      funext n
      simp only [thirdTarget, div_eq_mul_inv]
      ring
    rw [hfun]
    exact hmul
  have hProductPos (n : ℕ) : 0 < tiltedProduct μ B (criticalPoint μ B) n := by
    change 0 < ∏ j ∈ Finset.range n, tiltedMass μ B (criticalPoint μ B) j
    apply Finset.prod_pos
    intro j hj
    exact tiltedMass_pos_of hpos hmean hB (criticalPoint μ B) j
  have hprodEq : (fun n : ℕ => tiltedProduct μ B (criticalPoint μ B) n /
      (n : ℝ) ^ 2) =ᶠ[atTop]
      (fun n : ℕ => a ^ 3 *
        (tiltedLogMoment μ B (criticalPoint μ B) 3 n /
          (a ^ 3 * (n : ℝ) ^ 2)) /
          (tiltedLogMoment μ B (criticalPoint μ B) 3 n /
            tiltedProduct μ B (criticalPoint μ B) n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hthird.eventually_ne (by norm_num : (3 / 2 : ℝ) ≠ 0),
      hratio.eventually_ne hℓpos.ne'] with n hn hnum hden
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hprodne : tiltedProduct μ B (criticalPoint μ B) n ≠ 0 :=
      (hProductPos n).ne'
    have hJne : tiltedLogMoment μ B (criticalPoint μ B) 3 n ≠ 0 := by
      change tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        (Real.log B ^ 3 * (n : ℝ) ^ 2) ≠ 0 at hnum
      intro hJ
      apply hnum
      simp [hJ]
    dsimp [a]
    field_simp [hlogne, hnR, hprodne, hJne, hden]
  have hprod := Filter.Tendsto.congr' hprodEq.symm hprodAux
  have hprodval : a ^ 3 * ((3 / 2) / ℓ₃) = 3 * Real.log B ^ 3 / (2 * ℓ₃) := by
    dsimp [a]
    field_simp [hℓpos.ne']
  change Tendsto massTarget atTop (𝓝 2) ∧ Tendsto secondTarget atTop (𝓝 1) ∧
    Tendsto thirdTarget atTop (𝓝 (3 / 2)) ∧
    Tendsto (fun n : ℕ => tiltedProduct μ B (criticalPoint μ B) n / (n : ℝ) ^ 2)
      atTop (𝓝 (3 * Real.log B ^ 3 / (2 * ℓ₃)))
  rw [hprodval] at hprod
  exact ⟨hmass, hsecond, hthird, hprod⟩

/-- The response derivative normalized by `Real.log B * n ^ 2` converges to
`γ`, giving the second identity of `eq:gamma`. -/
theorem gamma_eq_limit_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n)
      (criticalPoint μ B) / tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃))
    (hExact :
      Tendsto (fun n : ℕ => (n : ℝ) *
        (tiltedMass μ B (criticalPoint μ B) n - 1)) atTop (𝓝 2) ∧
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n /
        (Real.log B ^ 2 * (n : ℝ))) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        (Real.log B ^ 3 * (n : ℝ) ^ 2)) atTop (𝓝 (3 / 2)) ∧
      Tendsto (fun n : ℕ => tiltedProduct μ B (criticalPoint μ B) n /
        (n : ℝ) ^ 2) atTop (𝓝 (3 * Real.log B ^ 3 / (2 * ℓ₃)))) :
    Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n)
      (criticalPoint μ B) / (Real.log B * (n : ℝ) ^ 2)) atTop (𝓝 γ) := by
  rcases hExact with ⟨_, _, _, hprod⟩
  let a : ℝ := Real.log B
  have ha : 0 < a := by
    dsimp [a]
    exact Real.log_pos (by linarith)
  have hprodpos (n : ℕ) : 0 < tiltedProduct μ B (criticalPoint μ B) n := by
    change 0 < ∏ j ∈ Finset.range n, tiltedMass μ B (criticalPoint μ B) j
    apply Finset.prod_pos
    intro j hj
    exact tiltedMass_pos_of hpos hmean hB (criticalPoint μ B) j
  have hfun :
      (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n)
        (criticalPoint μ B) / (a * (n : ℝ) ^ 2)) =
      (fun n : ℕ =>
        (deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
          tiltedProduct μ B (criticalPoint μ B) n) *
          (tiltedProduct μ B (criticalPoint μ B) n / (n : ℝ) ^ 2) / a) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hpn : tiltedProduct μ B (criticalPoint μ B) n ≠ 0 := (hprodpos n).ne'
      dsimp [a]
      field_simp [hnR, hpn, ha.ne']
  have hlim := (hκ.mul hprod).div_const a
  have hval :
      (κ * (3 * Real.log B ^ 3 / (2 * ℓ₃))) / Real.log B = γ := by
    rw [hγ]
    by_cases hℓ : ℓ₃ = 0
    · simp [hℓ]
    · field_simp [hℓ, ha.ne']
  change Tendsto
    (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n)
      (criticalPoint μ B) / (a * (n : ℝ) ^ 2)) atTop (𝓝 γ)
  rw [hfun, ← hval]
  exact hlim

end DiamondPinning
