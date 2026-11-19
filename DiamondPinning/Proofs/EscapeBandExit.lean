module

public import DiamondPinning.Proofs.HardEscape
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Uniform exit from the hard-recursion band

This file proves that a large upper-band moment forces an iterate of the hard
mean to reach `3/2` within `2L` steps and gives a uniform lower bound on the
hard free energy. It covers `escape:band-exit`, `escape:amplification`,
`escape:finite-hard`, and `escape:hard-energy` in `source/escape.tex`, lines
96–154. Pair counting is supplied as an explicit hypothesis.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

/-! ### The finite lower laws -/

private noncomputable def eb_tail (α : ℝ) (L k : ℕ) : ℝ :=
  if k = 0 then 1 else if k ≤ L then α / (2 : ℝ) ^ k else 0

private noncomputable def eb_weight (α : ℝ) (L k : ℕ) : ℝ :=
  eb_tail α L k - eb_tail α L (k + 1)

private lemma eb_weight_nonneg {α : ℝ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    {L : ℕ} (hL : 1 ≤ L) (k : ℕ) : 0 ≤ eb_weight α L k := by
  by_cases hk₀ : k = 0
  · subst k
    simp [eb_weight, eb_tail, hL]
    linarith
  by_cases hkL : k < L
  · have hkn : k ≠ 0 := hk₀
    have hk1 : k + 1 ≤ L := hkL
    simp only [eb_weight, eb_tail, hk₀, hk1, ite_true, ite_false,
      show k + 1 ≠ 0 by omega, show k ≤ L by omega]
    have hp : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := by
      rw [pow_succ]
      nth_rewrite 1 [← mul_one ((2 : ℝ) ^ k)]
      gcongr
      norm_num
    have hd := div_le_div_of_nonneg_left hα₀ (by positivity : 0 < (2 : ℝ) ^ k) hp
    linarith
  by_cases hk : k = L
  · subst k
    simp [eb_weight, eb_tail, hk₀]
    positivity
  · have hkGt : L < k := by omega
    simp [eb_weight, eb_tail, hk₀, show ¬ k ≤ L by omega,
      show ¬ k + 1 ≤ L by omega]

private lemma eb_weight_of_not_mem_range {α : ℝ} {L k : ℕ}
    (hk : k ∉ Finset.range (L + 1)) : eb_weight α L k = 0 := by
  simp only [Finset.mem_range, not_lt] at hk
  simp [eb_weight, eb_tail, show k ≠ 0 by omega, show ¬ k ≤ L by omega,
    show ¬ k + 1 ≤ L by omega]

private lemma eb_sum_weight (α : ℝ) (L n : ℕ) :
    ∑ k ∈ Finset.range n, eb_weight α L k = eb_tail α L 0 - eb_tail α L n := by
  exact Finset.sum_range_sub' (eb_tail α L) n

private lemma eb_sum_weight_all (α : ℝ) (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), eb_weight α L k = 1 := by
  rw [eb_sum_weight]
  simp [eb_tail, show ¬ L + 1 ≤ L by omega]

private noncomputable def eb_law (α : ℝ) (L : ℕ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hL : 1 ≤ L) : Measure ℕ :=
  (PMF.ofFinset (fun k => ENNReal.ofReal (eb_weight α L k)) (Finset.range (L + 1))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => eb_weight_nonneg hα₀ hα₂ hL k),
        eb_sum_weight_all, ENNReal.ofReal_one])
    (fun k hk => by rw [eb_weight_of_not_mem_range hk, ENNReal.ofReal_zero])).toMeasure

private lemma eb_law_isProbability (α : ℝ) (L : ℕ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hL : 1 ≤ L) : IsProbabilityMeasure (eb_law α L hα₀ hα₂ hL) := by
  unfold eb_law
  infer_instance

private lemma eb_law_real_singleton (α : ℝ) (L : ℕ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hL : 1 ≤ L) (k : ℕ) :
    (eb_law α L hα₀ hα₂ hL).real {k} = eb_weight α L k := by
  let _ := eb_law_isProbability α L hα₀ hα₂ hL
  rw [Measure.real, eb_law, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]
  simp [ENNReal.toReal_ofReal (eb_weight_nonneg hα₀ hα₂ hL k)]

private lemma eb_law_real_tail (α : ℝ) (L : ℕ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hL : 1 ≤ L) (k : ℕ) :
    (eb_law α L hα₀ hα₂ hL).real {y | k ≤ y} = eb_tail α L k := by
  let _ := eb_law_isProbability α L hα₀ hα₂ hL
  have hc : {y : ℕ | k ≤ y}ᶜ = ↑(Finset.range k) := by
    ext y
    simp
  rw [← compl_compl {y : ℕ | k ≤ y}, hc, measureReal_compl (by measurability)]
  simp only [probReal_univ, ← sum_measureReal_singleton]
  simp_rw [eb_law_real_singleton α L hα₀ hα₂ hL]
  rw [eb_sum_weight]
  simp [eb_tail]

private lemma eb_law_tail (α : ℝ) (L : ℕ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hL : 1 ≤ L) (k : ℕ) :
    eb_law α L hα₀ hα₂ hL {y | k ≤ y} = ENNReal.ofReal (eb_tail α L k) := by
  let _ := eb_law_isProbability α L hα₀ hα₂ hL
  rw [← ofReal_measureReal, eb_law_real_tail]

private lemma eb_weight_term {α : ℝ} {L r : ℕ} (hr₀ : r ≠ 0) (hrL : r < L) :
    (2 : ℝ) ^ r * eb_weight α L r = α / 2 := by
  simp only [eb_weight, eb_tail, hr₀, show r ≤ L by omega, show r + 1 ≠ 0 by omega,
    show r + 1 ≤ L by omega, ite_true, ite_false]
  rw [pow_succ]
  field_simp
  ring

private lemma eb_weight_term_last {α : ℝ} {L : ℕ} (hL : 1 ≤ L) :
    (2 : ℝ) ^ L * eb_weight α L L = α := by
  simp only [eb_weight, eb_tail, show L ≠ 0 by omega, le_refl,
    show L + 1 ≠ 0 by omega, show ¬ L + 1 ≤ L by omega, ite_true, ite_false, sub_zero]
  field_simp

private lemma eb_bandMoment_law (α : ℝ) (L a : ℕ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hL : 1 ≤ L) (ha₀ : 1 ≤ a) (haL : a ≤ L)
    (ha : a = ⌈(3 * L : ℝ) / 4⌉₊) :
    bandMoment (eb_law α L hα₀ hα₂ hL) (upperBand L) =
      α + α / 2 * (L - a : ℕ) := by
  classical
  have hLmem : L ∈ upperBand L := by
    simp [upperBand, ← ha, haL]
  rw [bandMoment]
  simp_rw [eb_law_real_singleton α L hα₀ hα₂ hL]
  rw [← Finset.sum_erase_add _ _ hLmem, eb_weight_term_last hL]
  have hreg : ∀ r ∈ (upperBand L).erase L,
      (2 : ℝ) ^ r * eb_weight α L r = α / 2 := by
    intro r hr
    rw [Finset.mem_erase, upperBand, ← ha, Finset.mem_Icc] at hr
    exact eb_weight_term (by omega) (by omega)
  rw [Finset.sum_congr rfl hreg, Finset.sum_const]
  have hcard : ((upperBand L).erase L).card = L - a := by
    rw [Finset.card_erase_of_mem hLmem]
    simp [upperBand, ← ha]
    omega
  rw [hcard, nsmul_eq_mul]
  ring

private lemma eb_bandMass_lower (α : ℝ) (L a : ℕ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hL : 1 ≤ L) (ha₀ : 1 ≤ a) (haL : a ≤ L)
    (ha : a = ⌈(3 * L : ℝ) / 4⌉₊) :
    α * L / 8 ≤ bandMoment (eb_law α L hα₀ hα₂ hL) (upperBand L) := by
  rw [eb_bandMoment_law α L a hα₀ hα₂ hL ha₀ haL ha]
  have hceil : (L - a : ℝ) + 1 ≥ (L : ℝ) / 4 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (3 * L : ℝ) / 4)
    rw [← ha] at h
    linarith
  have hcast : ((L - a : ℕ) : ℝ) = (L : ℝ) - a := Nat.cast_sub haL
  rw [hcast]
  have hd : 0 ≤ (L : ℝ) - a + 1 - L / 4 := by linarith
  nlinarith [mul_nonneg hα₀ hd]

/-! ### Arithmetic for amplification -/

private lemma eb_band_index_bounds {L : ℕ} (hL : 1 ≤ L) :
    1 ≤ ⌈(3 * L : ℝ) / 4⌉₊ ∧ ⌈(3 * L : ℝ) / 4⌉₊ ≤ L := by
  constructor
  · apply Nat.ceil_pos.2
    positivity
  · apply Nat.ceil_le.2
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith

private lemma eb_large_L {α : ℝ} {L : ℕ} (hα₂ : α ≤ 2)
    (hA : (186624 : ℝ) ≤ α * (L : ℝ) ^ 2) : 306 ≤ L := by
  by_contra h
  have hL : L ≤ 305 := by omega
  have hLR : (L : ℝ) ≤ 305 := by exact_mod_cast hL
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hs : (L : ℝ) ^ 2 ≤ (305 : ℝ) ^ 2 := by nlinarith
  have hα₀ : 0 ≤ α := by nlinarith [sq_nonneg (L : ℝ)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hα₂) (sq_nonneg (L : ℝ))]

private lemma eb_L_third {L : ℕ} (hL : 3 ≤ L) : (L : ℝ) / 3 ≤ (L / 2 : ℕ) := by
  have h : L ≤ 3 * (L / 2) := by omega
  have hR : (L : ℝ) ≤ 3 * (L / 2 : ℕ) := by exact_mod_cast h
  linarith

private lemma eb_two_L_half_le (L : ℕ) : 2 * (L / 2) ≤ L := by omega

private lemma eb_fraction_bounds {c w : ℝ} (hc : 0 < c) (hw : 0 ≤ w) :
    0 ≤ 2 * (w / (w + c)) ^ 2 ∧ 2 * (w / (w + c)) ^ 2 ≤ 2 := by
  have hd : 0 < w + c := by linarith
  have hq₀ : 0 ≤ w / (w + c) := div_nonneg hw hd.le
  have hq₁ : w / (w + c) ≤ 1 := (div_le_one hd).2 (by linarith)
  constructor
  · positivity
  · nlinarith [sq_nonneg (w / (w + c) - 1)]

private lemma eb_pair_coeff_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    2 * (x / (x + 2)) ^ 2 ≤ 2 * (y / (y + 2)) ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  have hdx : 0 < x + 2 := by linarith
  have hdy : 0 < y + 2 := by linarith
  have hq : x / (x + 2) ≤ y / (y + 2) := by
    rw [div_le_div_iff₀ hdx hdy]
    nlinarith
  have hq₀ : 0 ≤ x / (x + 2) := div_nonneg hx hdx.le
  gcongr

private lemma eb_pair_coeff_identity {x : ℝ} (hx : 0 ≤ x) :
    (x / 8) / (x / 8 + 2) = x / (x + 16) := by
  have h₁ : (0 : ℝ) < x / 8 + 2 := by positivity
  have h₂ : (0 : ℝ) < x + 16 := by linarith
  field_simp
  ring

private lemma eb_next_large {w : ℝ} (hw : 128 ≤ w) :
    (128 / 81 : ℝ) ≤ 2 * (w / (w + 16)) ^ 2 := by
  have hd : (0 : ℝ) < w + 16 := by linarith
  have hq : (8 / 9 : ℝ) ≤ w / (w + 16) := by
    rw [div_le_div_iff₀ (by norm_num) hd]
    nlinarith
  calc
    (128 / 81 : ℝ) = 2 * (8 / 9 : ℝ) ^ 2 := by norm_num
    _ ≤ 2 * (w / (w + 16)) ^ 2 := by gcongr

private lemma eb_amplify_real {α l l' : ℝ} (hα₀ : 0 ≤ α) (hl : 0 < l)
    (hl' : l / 3 ≤ l') (hw : α * l < 128) (hA : 186624 ≤ α * l ^ 2) :
    2 * (α * l ^ 2) ≤ (2 * (α * l / (α * l + 16)) ^ 2) * l' ^ 2 := by
  have hw₀ : 0 ≤ α * l := mul_nonneg hα₀ hl.le
  have hd : 0 < α * l + 16 := by linarith
  have hd144 : α * l + 16 ≤ 144 := by linarith
  have hdsq : (α * l + 16) ^ 2 ≤ (144 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd144) (by linarith : 0 ≤ α * l + 16 + 144)]
  have hratio : (α * l) ^ 2 / (144 : ℝ) ^ 2 ≤ (α * l / (α * l + 16)) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg (α * l)) (sq_pos_of_pos hd) hdsq
  have hl'₀ : 0 ≤ l' := by linarith
  have hlsq : l ^ 2 / 9 ≤ l' ^ 2 := by
    have hl3 : l ≤ 3 * l' := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hl3) (by linarith : 0 ≤ 3 * l' + l)]
  let A := α * l ^ 2
  have hA₀ : 0 ≤ A := by dsimp [A]; positivity
  have hAA : 186624 * A ≤ A ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hA) hA₀
    dsimp [A] at this ⊢
    nlinarith
  calc
    2 * (α * l ^ 2) = 2 * A := rfl
    _ ≤ 2 * A ^ 2 / 186624 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 186624)]
      nlinarith
    _ = 2 * ((α * l) ^ 2 / (144 : ℝ) ^ 2) * (l ^ 2 / 9) := by
      dsimp [A]
      ring
    _ ≤ (2 * (α * l / (α * l + 16)) ^ 2) * l' ^ 2 := by gcongr

private lemma eb_initial_A_real {M l l' : ℝ} (hM : 0 ≤ M) (hl : 10000 ≤ l)
    (hband : 10000 ≤ l * M) (hl' : l / 3 ≤ l') :
    186624 ≤ 2 * (M / (M + 2)) ^ 2 * l' ^ 2 := by
  have hl₀ : 0 < l := by linarith
  have hl'₀ : 0 ≤ l' := by linarith
  have hd : 0 < M + 2 := by linarith
  have hq₀ : 0 ≤ M / (M + 2) := div_nonneg hM hd.le
  have hql : (10000 / 9 : ℝ) ≤ (M / (M + 2)) * l' := by
    by_cases hM1 : 1 ≤ M
    · have hq : (1 / 3 : ℝ) ≤ M / (M + 2) := by
        rw [le_div_iff₀ hd]
        linarith
      have hp : l' / 3 ≤ (M / (M + 2)) * l' := by
        have := mul_le_mul_of_nonneg_right hq hl'₀
        nlinarith
      have hlnum : (10000 : ℝ) / 3 ≤ l' := by linarith
      linarith
    · have hMle : M ≤ 1 := by linarith
      have hq : M / 3 ≤ M / (M + 2) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hd]
        nlinarith
      calc
        (10000 / 9 : ℝ) ≤ (l * M) / 9 := by linarith
        _ = (M / 3) * (l / 3) := by ring
        _ ≤ (M / (M + 2)) * l' := by gcongr
  calc
    (186624 : ℝ) ≤ 2 * (10000 / 9 : ℝ) ^ 2 := by norm_num
    _ ≤ 2 * ((M / (M + 2)) * l') ^ 2 := by gcongr
    _ = 2 * (M / (M + 2)) ^ 2 * l' ^ 2 := by ring

/-! ### One pair-counting step -/

private def eb_pairs_property : Prop :=
  ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ}, 2 ≤ L →
    ∀ {I : Finset ℕ}, I ⊆ upperBand L → ∀ {k : ℕ}, 1 ≤ k → k ≤ L / 2 →
      ((2 : ℝ) ^ k)⁻¹ * 2 * (bandMoment ν I / (bandMoment ν I + 2)) ^ 2 ≤
        (hardLaw ν L).real {y | k ≤ y}

private def eb_tailBelow (ν : Measure ℕ) (α : ℝ) (L : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ L →
    ENNReal.ofReal (eb_tail α L k) ≤ ν {y | k ≤ y}

private lemma eb_bandMoment_nonneg (ν : Measure ℕ) (I : Finset ℕ) :
    0 ≤ bandMoment ν I := by
  classical
  unfold bandMoment
  exact Finset.sum_nonneg fun r _ => mul_nonneg (by positivity) measureReal_nonneg

private lemma eb_step (hP : eb_pairs_property) (α : ℝ) (L : ℕ)
    (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) (hL : 306 ≤ L) :
    eb_tailBelow
      (hardLaw (eb_law α L (by positivity) (by exact hα₂) (by omega)) L)
      (2 * (α * L / (α * L + 16)) ^ 2) (L / 2) := by
  let hL₁ : 1 ≤ L := by omega
  let a := ⌈(3 * L : ℝ) / 4⌉₊
  have ha := eb_band_index_bounds hL₁
  have hM : α * L / 8 ≤
      bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) :=
    eb_bandMass_lower α L a hα₀ hα₂ hL₁ ha.1 ha.2 rfl
  have hM₀ : 0 ≤ bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) :=
    eb_bandMoment_nonneg _ _
  have hw₀ : 0 ≤ α * (L : ℝ) := mul_nonneg hα₀ (by positivity)
  have hc : 2 * (α * L / (α * L + 16)) ^ 2 ≤
      2 * (bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) /
        (bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) + 2)) ^ 2 := by
    rw [← eb_pair_coeff_identity hw₀]
    apply eb_pair_coeff_mono (div_nonneg hw₀ (by norm_num))
    exact hM
  let _ := eb_law_isProbability α L hα₀ hα₂ hL₁
  let _ := hardLaw_isProbability (eb_law α L hα₀ hα₂ hL₁) L
  intro k hk hkL
  have hp := hP (eb_law α L hα₀ hα₂ hL₁) (L := L) (by omega)
    (I := upperBand L) (subset_rfl) hk hkL
  have hreal : ((2 : ℝ) ^ k)⁻¹ * (2 * (α * L / (α * L + 16)) ^ 2) ≤
      (hardLaw (eb_law α L hα₀ hα₂ hL₁) L).real {y | k ≤ y} := by
    calc
      ((2 : ℝ) ^ k)⁻¹ * (2 * (α * L / (α * L + 16)) ^ 2) ≤
          ((2 : ℝ) ^ k)⁻¹ *
            (2 * (bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) /
              (bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) + 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = ((2 : ℝ) ^ k)⁻¹ * 2 *
          (bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) /
            (bandMoment (eb_law α L hα₀ hα₂ hL₁) (upperBand L) + 2)) ^ 2 := by ring
      _ ≤ _ := hp
  have he := ENNReal.ofReal_le_ofReal hreal
  rw [ofReal_measureReal] at he
  convert he using 1
  · apply congrArg ENNReal.ofReal
    simp only [eb_tail, show k ≠ 0 by omega, hkL, ite_false, ite_true]
    ring

private lemma eb_full_tail {ν : Measure ℕ} [IsProbabilityMeasure ν]
    {α : ℝ} {L : ℕ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) (hL : 1 ≤ L)
    (h : eb_tailBelow ν α L) (k : ℕ) :
    eb_law α L hα₀ hα₂ hL {y | k ≤ y} ≤ ν {y | k ≤ y} := by
  rw [eb_law_tail]
  by_cases hkL : k ≤ L
  · by_cases hk₀ : k = 0
    · subst k
      simp [eb_tail]
    · exact h k (by omega) hkL
  · simp [eb_tail, hkL, show k ≠ 0 by omega]

private lemma eb_hardLaw_add (ν : Measure ℕ) (m n : ℕ) :
    hardLaw (hardLaw ν m) n = hardLaw ν (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [hardLaw_succ, ih]
      rw [show m + (n + 1) = (m + n) + 1 by omega, hardLaw_succ]

private lemma eb_hardMean_add (ν : Measure ℕ) (m n : ℕ) :
    hardMean (hardLaw ν m) n = hardMean ν (m + n) := by
  rw [hardMean, hardMean, eb_hardLaw_add]

/-! ### The terminal mean estimate -/

private lemma eb_sum_tailFun_five (y : ℕ) :
    ∑ k ∈ Finset.Icc 1 5, tailFun k y ≤ y := by
  classical
  have hsub : (Finset.Icc 1 5).filter (fun x => x ≤ y) ⊆ Finset.Icc 1 y := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    omega
  have hc := Finset.card_le_card hsub
  simpa [tailFun] using hc

private lemma eb_mean_five {ν : Measure ℕ} {α : ℝ} {L : ℕ}
    (hα₀ : 0 ≤ α) (hL : 5 ≤ L) (ht : eb_tailBelow ν α L) :
    ENNReal.ofReal (α * (31 / 32 : ℝ)) ≤ ∫⁻ y, (y : ℝ≥0∞) ∂ν := by
  classical
  have hform : ∀ k ∈ Finset.Icc 1 5, eb_tail α L k = α / (2 : ℝ) ^ k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp [eb_tail, show k ≠ 0 by omega, show k ≤ L by omega]
  have hsum : ∑ k ∈ Finset.Icc 1 5, eb_tail α L k = α * (31 / 32 : ℝ) := by
    rw [Finset.sum_congr rfl hform]
    norm_num [Finset.sum_Icc_succ_top]
    ring
  rw [← hsum, ENNReal.ofReal_sum_of_nonneg]
  · calc
      (∑ k ∈ Finset.Icc 1 5, ENNReal.ofReal (eb_tail α L k)) ≤
          ∑ k ∈ Finset.Icc 1 5, ∫⁻ y, (tailFun k y : ℝ≥0∞) ∂ν := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← tail_as_lintegral]
        rw [Finset.mem_Icc] at hk
        exact ht k hk.1 (hk.2.trans hL)
      _ = ∫⁻ y, ∑ k ∈ Finset.Icc 1 5, (tailFun k y : ℝ≥0∞) ∂ν := by
        rw [lintegral_finsetSum _ (fun k _ => by fun_prop)]
      _ ≤ ∫⁻ y, (y : ℝ≥0∞) ∂ν := by
        apply lintegral_mono
        intro y
        have he : (↑(∑ k ∈ Finset.Icc 1 5, tailFun k y) : ℝ≥0∞) ≤
            (y : ℝ≥0∞) := by
          exact_mod_cast eb_sum_tailFun_five y
        simpa only [Nat.cast_sum] using he
  · intro k hk
    rw [hform k hk]
    positivity

private lemma eb_terminal_mean {ν : Measure ℕ} {α : ℝ} {L : ℕ}
    (hα : (128 / 81 : ℝ) ≤ α) (hL : 150 ≤ L) (ht : eb_tailBelow ν α L) :
    (3 / 2 : ℝ≥0∞) ≤ ∫⁻ y, (y : ℝ≥0∞) ∂ν := by
  have hα₀ : 0 ≤ α := by norm_num at hα ⊢; linarith
  have hreal : (3 / 2 : ℝ) ≤ α * (31 / 32 : ℝ) := by nlinarith
  calc
    (3 / 2 : ℝ≥0∞) = ENNReal.ofReal (3 / 2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    _ ≤ ENNReal.ofReal (α * (31 / 32 : ℝ)) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ∫⁻ y, (y : ℝ≥0∞) ∂ν := eb_mean_five hα₀ (by omega) ht

/-! ### Well-founded amplification -/

private def eb_allTailBelow (ν : Measure ℕ) (α : ℝ) (L : ℕ) : Prop :=
  ∀ k : ℕ, ENNReal.ofReal (eb_tail α L k) ≤ ν {y | k ≤ y}

private lemma eb_allTailBelow_of_tailBelow {ν : Measure ℕ} [IsProbabilityMeasure ν]
    {α : ℝ} {L : ℕ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) (hL : 1 ≤ L)
    (h : eb_tailBelow ν α L) : eb_allTailBelow ν α L := by
  intro k
  rw [← eb_law_tail α L hα₀ hα₂ hL]
  exact eb_full_tail hα₀ hα₂ hL h k

private theorem eb_amplify (hP : eb_pairs_property)
    (L : ℕ) (α : ℝ) (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2)
    (hA : (186624 : ℝ) ≤ α * (L : ℝ) ^ 2)
    (ν : Measure ℕ) [IsProbabilityMeasure ν] (htail : eb_allTailBelow ν α L) :
    ∃ T : ℕ, T ≤ 2 * L ∧ (3 / 2 : ℝ≥0∞) ≤ hardMean ν T := by
  induction L using Nat.strong_induction_on generalizing α ν with
  | _ L ih =>
    have hL : 306 ≤ L := eb_large_L hα₂ hA
    have hL₁ : 1 ≤ L := by omega
    have hthird : (L : ℝ) / 3 ≤ (L / 2 : ℕ) := eb_L_third (by omega)
    have htailLaw : ∀ k : ℕ,
        eb_law α L hα₀ hα₂ hL₁ {y | k ≤ y} ≤ ν {y | k ≤ y} := by
      intro k
      rw [eb_law_tail]
      exact htail k
    have hevolved := hardLaw_tail_mono htailLaw L
    have hw₀ : 0 ≤ α * (L : ℝ) := mul_nonneg hα₀ (by positivity)
    have hstep := eb_step hP α L hα₀ hα₂ hL
    let _ := eb_law_isProbability α L hα₀ hα₂ hL₁
    let _ := hardLaw_isProbability (eb_law α L hα₀ hα₂ hL₁) L
    have hβ := eb_fraction_bounds (c := 16) (by norm_num) hw₀
    by_cases hw : 128 ≤ α * (L : ℝ)
    · have hβlarge : (128 / 81 : ℝ) ≤ 2 * (α * L / (α * L + 16)) ^ 2 :=
        eb_next_large hw
      let _ := hardLaw_isProbability ν L
      have hnext : eb_tailBelow (hardLaw ν L)
          (2 * (α * L / (α * L + 16)) ^ 2) (L / 2) := by
        intro k hk hkL
        have hs := eb_allTailBelow_of_tailBelow hβ.1 hβ.2 (by omega) hstep k
        exact (hs.trans (hevolved k))
      have hm := eb_terminal_mean hβlarge (show 150 ≤ L / 2 by omega) hnext
      refine ⟨L, by omega, ?_⟩
      simpa [hardMean] using hm
    · have hwlt : α * (L : ℝ) < 128 := lt_of_not_ge hw
      have hdouble := eb_amplify_real hα₀ (by positivity : (0 : ℝ) < L) hthird hwlt hA
      have hA' : (186624 : ℝ) ≤
          (2 * (α * L / (α * L + 16)) ^ 2) * (L / 2 : ℕ) ^ 2 := by
        have hA₀ : (0 : ℝ) ≤ 186624 := by norm_num
        rw [show ((L / 2 : ℕ) : ℝ) = (L / 2 : ℕ) by rfl]
        linarith
      let _ := hardLaw_isProbability ν L
      have hnext : eb_allTailBelow (hardLaw ν L)
          (2 * (α * L / (α * L + 16)) ^ 2) (L / 2) := by
        intro k
        have hs := eb_allTailBelow_of_tailBelow hβ.1 hβ.2 (by omega) hstep k
        exact hs.trans (hevolved k)
      obtain ⟨T, hT, hm⟩ := ih (L / 2) (by omega)
        (2 * (α * L / (α * L + 16)) ^ 2) hβ.1 hβ.2 hA' (hardLaw ν L) hnext
      refine ⟨L + T, ?_, ?_⟩
      · have := eb_two_L_half_le L
        omega
      · rw [← eb_hardMean_add]
        exact hm

/-- A uniform upper-band moment implies bounded time to hard mean at least
`3/2` and a uniform hard-free-energy lower bound, assuming pair counting. -/
theorem escape_bandExit_of_pairs
    (hP : ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ}, 2 ≤ L →
      ∀ {I : Finset ℕ}, I ⊆ upperBand L → ∀ {k : ℕ}, 1 ≤ k → k ≤ L / 2 →
        ((2 : ℝ) ^ k)⁻¹ * 2 * (bandMoment ν I / (bandMoment ν I + 2)) ^ 2 ≤
          (hardLaw ν L).real {y | k ≤ y})
    (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ}
    (hL : 10 ^ 4 ≤ L) (hband : (10 : ℝ) ^ 4 ≤ L * bandMoment ν (upperBand L)) :
    (∃ T : ℕ, T ≤ 2 * L ∧ (3 / 2 : ℝ≥0∞) ≤ hardMean ν T) ∧
      2⁻¹ * ((2 : ℝ≥0∞) ^ (2 * L))⁻¹ ≤ hardFreeEnergy ν := by
  norm_num at hband
  have hLR : (10000 : ℝ) ≤ L := by exact_mod_cast hL
  have hM₀ : 0 ≤ bandMoment ν (upperBand L) := eb_bandMoment_nonneg _ _
  have hthird : (L : ℝ) / 3 ≤ (L / 2 : ℕ) := eb_L_third (by omega)
  have hA : (186624 : ℝ) ≤
      2 * (bandMoment ν (upperBand L) / (bandMoment ν (upperBand L) + 2)) ^ 2 *
        ((L / 2 : ℕ) : ℝ) ^ 2 :=
    eb_initial_A_real hM₀ hLR hband hthird
  have hβ := eb_fraction_bounds (c := 2) (by norm_num) hM₀
  let _ := hardLaw_isProbability ν L
  have hfirst : eb_tailBelow (hardLaw ν L)
      (2 * (bandMoment ν (upperBand L) / (bandMoment ν (upperBand L) + 2)) ^ 2)
      (L / 2) := by
    intro k hk hkL
    have hp := hP ν (L := L) (by omega) (I := upperBand L) subset_rfl hk hkL
    have he := ENNReal.ofReal_le_ofReal hp
    rw [ofReal_measureReal] at he
    convert he using 1
    apply congrArg ENNReal.ofReal
    simp only [eb_tail, show k ≠ 0 by omega, hkL, ite_false, ite_true]
    ring
  have hall := eb_allTailBelow_of_tailBelow hβ.1 hβ.2 (by omega) hfirst
  obtain ⟨T, hT, hm⟩ := eb_amplify hP (L / 2)
    (2 * (bandMoment ν (upperBand L) / (bandMoment ν (upperBand L) + 2)) ^ 2)
    hβ.1 hβ.2 hA (hardLaw ν L) hall
  have htime : L + T ≤ 2 * L := by
    have := eb_two_L_half_le L
    omega
  have hmean : (3 / 2 : ℝ≥0∞) ≤ hardMean ν (L + T) := by
    rw [← eb_hardMean_add]
    exact hm
  refine ⟨⟨L + T, htime, hmean⟩, ?_⟩
  have hpow : ((2 : ℝ≥0∞) ^ (2 * L))⁻¹ ≤ ((2 : ℝ≥0∞) ^ (L + T))⁻¹ := by
    gcongr
    norm_num
  have hm₁ : (2 : ℝ≥0∞)⁻¹ ≤ hardMean ν (L + T) - 1 := by
    apply ENNReal.le_sub_of_add_le_left (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    have hc : (1 : ℝ≥0∞) + 2⁻¹ = 3 / 2 := by
      rw [ENNReal.div_eq_inv_mul]
      calc
        (1 : ℝ≥0∞) + 2⁻¹ = (2⁻¹ + 2⁻¹) + 2⁻¹ := by
          rw [ENNReal.inv_two_add_inv_two]
        _ = 2⁻¹ * 3 := by ring
    rw [hc]
    exact hmean
  calc
    2⁻¹ * ((2 : ℝ≥0∞) ^ (2 * L))⁻¹ ≤
        2⁻¹ * ((2 : ℝ≥0∞) ^ (L + T))⁻¹ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((2 : ℝ≥0∞) ^ (L + T))⁻¹ * 2⁻¹ := mul_comm _ _
    _ ≤ ((2 : ℝ≥0∞) ^ (L + T))⁻¹ * (hardMean ν (L + T) - 1) :=
      mul_le_mul_of_nonneg_left hm₁ (by positivity)
    _ ≤ hardFreeEnergy ν := hardFreeEnergy_ge_aux ν (L + T)

end DiamondPinning
