module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Moments
public import DiamondPinning.Model.FreeEnergy
public import DiamondPinning.Statements.Env
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Fractional-moment recursion and the critical barrier

This module proves the fractional-moment inequality `eq:jensen` and the
critical floor barrier `lem:barrier`. The barrier follows from the defect
recursion `eq:contraction` together with finite-height field comparison.
The source is `source/critical.tex` lines 84–155 for the moment recursion and
lines 163–178 for the barrier.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set

private theorem rpow_le_one_add {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    x ^ q ≤ 1 + x := by
  rcases le_total x 1 with hx1 | hx1
  · exact (Real.rpow_le_one hx hx1 hq0).trans (by linarith)
  · calc
      x ^ q ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hq1
      _ = x := Real.rpow_one x
      _ ≤ 1 + x := by linarith

private theorem integrable_realMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun x : ℝ => x ^ q) (lawR μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hdom : Integrable (fun x : ℝ => 1 + x) (lawR μ B h n) :=
    (integrable_const 1).add hi
  apply hdom.mono' (Real.continuous_rpow_const hq0).measurable.aestronglyMeasurable
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]
  exact rpow_le_one_add hx.le hq0 hq1

private theorem realMoment_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < realMoment μ B h n q := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_realMoment hpos hmean hB h n hq0 hq1
  have hsupp : Function.support (fun x : ℝ => x ^ q) =ᵐ[lawR μ B h n] Set.univ := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    simp only [Function.support, Set.mem_ofPred_eq, Set.mem_univ]
    exact eq_true (Real.rpow_pos_of_pos hx q).ne'
  unfold realMoment
  have hnonneg : 0 ≤ᵐ[lawR μ B h n] (fun x : ℝ => x ^ q) := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    exact Real.rpow_nonneg hx.le q
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hi, measure_congr hsupp, measure_univ]
  exact zero_lt_one

private theorem convexOn_rpow_add_const {q c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 ≤ c) :
    ConvexOn ℝ (Ici 0) (fun x => (x ^ (1 / q) + c) ^ q) := by
  let p := 1 / q
  let f' : ℝ → ℝ := fun x => (x ^ p + c) ^ (q - 1) * x ^ (p - 1)
  let f'' : ℝ → ℝ := fun x =>
    ((q - 1) * (x ^ p + c) ^ (q - 2) * (p * x ^ (p - 1))) * x ^ (p - 1) +
      (x ^ p + c) ^ (q - 1) * ((p - 1) * x ^ (p - 2))
  have hp0 : 0 < p := one_div_pos.mpr hq0
  have hp1 : 1 < p := (one_lt_div hq0).mpr hq1
  have hqp : q * p = 1 := by dsimp [p]; field_simp
  have hpq : (q - 1) * p = 1 - p := by nlinarith
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici (0 : ℝ)) (f' := f') (f'' := f'')
  · exact ((Real.continuous_rpow_const hp0.le).add continuous_const).continuousOn.rpow_const
      (fun _ _ => Or.inr hq0.le)
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hg : HasDerivAt (fun y : ℝ => y ^ p + c) (p * x ^ (p - 1)) x := by
      convert (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx0)).add_const c using 1
    have hbase : x ^ p + c ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hx p) hc)
    convert (hg.rpow_const (p := q) (Or.inl hbase)).hasDerivWithinAt using 1
    dsimp [f']
    calc
      (x ^ p + c) ^ (q - 1) * x ^ (p - 1) =
          (q * p) * (x ^ p + c) ^ (q - 1) * x ^ (p - 1) := by rw [hqp, one_mul]
      _ = p * x ^ (p - 1) * q * (x ^ p + c) ^ (q - 1) := by ring

  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hg : HasDerivAt (fun y : ℝ => y ^ p + c) (p * x ^ (p - 1)) x := by
      convert (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx0)).add_const c using 1
    have hg' : HasDerivAt (fun y : ℝ => y ^ (p - 1))
        ((p - 1) * x ^ (p - 2)) x := by
      convert Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hx0) using 1
      ring
    have hbase : x ^ p + c ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hx p) hc)
    convert ((hg.rpow_const (p := q - 1) (Or.inl hbase)).mul hg').hasDerivWithinAt using 1
    dsimp [f', f'']
    ring
  · intro x hx
    rw [interior_Ici] at hx
    have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
    have hgpos : 0 < x ^ p + c := by positivity
    have hnonneg : 0 ≤ (x ^ p + c) ^ (q - 2) * x ^ (p - 2) * (p - 1) * c := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hgpos.le _) (Real.rpow_nonneg hx.le _))
          (sub_nonneg.mpr hp1.le)) hc
    convert hnonneg using 1
    have hg1 : (x ^ p + c) ^ (q - 1) = (x ^ p + c) ^ (q - 2) * (x ^ p + c) := by
      calc
        (x ^ p + c) ^ (q - 1) = (x ^ p + c) ^ ((q - 2) + 1) := by
          congr 1
          ring
        _ = (x ^ p + c) ^ (q - 2) * (x ^ p + c) ^ (1 : ℝ) := Real.rpow_add hgpos _ _
        _ = (x ^ p + c) ^ (q - 2) * (x ^ p + c) := by rw [Real.rpow_one]
    have hpow : x ^ (p - 1) * x ^ (p - 1) = x ^ (p - 2) * x ^ p := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      ring
    dsimp [f'']
    rw [hg1]
    calc
      (q - 1) * (x ^ p + c) ^ (q - 2) * (p * x ^ (p - 1)) * x ^ (p - 1) +
          (x ^ p + c) ^ (q - 2) * (x ^ p + c) * ((p - 1) * x ^ (p - 2)) =
          (x ^ p + c) ^ (q - 2) * x ^ (p - 2) *
            ((q - 1) * p * x ^ p + (p - 1) * (x ^ p + c)) := by
              linear_combination ((q - 1) * (x ^ p + c) ^ (q - 2) * p) * hpow
      _ = (x ^ p + c) ^ (q - 2) * x ^ (p - 2) * (p - 1) * c := by
              rw [hpq]
              ring

private theorem product_realMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) (q : ℝ) :
    (∫ p : ℝ × ℝ, (p.1 * p.2) ^ q ∂((lawR μ B h n).prod (lawR μ B h n))) =
      realMoment μ B h n q ^ 2 := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hp : ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h n).prod (lawR μ B h n)),
      (p.1 * p.2) ^ q = p.1 ^ q * p.2 ^ q := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    filter_upwards [ae_pos_lawR hpos hB h n] with y hy
    exact Real.mul_rpow hx.le hy.le
  rw [integral_congr_ae hp, integral_prod_mul (fun x : ℝ => x ^ q) (fun y : ℝ => y ^ q)]
  simp only [realMoment]
  ring


private theorem realMoment_succ_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (((realMoment μ B h n q ^ (1 / q)) ^ 2 + (B - 1)) / B) ^ q ≤
      realMoment μ B h (n + 1) q := by
  let ν := lawR μ B h n
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let p := 1 / q
  have hp0 : 0 < p := one_div_pos.mpr hq0
  have hp1 : 1 < p := (one_lt_div hq0).mpr hq1
  have hqp : q * p = 1 := by dsimp [p]; field_simp
  have hB0 : 0 < B := by linarith
  have hc : 0 ≤ B - 1 := by linarith
  have hG : 0 < realMoment μ B h n q := realMoment_pos hpos hmean hB h n hq0.le hq1.le
  have hpair : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), 0 < z.1 ∧ 0 < z.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    filter_upwards [ae_pos_lawR hpos hB h n] with y hy
    exact ⟨hx, hy⟩
  have hpow_mul : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν),
      (z.1 * z.2) ^ q = z.1 ^ q * z.2 ^ q := by
    filter_upwards [hpair] with z hz
    exact Real.mul_rpow hz.1.le hz.2.le
  have hqi : Integrable (fun x : ℝ => x ^ q) ν :=
    integrable_realMoment hpos hmean hB h n hq0.le hq1.le
  have hSq : Integrable (fun z : ℝ × ℝ => (z.1 * z.2) ^ q) (ν.prod ν) :=
    (hqi.mul_prod hqi).congr (Filter.EventuallyEq.symm hpow_mul)
  let f : ℝ → ℝ := fun x => (x ^ p + (B - 1)) ^ q
  have hfcont : Continuous f :=
    ((Real.continuous_rpow_const hp0.le).add continuous_const).rpow_const (fun _ => Or.inr hq0.le)
  have hcomp : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν),
      f ((z.1 * z.2) ^ q) = (z.1 * z.2 + (B - 1)) ^ q := by
    filter_upwards [hpair] with z hz
    dsimp [f]
    congr 2
    rw [← Real.rpow_mul (mul_nonneg hz.1.le hz.2.le), hqp, Real.rpow_one]
  have hfi : Integrable (fun z : ℝ × ℝ => f ((z.1 * z.2) ^ q)) (ν.prod ν) := by
    have hdom : Integrable (fun z : ℝ × ℝ => (z.1 * z.2) ^ q + (B - 1) ^ q) (ν.prod ν) :=
      hSq.add (integrable_const _)
    apply hdom.mono' (hfcont.comp ((Real.continuous_rpow_const hq0.le).comp
      (continuous_fst.mul continuous_snd))).measurable.aestronglyMeasurable
    filter_upwards [hpair] with z hz
    have hz0 : 0 ≤ z.1 * z.2 := mul_nonneg hz.1.le hz.2.le
    change ‖f ((z.1 * z.2) ^ q)‖ ≤ (z.1 * z.2) ^ q + (B - 1) ^ q
    rw [Real.norm_of_nonneg (Real.rpow_nonneg
      (add_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hz0 q) p) hc) q)]
    calc
      (((z.1 * z.2) ^ q) ^ p + (B - 1)) ^ q ≤
          (((z.1 * z.2) ^ q) ^ p) ^ q + (B - 1) ^ q :=
        Real.rpow_add_le_add_rpow (Real.rpow_nonneg (Real.rpow_nonneg hz0 q) p) hc hq0.le hq1.le
      _ = (z.1 * z.2) ^ q + (B - 1) ^ q := by
        congr 1
        rw [← Real.rpow_mul (Real.rpow_nonneg hz0 q), mul_comm p q, hqp, Real.rpow_one]
  have hJ := (convexOn_rpow_add_const hq0 hq1 hc).map_integral_le hfcont.continuousOn
    isClosed_Ici (show ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), (z.1 * z.2) ^ q ∈ Ici 0 by
      filter_upwards [hpair] with z hz
      exact Real.rpow_nonneg (mul_nonneg hz.1.le hz.2.le) q) hSq hfi
  rw [integral_congr_ae hcomp, product_realMoment hpos hB h n q] at hJ
  have hsquare : (realMoment μ B h n q ^ 2) ^ p = (realMoment μ B h n q ^ p) ^ 2 := by
    rw [← Real.rpow_natCast (realMoment μ B h n q ^ p) 2,
      ← Real.rpow_natCast (realMoment μ B h n q) 2,
      ← Real.rpow_mul hG.le, ← Real.rpow_mul hG.le]
    congr 1
    push_cast
    ring
  rw [hsquare] at hJ
  have hrec : realMoment μ B h (n + 1) q =
      (∫ z : ℝ × ℝ, (z.1 * z.2 + (B - 1)) ^ q ∂(ν.prod ν)) / B ^ q := by
    unfold realMoment
    rw [lawR_succ, integral_map (by fun_prop)
      (Real.continuous_rpow_const hq0.le).measurable.aestronglyMeasurable, ← integral_div]
    apply integral_congr_ae
    filter_upwards [hpair] with z hz
    exact Real.div_rpow (add_nonneg (mul_nonneg hz.1.le hz.2.le) hc) hB0.le q
  have hmain : (((realMoment μ B h n q ^ p) ^ 2 + (B - 1)) / B) ^ q ≤
      realMoment μ B h (n + 1) q := by
    have hbase : 0 ≤ (realMoment μ B h n q ^ p) ^ 2 + (B - 1) :=
      add_nonneg (sq_nonneg _) hc
    rw [hrec, Real.div_rpow hbase hB0.le q]
    exact (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hB0 q)).2 hJ
  exact hmain

/-- Squaring and taking the `q`-th power gives the recursive lower bound for
fractional moments in `eq:jensen`, proving the frozen `jensen_step`. -/
theorem jensen_step_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    ((realMoment μ B h n q ^ (1 / q)) ^ 2 + (B - 1)) / B ≤
      realMoment μ B h (n + 1) q ^ (1 / q) := by
  have hlow := realMoment_succ_lower hpos hmean hB h hq0 hq1 n
  have hbase : 0 ≤ ((realMoment μ B h n q ^ (1 / q)) ^ 2 + (B - 1)) / B := by
    exact div_nonneg (add_nonneg (sq_nonneg _) (by linarith)) (by linarith)
  have hp : 0 ≤ 1 / q := (one_div_pos.mpr hq0).le
  have hout := Real.rpow_le_rpow (Real.rpow_nonneg hbase q) hlow hp
  calc
    ((realMoment μ B h n q ^ (1 / q)) ^ 2 + (B - 1)) / B =
        ((((realMoment μ B h n q ^ (1 / q)) ^ 2 + (B - 1)) / B) ^ q) ^ (1 / q) := by
      rw [← Real.rpow_mul hbase, show q * (1 / q) = 1 by field_simp, Real.rpow_one]
    _ ≤ realMoment μ B h (n + 1) q ^ (1 / q) := hout


private theorem rpow_correction_anti {r x c q : ℝ} (hr : 0 ≤ r) (hrx : r ≤ x)
    (hc : 0 ≤ c) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (x + c) ^ q - x ^ q ≤ (r + c) ^ q - r ^ q := by
  rcases hrx.eq_or_lt with hrx | hrx
  · subst x
    rfl
  rcases hc.eq_or_lt with hc | hc
  · subst c
    simp
  let d := x + c - r
  let a := (x - r) / d
  let b := c / d
  have hd : 0 < d := by dsimp [d]; linarith
  have hxc : 0 ≤ x + c := add_nonneg (hr.trans hrx.le) hc.le
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hd.le
  have hb0 : 0 ≤ b := div_nonneg hc.le hd.le
  have ha : a * d = x - r := by
    dsimp [a]
    exact div_mul_cancel₀ _ hd.ne'
  have hb : b * d = c := by
    dsimp [b]
    exact div_mul_cancel₀ _ hd.ne'
  have hab : a + b = 1 := by
    apply mul_left_cancel₀ hd.ne'
    calc
      d * (a + b) = a * d + b * d := by ring
      _ = (x - r) + c := by rw [ha, hb]
      _ = d * 1 := by dsimp [d]; ring
  have hpoint1 : a * r + b * (x + c) = r + c := by
    apply mul_left_cancel₀ hd.ne'
    calc
      d * (a * r + b * (x + c)) = (a * d) * r + (b * d) * (x + c) := by ring
      _ = (x - r) * r + c * (x + c) := by rw [ha, hb]
      _ = d * (r + c) := by dsimp [d]; ring
  have hpoint2 : b * r + a * (x + c) = x := by
    apply mul_left_cancel₀ hd.ne'
    calc
      d * (b * r + a * (x + c)) = (b * d) * r + (a * d) * (x + c) := by ring
      _ = c * r + (x - r) * (x + c) := by rw [ha, hb]
      _ = d * x := by dsimp [d]; ring
  have h1 := (Real.concaveOn_rpow hq0 hq1).2 hr hxc ha0 hb0 hab
  have h2 := (Real.concaveOn_rpow hq0 hq1).2 hr hxc hb0 ha0 (by linarith [hab])
  simp only [smul_eq_mul] at h1 h2
  rw [hpoint1] at h1
  rw [hpoint2] at h2
  have hsum : (a + b) * (r ^ q + (x + c) ^ q) ≤ (r + c) ^ q + x ^ q := by
    nlinarith
  rw [hab, one_mul] at hsum
  linarith

private theorem realMoment_succ_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    realMoment μ B h (n + 1) q ≤
      (realMoment μ B h n q ^ 2 +
        ((floorSeq B n ^ 2 + (B - 1)) ^ q - floorSeq B n ^ (2 * q))) / B ^ q := by
  let ν := lawR μ B h n
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  have hB0 : 0 < B := by linarith
  have hc : 0 ≤ B - 1 := by linarith
  have hb : 0 ≤ floorSeq B n := floorSeq_nonneg hB n
  have hpair : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), 0 < z.1 ∧ 0 < z.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    filter_upwards [ae_pos_lawR hpos hB h n] with y hy
    exact ⟨hx, hy⟩
  have hpairFloor : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), floorSeq B n ^ 2 ≤ z.1 * z.2 := by
    have hf : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν),
        floorSeq B n ≤ z.1 ∧ floorSeq B n ≤ z.2 := by
      rw [Measure.ae_prod_iff_ae_ae (by measurability)]
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with y hy
      exact ⟨hx, hy⟩
    filter_upwards [hf] with z hz
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hz.2)]
  have hpow_mul : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν),
      (z.1 * z.2) ^ q = z.1 ^ q * z.2 ^ q := by
    filter_upwards [hpair] with z hz
    exact Real.mul_rpow hz.1.le hz.2.le
  have hqi : Integrable (fun x : ℝ => x ^ q) ν :=
    integrable_realMoment hpos hmean hB h n hq0.le hq1.le
  have hSq : Integrable (fun z : ℝ × ℝ => (z.1 * z.2) ^ q) (ν.prod ν) :=
    (hqi.mul_prod hqi).congr (Filter.EventuallyEq.symm hpow_mul)
  have hb2 : (floorSeq B n ^ 2) ^ q = floorSeq B n ^ (2 * q) := by
    rw [← Real.rpow_natCast (floorSeq B n) 2, ← Real.rpow_mul hb]
    norm_num
  have hpoint : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν),
      (z.1 * z.2 + (B - 1)) ^ q ≤ (z.1 * z.2) ^ q +
        ((floorSeq B n ^ 2 + (B - 1)) ^ q - floorSeq B n ^ (2 * q)) := by
    filter_upwards [hpair, hpairFloor] with z hz hzb
    have hh := rpow_correction_anti (sq_nonneg (floorSeq B n)) hzb hc hq0.le hq1.le
    rw [hb2] at hh
    linarith
  have hleft : Integrable (fun z : ℝ × ℝ => (z.1 * z.2 + (B - 1)) ^ q) (ν.prod ν) := by
    apply (hSq.add (integrable_const
      ((floorSeq B n ^ 2 + (B - 1)) ^ q - floorSeq B n ^ (2 * q)))).mono'
      ((Real.continuous_rpow_const hq0.le).comp
        ((continuous_fst.mul continuous_snd).add continuous_const)).measurable.aestronglyMeasurable
    filter_upwards [hpair, hpairFloor] with z hz hzb
    change ‖(z.1 * z.2 + (B - 1)) ^ q‖ ≤ (z.1 * z.2) ^ q +
      ((floorSeq B n ^ 2 + (B - 1)) ^ q - floorSeq B n ^ (2 * q))
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (add_nonneg (mul_nonneg hz.1.le hz.2.le) hc) q)]
    have hh := rpow_correction_anti (sq_nonneg (floorSeq B n)) hzb hc hq0.le hq1.le
    rw [hb2] at hh
    linarith
  have hrec : realMoment μ B h (n + 1) q =
      (∫ z : ℝ × ℝ, (z.1 * z.2 + (B - 1)) ^ q ∂(ν.prod ν)) / B ^ q := by
    unfold realMoment
    rw [lawR_succ, integral_map (by fun_prop)
      (Real.continuous_rpow_const hq0.le).measurable.aestronglyMeasurable, ← integral_div]
    apply integral_congr_ae
    filter_upwards [hpair] with z hz
    exact Real.div_rpow (add_nonneg (mul_nonneg hz.1.le hz.2.le) hc) hB0.le q
  rw [hrec]
  apply (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hB0 q)).2
  calc
    (∫ z : ℝ × ℝ, (z.1 * z.2 + (B - 1)) ^ q ∂(ν.prod ν)) ≤
        ∫ z : ℝ × ℝ, ((z.1 * z.2) ^ q +
          ((floorSeq B n ^ 2 + (B - 1)) ^ q - floorSeq B n ^ (2 * q))) ∂(ν.prod ν) :=
      integral_mono_ae hleft (hSq.add (integrable_const _)) hpoint
    _ = realMoment μ B h n q ^ 2 +
        ((floorSeq B n ^ 2 + (B - 1)) ^ q - floorSeq B n ^ (2 * q)) := by
      rw [integral_add hSq (integrable_const _), integral_const,
        product_realMoment hpos hB h n q]
      simp


private theorem realMoment_floor_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    floorSeq B n ^ q ≤ realMoment μ B h n q := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  unfold realMoment
  have hconst : (∫ _x : ℝ, floorSeq B n ^ q ∂lawR μ B h n) = floorSeq B n ^ q := by simp
  rw [← hconst]
  apply integral_mono_ae (integrable_const _) (integrable_realMoment hpos hmean hB h n hq0 hq1)
  filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
  exact Real.rpow_le_rpow (floorSeq_nonneg hB n) hx hq0

/-- The floor-centered moment defect obeys `eq:contraction`
(`source/critical.tex` lines 171–173). -/
private theorem realMoment_defect_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    realMoment μ B h (n + 1) q - floorSeq B (n + 1) ^ q ≤
      (2 * (realMoment μ B h n q - floorSeq B n ^ q) +
        (realMoment μ B h n q - floorSeq B n ^ q) ^ 2) / B ^ q := by
  have hB0 : 0 < B := by linarith
  have hc : 0 ≤ B - 1 := by linarith
  have hb : 0 ≤ floorSeq B n := floorSeq_nonneg hB n
  have hb1 : floorSeq B n ≤ 1 := floorSeq_le_one hB n
  have hbq : floorSeq B n ^ q ≤ 1 := Real.rpow_le_one hb hb1 hq0.le
  have hY : 0 ≤ realMoment μ B h n q - floorSeq B n ^ q :=
    sub_nonneg.mpr (realMoment_floor_lower hpos hmean hB h n hq0.le hq1.le)
  have hupper := realMoment_succ_upper hpos hmean hB h hq0 hq1 n
  have hfloor : floorSeq B (n + 1) ^ q =
      (floorSeq B n ^ 2 + (B - 1)) ^ q / B ^ q := by
    rw [floorSeq_succ, Real.div_rpow (add_nonneg (sq_nonneg _) hc) hB0.le]
  rw [hfloor]
  calc
    realMoment μ B h (n + 1) q - (floorSeq B n ^ 2 + (B - 1)) ^ q / B ^ q ≤
        (realMoment μ B h n q ^ 2 +
          ((floorSeq B n ^ 2 + (B - 1)) ^ q - floorSeq B n ^ (2 * q))) / B ^ q -
          (floorSeq B n ^ 2 + (B - 1)) ^ q / B ^ q := sub_le_sub_right hupper _
    _ = (realMoment μ B h n q ^ 2 - (floorSeq B n ^ q) ^ 2) / B ^ q := by
      have hb2 : floorSeq B n ^ (2 * q) = (floorSeq B n ^ q) ^ 2 := by
        rw [← Real.rpow_natCast (floorSeq B n ^ q) 2, ← Real.rpow_mul hb]
        congr 1
        push_cast
        ring
      rw [hb2]
      ring
    _ = (2 * floorSeq B n ^ q * (realMoment μ B h n q - floorSeq B n ^ q) +
        (realMoment μ B h n q - floorSeq B n ^ q) ^ 2) / B ^ q := by ring
    _ ≤ (2 * (realMoment μ B h n q - floorSeq B n ^ q) +
        (realMoment μ B h n q - floorSeq B n ^ q) ^ 2) / B ^ q := by
      apply (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hB0 q)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hbq) hY]

private theorem tendsto_realMoment_of_small_defect {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ)
    (hsmall : realMoment μ B h n q - floorSeq B n ^ q < B ^ q - 2) :
    Tendsto (fun k => realMoment μ B h k q) atTop (𝓝 1) := by
  let Y : ℕ → ℝ := fun k => realMoment μ B h k q - floorSeq B k ^ q
  let r : ℝ := (2 + Y n) / B ^ q
  have hB0 : 0 < B := by linarith
  have hA : 0 < B ^ q := Real.rpow_pos_of_pos hB0 q
  have hYn : 0 ≤ Y n := sub_nonneg.mpr (realMoment_floor_lower hpos hmean hB h n hq0.le hq1.le)
  have hA2 : 2 < B ^ q := by dsimp [Y] at hsmall hYn; linarith
  have hr0 : 0 ≤ r := div_nonneg (by dsimp [Y] at *; linarith) hA.le
  have hr1 : r < 1 := by
    rw [div_lt_one hA]
    dsimp [Y] at *
    linarith
  have hstep (k : ℕ) : Y (k + 1) ≤ (2 * Y k + Y k ^ 2) / B ^ q := by
    exact realMoment_defect_step hpos hmean hB h hq0 hq1 k
  have htail : ∀ k : ℕ, 0 ≤ Y (n + k) ∧ Y (n + k) ≤ Y n ∧
      Y (n + k) ≤ r ^ k * Y n := by
    intro k
    induction k with
    | zero => simp [hYn]
    | succ k ih =>
      have hs := hstep (n + k)
      have hratio : Y ((n + k) + 1) ≤ r * Y (n + k) := by
        calc
          Y ((n + k) + 1) ≤ (2 * Y (n + k) + Y (n + k) ^ 2) / B ^ q := hs
          _ = (Y (n + k) * (2 + Y (n + k))) / B ^ q := by ring
          _ ≤ (Y (n + k) * (2 + Y n)) / B ^ q := by
            apply (div_le_div_iff_of_pos_right hA).2
            exact mul_le_mul_of_nonneg_left (by linarith [ih.2.1]) ih.1
          _ = r * Y (n + k) := by dsimp [r]; ring
      have hweak : Y ((n + k) + 1) ≤ Y (n + k) := by
        calc
          Y ((n + k) + 1) ≤ r * Y (n + k) := hratio
          _ ≤ 1 * Y (n + k) := mul_le_mul_of_nonneg_right hr1.le ih.1
          _ = Y (n + k) := one_mul _
      rw [show n + (k + 1) = (n + k) + 1 by omega]
      refine ⟨sub_nonneg.mpr (realMoment_floor_lower hpos hmean hB h (n + (k + 1)) hq0.le hq1.le),
        hweak.trans ih.2.1, ?_⟩
      calc
        Y ((n + k) + 1) ≤ r * Y (n + k) := hratio
        _ ≤ r * (r ^ k * Y n) := mul_le_mul_of_nonneg_left ih.2.2 hr0
        _ = r ^ (k + 1) * Y n := by rw [pow_succ]; ring
  have hzero : Tendsto (fun k => Y (n + k)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => (htail k).1) (fun k => (htail k).2.2)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (Y n)
  have hzero' : Tendsto (fun k => Y (k + n)) atTop (𝓝 0) := by
    simpa [Nat.add_comm] using hzero
  have hYlim : Tendsto Y atTop (𝓝 0) := (tendsto_add_atTop_iff_nat n).1 hzero'
  have hblim : Tendsto (fun k => floorSeq B k ^ q) atTop (𝓝 1) := by
    have ht := (Real.continuous_rpow_const hq0.le).continuousAt.tendsto.comp (tendsto_floorSeq hB)
    simpa only [Function.comp_def, Real.one_rpow] using ht
  have hsum := hYlim.add hblim
  simpa [Y] using hsum


private theorem freeEnergy_eq_zero_of_small_defect {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ)
    (hsmall : realMoment μ B h n q - floorSeq B n ^ q < B ^ q - 2) :
    freeEnergy μ B h = 0 := by
  have hG := tendsto_realMoment_of_small_defect hpos hmean hB h hq0 hq1 n hsmall
  have hlog : ∀ {k : ℕ}, 1 ≤ k →
      (∫ x, Real.log x ∂lawR μ B h k) ≤ realMoment μ B h k q / q := by
    intro k hk
    have hli := integrable_log_lawR_of hpos hmean hB h hk
    have hqi := integrable_realMoment hpos hmean hB h k hq0.le hq1.le
    have hpoint : ∀ᵐ x ∂lawR μ B h k, q * Real.log x ≤ x ^ q := by
      filter_upwards [ae_pos_lawR hpos hB h k] with x hx
      calc
        q * Real.log x ≤ q * (x ^ q / q) :=
          mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx.le hq0) hq0.le
        _ = x ^ q := by field_simp
    have hmono := integral_mono_ae (hli.const_mul q) hqi hpoint
    rw [integral_const_mul] at hmono
    exact (le_div_iff₀ hq0).2 (by simpa [realMoment, mul_comm] using hmono)
  have hscale : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have heq : (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) = fun k => ((1 : ℝ) / 2) ^ k := by
      ext k
      simp [inv_pow]
    rw [heq]
    exact ht
  have hupper : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹ * (realMoment μ B h k q / q))
      atTop (𝓝 0) := by
    have ht := hscale.mul (hG.div_const q)
    simpa using ht
  have hS := freeEnergy_tendsto_statement_aux hpos hmean hB h
  have hle : freeEnergy μ B h ≤ 0 := by
    apply le_of_tendsto_of_tendsto hS hupper
    filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
    exact mul_le_mul_of_nonneg_left (hlog hk) (by positivity)
  exact le_antisymm hle (freeEnergy_nonneg_aux hpos hmean hB h)

/-- Increasing the field multiplies the height-`n` fractional moment by at
most `exp (q * 2 ^ n * u)`, the fractional form of the field bound in
`source/critical.tex` lines 174–176. -/
private theorem realMoment_field_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    realMoment μ B (h + u) n q ≤
      Real.exp (q * ((2 : ℝ) ^ n * u)) * realMoment μ B h n q := by
  have hi (k : ℝ) : Integrable (fun e => (evalR B k n e) ^ q) (envMeasure μ n) := by
    apply (integrable_map_measure
      (Real.continuous_rpow_const hq0.le).measurable.aestronglyMeasurable
      (measurable_evalR B k n).aemeasurable).1
    rw [map_evalR_envMeasure μ B k n]
    exact integrable_realMoment hpos hmean hB k n hq0.le hq1.le
  have heval (k : ℝ) : (∫ e, (evalR B k n e) ^ q ∂envMeasure μ n) =
      realMoment μ B k n q := by
    unfold realMoment
    rw [← map_evalR_envMeasure μ B k n, integral_map (measurable_evalR B k n).aemeasurable
      (Real.continuous_rpow_const hq0.le).measurable.aestronglyMeasurable]
  have hpoint : ∀ᵐ e ∂envMeasure μ n, (evalR B (h + u) n e) ^ q ≤
      Real.exp (q * ((2 : ℝ) ^ n * u)) * (evalR B h n e) ^ q := by
    filter_upwards [ae_envPos hpos n] with e he
    have hp : 0 < evalR B h n e := evalR_pos (by linarith) h he
    have hp' : 0 < evalR B (h + u) n e := evalR_pos (by linarith) (h + u) he
    have hs := (evalR_shift_bounds (B := B) (h := h) (u := u) (show 1 < B by linarith) hu n e he).2
    have hexp : (Real.exp ((2 : ℝ) ^ n * u)) ^ q = Real.exp (q * ((2 : ℝ) ^ n * u)) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    calc
      (evalR B (h + u) n e) ^ q ≤
          (Real.exp ((2 : ℝ) ^ n * u) * evalR B h n e) ^ q :=
        Real.rpow_le_rpow hp'.le hs hq0.le
      _ = (Real.exp ((2 : ℝ) ^ n * u)) ^ q * (evalR B h n e) ^ q :=
        Real.mul_rpow (Real.exp_pos _).le hp.le
      _ = Real.exp (q * ((2 : ℝ) ^ n * u)) * (evalR B h n e) ^ q := by rw [hexp]
  have hI := integral_mono_ae (hi (h + u)) ((hi h).const_mul _) hpoint
  rw [integral_const_mul, heval (h + u), heval h] at hI
  exact hI

/-- At the critical point the fractional moment is bounded below by the
floor-centered barrier `floorSeq B n ^ q + B ^ q - 2`, proving the frozen
`barrier`. -/
theorem barrier_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {q : ℝ} (hq : theta B < q)
    (hq1 : q < 1) {n : ℕ} (hn : 1 ≤ n) :
    floorSeq B n ^ q + B ^ q - 2 ≤ realMoment μ B (criticalPoint μ B) n q := by
  have hq0 : 0 < q := (theta_pos hB).trans hq
  by_contra hnot
  push Not at hnot
  let hc := criticalPoint μ B
  let T := floorSeq B n ^ q + B ^ q - 2
  let G := realMoment μ B hc n q
  have hGT : G < T := hnot
  have hG0 : 0 < G := realMoment_pos hpos hmean hB hc n hq0.le hq1.le
  have hT0 : 0 < T := hG0.trans hGT
  have hratio : 1 < T / G := (one_lt_div hG0).2 hGT
  have hD : 0 < q * (2 : ℝ) ^ n := mul_pos hq0 (by positivity)
  let u := Real.log (T / G) / (2 * (q * (2 : ℝ) ^ n))
  have hu : 0 < u := div_pos (Real.log_pos hratio) (by positivity)
  have huarg : q * ((2 : ℝ) ^ n * u) = Real.log (T / G) / 2 := by
    dsimp [u]
    field_simp [ne_of_gt hD]
  have hfield := realMoment_field_le hpos hmean hB hc hu.le n hq0 hq1
  have hexp : Real.exp (Real.log (T / G) / 2) < T / G := by
    calc
      Real.exp (Real.log (T / G) / 2) < Real.exp (Real.log (T / G)) :=
        Real.exp_lt_exp.mpr (by have := Real.log_pos hratio; linarith)
      _ = T / G := Real.exp_log (div_pos hT0 hG0)
  have hK : Real.exp (q * ((2 : ℝ) ^ n * u)) * G < T := by
    calc
      Real.exp (q * ((2 : ℝ) ^ n * u)) * G = Real.exp (Real.log (T / G) / 2) * G := by rw [huarg]
      _ < (T / G) * G := mul_lt_mul_of_pos_right hexp hG0
      _ = T := by field_simp
  have hsmall : realMoment μ B (hc + u) n q - floorSeq B n ^ q < B ^ q - 2 := by
    have ht := hfield.trans_lt hK
    dsimp [G, T] at hK hGT ⊢
    linarith
  have hzero := freeEnergy_eq_zero_of_small_defect hpos hmean hB (hc + u) hq0 hq1 n hsmall
  have hlast := (criticalPoint_isGreatest_aux hpos hmean hB).2 hzero
  dsimp [hc] at hlast
  linarith

end DiamondPinning
