module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Hard
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The hard recursion, its free energy, and stochastic order

This file proves recurrences and bounds for the hard mean and free energy,
including their real-valued form, and proves monotonicity under tail
domination. It covers the hard free energy in `source/escape.tex`, lines
45–50, and the finiteness and comparison inputs to `escape:comparison` in
lines 156–189. The last lemma gives the finite first moment used by the first
claim of `escape:comparison`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The hard law at height `j + 1` is the pushforward of two independent
copies by `(x, y) ↦ x + y - 1`. -/
lemma hardLaw_succ (ν : Measure ℕ) (j : ℕ) :
    hardLaw ν (j + 1) = ((hardLaw ν j).prod (hardLaw ν j)).map
      (fun p : ℕ × ℕ => p.1 + p.2 - 1) := by
  rfl

/-- Every iterate of the hard recursion preserves the probability-measure property. -/
lemma hardLaw_isProbability (ν : Measure ℕ) [IsProbabilityMeasure ν] (j : ℕ) :
    IsProbabilityMeasure (hardLaw ν j) := by
  induction j with
  | zero =>
      change IsProbabilityMeasure ν
      infer_instance
  | succ j ih =>
      rw [hardLaw_succ]
      let _ := ih
      infer_instance

/-- The mean at height `j + 1` is the integral of `(x, y) ↦ x + y - 1`
over the product hard law at height `j`. -/
lemma hardMean_succ (ν : Measure ℕ) (j : ℕ) :
    hardMean ν (j + 1) = ∫⁻ p : ℕ × ℕ, ((p.1 + p.2 - 1 : ℕ) : ℝ≥0∞)
      ∂((hardLaw ν j).prod (hardLaw ν j)) := by
  rw [hardMean, hardLaw_succ]
  rw [lintegral_map (by fun_prop) (by fun_prop)]

/-- The hard mean grows by at most a factor of two at each recursion step. -/
lemma hardMean_succ_le (ν : Measure ℕ) [IsProbabilityMeasure ν] (j : ℕ) :
    hardMean ν (j + 1) ≤ 2 * hardMean ν j := by
  let _ := hardLaw_isProbability ν j
  rw [hardMean_succ]
  calc
    ∫⁻ p : ℕ × ℕ, ((p.1 + p.2 - 1 : ℕ) : ℝ≥0∞)
        ∂((hardLaw ν j).prod (hardLaw ν j)) ≤
      ∫⁻ p : ℕ × ℕ, (p.1 : ℝ≥0∞) + p.2
        ∂((hardLaw ν j).prod (hardLaw ν j)) := by
          apply lintegral_mono
          intro p
          rcases p with ⟨a, b⟩
          dsimp
          exact_mod_cast Nat.sub_le (a + b) 1
    _ = 2 * hardMean ν j := by
      rw [lintegral_add_left (by fun_prop)]
      rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
      simp [hardMean, two_mul]


/-- One hard recursion step decreases the mean by at most the defect from doubling it. -/
lemma hardMean_succ_ge (ν : Measure ℕ) [IsProbabilityMeasure ν] (j : ℕ) :
    2 * hardMean ν j - 1 ≤ hardMean ν (j + 1) := by
  let _ := hardLaw_isProbability ν j
  have hadd : ∫⁻ p : ℕ × ℕ, (p.1 : ℝ≥0∞) + p.2
      ∂((hardLaw ν j).prod (hardLaw ν j)) = 2 * hardMean ν j := by
    rw [lintegral_add_left (by fun_prop)]
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
    simp [hardMean, two_mul]
  rw [hardMean_succ]
  calc
    2 * hardMean ν j - 1 =
        (∫⁻ p : ℕ × ℕ, (p.1 : ℝ≥0∞) + p.2 ∂((hardLaw ν j).prod (hardLaw ν j))) -
          ∫⁻ _p : ℕ × ℕ, (1 : ℝ≥0∞) ∂((hardLaw ν j).prod (hardLaw ν j)) := by
      rw [hadd]
      simp
    _ ≤ ∫⁻ p : ℕ × ℕ, ((p.1 : ℝ≥0∞) + p.2) - 1
        ∂((hardLaw ν j).prod (hardLaw ν j)) :=
      lintegral_sub_le _ _ (by fun_prop)
    _ ≤ ∫⁻ p : ℕ × ℕ, ((p.1 + p.2 - 1 : ℕ) : ℝ≥0∞)
        ∂((hardLaw ν j).prod (hardLaw ν j)) := by
      apply lintegral_mono
      rintro ⟨a, b⟩
      dsimp
      rw [ENNReal.natCast_sub]
      simp

/-- The normalized centered hard mean `2⁻ʲ (hardMean ν j - 1)` increases with `j`. -/
lemma centeredHardMean_mono (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    Monotone (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * (hardMean ν j - 1)) := by
  apply monotone_nat_of_le_succ
  intro j
  have hrec : 2 * (hardMean ν j - 1) ≤ hardMean ν (j + 1) - 1 := by
    have h := tsub_le_tsub_right (hardMean_succ_ge ν j) 1
    convert h using 1
    rw [ENNReal.mul_sub (by intros; norm_num), tsub_tsub]
    norm_num
  calc
    ((2 : ℝ≥0∞) ^ j)⁻¹ * (hardMean ν j - 1) =
        ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * (2 * (hardMean ν j - 1)) := by
      rw [pow_succ, ENNReal.mul_inv (by simp) (by simp)]
      calc
        ((2 : ℝ≥0∞) ^ j)⁻¹ * (hardMean ν j - 1) =
            ((2 : ℝ≥0∞) ^ j)⁻¹ * 2⁻¹ * 2 * (hardMean ν j - 1) := by
          calc
            ((2 : ℝ≥0∞) ^ j)⁻¹ * (hardMean ν j - 1) =
                ((2 : ℝ≥0∞) ^ j)⁻¹ * (2⁻¹ * 2) * (hardMean ν j - 1) := by
              rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
              simp
            _ = ((2 : ℝ≥0∞) ^ j)⁻¹ * 2⁻¹ * 2 * (hardMean ν j - 1) := by
              ac_rfl
        _ = (((2 : ℝ≥0∞) ^ j)⁻¹ * 2⁻¹) * (2 * (hardMean ν j - 1)) := by
          ac_rfl
    _ ≤ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * (hardMean ν (j + 1) - 1) := by
      gcongr

/-- The normalized hard means decrease to `hardFreeEnergy ν`; this proves the
frozen `hardFreeEnergy_tendsto`. -/
theorem hardFreeEnergy_tendsto_aux (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    Antitone (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j) ∧
      Tendsto (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j) atTop
        (𝓝 (hardFreeEnergy ν)) := by
  have hanti : Antitone (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j) := by
    apply antitone_nat_of_succ_le
    intro j
    rw [pow_succ, ENNReal.mul_inv (by simp) (by simp)]
    calc
      ((2 : ℝ≥0∞) ^ j)⁻¹ * 2⁻¹ * hardMean ν (j + 1) =
          ((2 : ℝ≥0∞) ^ j)⁻¹ * (2⁻¹ * hardMean ν (j + 1)) := mul_assoc _ _ _
      _ ≤ ((2 : ℝ≥0∞) ^ j)⁻¹ * (2⁻¹ * (2 * hardMean ν j)) := by
        gcongr
        exact hardMean_succ_le ν j
      _ = ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j := by
        calc
          ((2 : ℝ≥0∞) ^ j)⁻¹ * (2⁻¹ * (2 * hardMean ν j)) =
              ((2 : ℝ≥0∞) ^ j)⁻¹ * (2⁻¹ * 2) * hardMean ν j := by ac_rfl
          _ = ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j := by
            rw [ENNReal.inv_mul_cancel] <;> norm_num
  refine ⟨hanti, ?_⟩
  exact tendsto_atTop_iInf hanti


/-- Every normalized centered hard mean is a lower bound for `hardFreeEnergy ν`;
this proves the frozen `hardFreeEnergy_ge`. -/
theorem hardFreeEnergy_ge_aux (ν : Measure ℕ) [IsProbabilityMeasure ν] (j : ℕ) :
    ((2 : ℝ≥0∞) ^ j)⁻¹ * (hardMean ν j - 1) ≤ hardFreeEnergy ν := by
  have hanti := (hardFreeEnergy_tendsto_aux ν).1
  have hmono := centeredHardMean_mono ν
  apply le_iInf
  intro k
  calc
    ((2 : ℝ≥0∞) ^ j)⁻¹ * (hardMean ν j - 1) ≤
        ((2 : ℝ≥0∞) ^ (max j k))⁻¹ * (hardMean ν (max j k) - 1) :=
      hmono (le_max_left _ _)
    _ ≤ ((2 : ℝ≥0∞) ^ (max j k))⁻¹ * hardMean ν (max j k) := by
      gcongr
      exact tsub_le_self
    _ ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ * hardMean ν k := hanti (le_max_right _ _)


/-- Finite initial hard mean gives finite hard means at every height, finite hard
free energy, and convergence of their real normalizations; this proves the
frozen `hardFreeEnergy_real`. -/
theorem hardFreeEnergy_real_aux (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hfin : hardMean ν 0 ≠ ∞) :
    (∀ j, hardMean ν j ≠ ∞) ∧ hardFreeEnergy ν ≠ ∞ ∧
      Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹ * (hardMean ν j).toReal) atTop
        (𝓝 (hardFreeEnergy ν).toReal) := by
  have hm : ∀ j, hardMean ν j ≠ ∞ := by
    intro j
    induction j with
    | zero => exact hfin
    | succ j ih =>
        exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) ih) (hardMean_succ_le ν j)
  have hFle : hardFreeEnergy ν ≤ hardMean ν 0 := by
    have h := iInf_le (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j) 0
    simpa [hardFreeEnergy] using h
  have hF : hardFreeEnergy ν ≠ ∞ := ne_top_of_le_ne_top hfin hFle
  refine ⟨hm, hF, ?_⟩
  have ht := (ENNReal.tendsto_toReal hF).comp (hardFreeEnergy_tendsto_aux ν).2
  convert ht using 1
  ext j
  simp [ENNReal.toReal_mul]



/-! ### Tail domination -/

/-- Tail domination of integer laws gives domination of integrals of every
nonnegative monotone real function. -/
lemma lintegral_ofReal_mono_of_tail {ν ρ : Measure ℕ}
    (htail : ∀ k : ℕ, ν {y | k ≤ y} ≤ ρ {y | k ≤ y})
    (f : ℕ → ℝ) (hf₀ : ∀ y, 0 ≤ f y) (hf : Monotone f) :
    (∫⁻ y, ENNReal.ofReal (f y) ∂ν) ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂ρ := by
  rw [lintegral_eq_lintegral_meas_le ν
    (Eventually.of_forall hf₀) (by fun_prop)]
  rw [lintegral_eq_lintegral_meas_le ρ
    (Eventually.of_forall hf₀) (by fun_prop)]
  apply lintegral_mono
  intro t
  let S : Set ℕ := {y | t ≤ f y}
  have hSupper : IsUpperSet S := by
    intro a b hab ha
    exact ha.trans (hf hab)
  change ν S ≤ ρ S
  rcases hSupper.eq_empty_or_Ici with hS | ⟨k, hS⟩
  · simp [hS]
  · rw [hS]
    exact htail k

/-- Tail domination of integer laws gives domination of integrals of every
monotone natural-valued function. -/
lemma lintegral_mono_of_tail {ν ρ : Measure ℕ}
    (htail : ∀ k : ℕ, ν {y | k ≤ y} ≤ ρ {y | k ≤ y})
    (f : ℕ → ℕ) (hf : Monotone f) :
    (∫⁻ y, (f y : ℝ≥0∞) ∂ν) ≤ ∫⁻ y, (f y : ℝ≥0∞) ∂ρ := by
  have h := lintegral_ofReal_mono_of_tail htail (fun y => (f y : ℝ))
    (fun y => by positivity) (fun a b hab => by
      change (f a : ℝ) ≤ (f b : ℝ)
      exact_mod_cast hf hab)
  simpa only [ENNReal.ofReal_natCast] using h

/-- Tail domination of integer laws gives domination of lower integrals of
every monotone extended-nonnegative function. -/
lemma lintegral_ennreal_mono_of_tail {ν ρ : Measure ℕ}
    (htail : ∀ k : ℕ, ν {y | k ≤ y} ≤ ρ {y | k ≤ y})
    (f : ℕ → ℝ≥0∞) (hf : Monotone f) :
    (∫⁻ y, f y ∂ν) ≤ ∫⁻ y, f y ∂ρ := by
  let trunc : ℕ → ℕ → ℝ := fun N y => (min (N : ℝ≥0∞) (f y)).toReal
  have htrunc₀ (N y : ℕ) : 0 ≤ trunc N y := ENNReal.toReal_nonneg
  have htrunc_mono (N : ℕ) : Monotone (trunc N) := by
    intro a b hab
    apply ENNReal.toReal_mono
      (ne_top_of_le_ne_top (by simp : (N : ℝ≥0∞) ≠ ∞) (min_le_left _ _))
    exact min_le_min le_rfl (hf hab)
  have htrunc_ofReal (N y : ℕ) :
      ENNReal.ofReal (trunc N y) = min (N : ℝ≥0∞) (f y) := by
    dsimp [trunc]
    exact ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top (by simp : (N : ℝ≥0∞) ≠ ∞) (min_le_left _ _))
  have hsup (y : ℕ) : (⨆ N : ℕ, min (N : ℝ≥0∞) (f y)) = f y := by
    apply le_antisymm
    · exact iSup_le fun N => min_le_right _ _
    · by_cases htop : f y = ∞
      · rw [htop, ← ENNReal.iSup_natCast]
        apply iSup_mono
        intro N
        rw [min_eq_left (le_iSup (fun n : ℕ => (n : ℝ≥0∞)) N)]
      · let N := ⌈(f y).toReal⌉₊
        have hfN : f y ≤ (N : ℝ≥0∞) := by
          apply (ENNReal.toReal_le_toReal htop (by simp)).1
          simpa [N] using Nat.le_ceil (f y).toReal
        calc
          f y = min (N : ℝ≥0∞) (f y) := (min_eq_right hfN).symm
          _ ≤ ⨆ N : ℕ, min (N : ℝ≥0∞) (f y) := by
            refine le_iSup_of_le N ?_
            exact le_rfl
  rw [show (fun y => f y) = (fun y => ⨆ N : ℕ, min (N : ℝ≥0∞) (f y)) from
    funext fun y => (hsup y).symm]
  have hfamily : Monotone (fun (N : ℕ) (y : ℕ) => min (N : ℝ≥0∞) (f y)) := by
    intro N M hNM y
    exact min_le_min (by exact_mod_cast hNM) le_rfl
  rw [lintegral_iSup (μ := ν) (fun N => by fun_prop) hfamily]
  rw [lintegral_iSup (μ := ρ) (fun N => by fun_prop) hfamily]
  apply iSup_mono
  intro N
  have h := lintegral_ofReal_mono_of_tail htail (trunc N) (htrunc₀ N) (htrunc_mono N)
  simpa only [htrunc_ofReal] using h

/-- Componentwise tail domination gives integral domination for separately
monotone functions on a product of integer laws. -/
lemma lintegral_prod_mono_of_tail {ν₁ ρ₁ ν₂ ρ₂ : Measure ℕ}
    (h₁ : ∀ k : ℕ, ν₁ {y | k ≤ y} ≤ ρ₁ {y | k ≤ y})
    (h₂ : ∀ k : ℕ, ν₂ {y | k ≤ y} ≤ ρ₂ {y | k ≤ y})
    (f : ℕ × ℕ → ℕ) (hf₁ : ∀ b, Monotone fun a => f (a, b))
    (hf₂ : ∀ a, Monotone fun b => f (a, b)) :
    (∫⁻ p, (f p : ℝ≥0∞) ∂(ν₁.prod ν₂)) ≤
      ∫⁻ p, (f p : ℝ≥0∞) ∂(ρ₁.prod ρ₂) := by
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    (∫⁻ a, ∫⁻ b, (f (a, b) : ℝ≥0∞) ∂ν₂ ∂ν₁) ≤
        ∫⁻ a, ∫⁻ b, (f (a, b) : ℝ≥0∞) ∂ρ₂ ∂ν₁ := by
      apply lintegral_mono
      intro a
      exact lintegral_mono_of_tail h₂ _ (hf₂ a)
    _ ≤ ∫⁻ a, ∫⁻ b, (f (a, b) : ℝ≥0∞) ∂ρ₂ ∂ρ₁ := by
      apply lintegral_ennreal_mono_of_tail h₁
      intro a₁ a₂ ha
      apply lintegral_mono
      intro b
      change (f (a₁, b) : ℝ≥0∞) ≤ (f (a₂, b) : ℝ≥0∞)
      exact_mod_cast hf₁ b ha

/-- The natural-valued indicator of the upper tail `{k, k + 1, …}`. -/
def tailFun (k y : ℕ) : ℕ := if k ≤ y then 1 else 0

/-- The upper-tail indicator `tailFun k` is monotone. -/
lemma tailFun_mono (k : ℕ) : Monotone (tailFun k) := by
  intro a b hab
  by_cases hka : k ≤ a
  · have hkb : k ≤ b := hka.trans hab
    simp [tailFun, hka, hkb]
  · simp [tailFun, hka]

/-- The mass of an upper tail is the lower integral of its natural-valued indicator. -/
lemma tail_as_lintegral (ν : Measure ℕ) (k : ℕ) :
    ν {y | k ≤ y} = ∫⁻ y, (tailFun k y : ℝ≥0∞) ∂ν := by
  classical
  calc
    ν {y | k ≤ y} = ∫⁻ _y in {y | k ≤ y}, (1 : ℝ≥0∞) ∂ν := by simp
    _ = ∫⁻ y, Set.indicator {y | k ≤ y} (fun _ => (1 : ℝ≥0∞)) y ∂ν :=
      (lintegral_indicator measurableSet_Ici (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∫⁻ y, (tailFun k y : ℝ≥0∞) ∂ν := by
      congr 1 with y
      simp [tailFun, Set.indicator]

/-- Tail domination is preserved by every iterate of the hard law and implies
domination of monotone integrals. -/
lemma lintegral_hardLaw_mono_of_tail {ν ρ : Measure ℕ}
    (h : ∀ k : ℕ, ν {y | k ≤ y} ≤ ρ {y | k ≤ y}) :
    ∀ (j : ℕ) (f : ℕ → ℕ), Monotone f →
      (∫⁻ y, (f y : ℝ≥0∞) ∂hardLaw ν j) ≤
        ∫⁻ y, (f y : ℝ≥0∞) ∂hardLaw ρ j := by
  intro j
  induction j with
  | zero =>
      intro f hf
      exact lintegral_mono_of_tail h f hf
  | succ j ih =>
      have htail : ∀ k : ℕ, hardLaw ν j {y | k ≤ y} ≤ hardLaw ρ j {y | k ≤ y} := by
        intro k
        rw [tail_as_lintegral, tail_as_lintegral]
        exact ih (tailFun k) (tailFun_mono k)
      intro f hf
      rw [hardLaw_succ, hardLaw_succ, lintegral_map (by fun_prop) (by fun_prop),
        lintegral_map (by fun_prop) (by fun_prop)]
      exact lintegral_prod_mono_of_tail htail htail _
        (fun b a₁ a₂ ha => hf (by dsimp; omega))
        (fun a b₁ b₂ hb => hf (by dsimp; omega))

/-- Every iterate of the hard recursion preserves tail domination between integer laws. -/
lemma hardLaw_tail_mono {ν ρ : Measure ℕ}
    (h : ∀ k : ℕ, ν {y | k ≤ y} ≤ ρ {y | k ≤ y}) (j k : ℕ) :
    hardLaw ν j {y | k ≤ y} ≤ hardLaw ρ j {y | k ≤ y} := by
  rw [tail_as_lintegral, tail_as_lintegral]
  exact lintegral_hardLaw_mono_of_tail h j (tailFun k) (tailFun_mono k)

/-- The mean at every hard-recursion height is monotone with respect to tail domination. -/
lemma hardMean_mono_of_tail {ν ρ : Measure ℕ}
    (h : ∀ k : ℕ, ν {y | k ≤ y} ≤ ρ {y | k ≤ y}) (j : ℕ) :
    hardMean ν j ≤ hardMean ρ j := by
  exact lintegral_hardLaw_mono_of_tail h j id monotone_id

/-- The hard free energy is monotone with respect to tail domination of the initial integer laws. -/
lemma hardFreeEnergy_mono_of_tail {ν ρ : Measure ℕ}
    (h : ∀ k : ℕ, ν {y | k ≤ y} ≤ ρ {y | k ≤ y}) :
    hardFreeEnergy ν ≤ hardFreeEnergy ρ := by
  apply le_iInf
  intro j
  calc
    hardFreeEnergy ν ≤ ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j :=
      iInf_le (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j) j
    _ ≤ ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ρ j := by
      gcongr
      exact hardMean_mono_of_tail h j


/-- The deterministic-floor hard law has finite initial mean: positivity and
unit mean of `μ` supply the first claim of `escape:comparison`. -/
lemma floorHardMean_ne_top {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    hardMean (floorHardLaw μ B h n) 0 ≠ ∞ := by
  let _ : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hb : 0 < floorSeq B n :=
    (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hb1 : floorSeq B n < 1 := floorSeq_lt_one hB n
  have ha : 0 < Real.log (B / floorSeq B n) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hb]
    nlinarith
  have hab : 0 < Real.log (B / floorSeq B n) * floorSeq B n := mul_pos ha hb
  have hi := integrable_lawR_of hpos hmean hB h n
  rw [hardMean, floorHardLaw]
  change (∫⁻ y, (y : ℝ≥0∞) ∂(floorHardLaw μ B h n)) ≠ ∞
  rw [floorHardLaw]
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply ne_top_of_le_ne_top (b := ∫⁻ r, ENNReal.ofReal
    ((Real.log (B / floorSeq B n) * floorSeq B n)⁻¹ * r) ∂(lawR μ B h n))
    (hi.const_mul _).lintegral_lt_top.ne
  apply lintegral_mono_ae
  filter_upwards [ae_pos_lawR hpos hB h n] with r hr
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hconst : 0 ≤ (Real.log (B / floorSeq B n) * floorSeq B n)⁻¹ :=
    inv_nonneg.mpr hab.le
  by_cases hq0 : 0 ≤ Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)
  · calc
      (⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊ : ℝ) ≤
          Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n) := Nat.floor_le hq0
      _ ≤ (Real.log (B / floorSeq B n) * floorSeq B n)⁻¹ * r := by
        rw [div_le_iff₀ ha]
        calc
          Real.log (r / floorSeq B n) ≤ r / floorSeq B n - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hr hb)
          _ ≤ r / floorSeq B n := by linarith
          _ = (Real.log (B / floorSeq B n) * floorSeq B n)⁻¹ * r *
              Real.log (B / floorSeq B n) := by
            field_simp
  · rw [Nat.floor_of_nonpos (le_of_not_ge hq0)]
    simpa using mul_nonneg hconst hr.le

end DiamondPinning
