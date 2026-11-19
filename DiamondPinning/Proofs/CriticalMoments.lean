module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Moments
public import DiamondPinning.Model.FreeEnergy
public import DiamondPinning.Proofs.JensenBarrier
public import DiamondPinning.Statements.Env
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Set
open scoped Topology BigOperators

/-- A binary tree with independent blocks at its leaves. -/
@[reducible] def BlockTree (α : Type*) : ℕ → Type _
  | 0 => α
  | k + 1 => BlockTree α k × BlockTree α k

instance blockTreeMeasurableSpace {α : Type*} [MeasurableSpace α] :
    (k : ℕ) → MeasurableSpace (BlockTree α k)
  | 0 => ‹MeasurableSpace α›
  | k + 1 => @Prod.instMeasurableSpace _ _ (blockTreeMeasurableSpace k) (blockTreeMeasurableSpace k)

/-- The product law of the (2^k) blocks. -/
noncomputable def blockMeasure {α : Type*} [MeasurableSpace α] (ν : Measure α) :
    (k : ℕ) → Measure (BlockTree α k)
  | 0 => ν
  | k + 1 => (blockMeasure ν k).prod (blockMeasure ν k)

instance blockMeasureProbability {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] :
    (k : ℕ) → IsProbabilityMeasure (blockMeasure ν k)
  | 0 => inferInstanceAs (IsProbabilityMeasure ν)
  | k + 1 =>
    haveI := blockMeasureProbability ν k
    inferInstanceAs (IsProbabilityMeasure ((blockMeasure ν k).prod (blockMeasure ν k)))

/-- Cut a height-(n+k) environment at the roots of its height-(n) blocks. -/
def envBlocks (n : ℕ) : (k : ℕ) → Env (n + k) ≃ᵐ BlockTree (Env n) k
  | 0 => MeasurableEquiv.refl _
  | k + 1 => (envBlocks n k).prodCongr (envBlocks n k)

theorem measurePreserving_envBlocks (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (k : ℕ) → MeasurePreserving (envBlocks n k) (envMeasure μ (n + k))
      (blockMeasure (envMeasure μ n) k)
  | 0 => MeasurePreserving.id _
  | k + 1 => by
    refine ⟨(envBlocks n (k + 1)).measurable, ?_⟩
    change Measure.map (Prod.map (envBlocks n k) (envBlocks n k))
      ((envMeasure μ (n + k)).prod (envMeasure μ (n + k))) =
        (blockMeasure (envMeasure μ n) k).prod (blockMeasure (envMeasure μ n) k)
    rw [← Measure.map_prod_map _ _ (envBlocks n k).measurable (envBlocks n k).measurable,
      (measurePreserving_envBlocks μ n k).map_eq]

private def marked {α : Type*} (S : Set α) : (k : ℕ) → Set (BlockTree α k)
  | 0 => S
  | k + 1 => Prod.fst ⁻¹' marked S k ∪ Prod.snd ⁻¹' marked S k

private theorem measurableSet_marked {α : Type*} [MeasurableSpace α] {S : Set α}
    (hS : MeasurableSet S) : (k : ℕ) → MeasurableSet (marked S k)
  | 0 => hS
  | k + 1 => (measurableSet_marked hS k).preimage measurable_fst |>.union
      ((measurableSet_marked hS k).preimage measurable_snd)

private theorem blockMeasure_marked_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {S : Set α} (hS : MeasurableSet S) :
    ∀ k, (blockMeasure ν k).real (marked S k) ≤ (2 : ℝ) ^ k * ν.real S := by
  intro k
  induction k with
  | zero =>
    rw [pow_zero, one_mul]
    exact le_rfl
  | succ k ih =>
    let τ := blockMeasure ν k
    have hm := measurableSet_marked hS k
    let : IsProbabilityMeasure τ := blockMeasureProbability ν k
    change (τ.prod τ).real (Prod.fst ⁻¹' marked S k ∪ Prod.snd ⁻¹' marked S k) ≤ _
    have h₁ : (τ.prod τ).real (Prod.fst ⁻¹' marked S k) = τ.real (marked S k) := by
      rw [← map_measureReal_apply measurable_fst hm, Measure.map_fst_prod]
      simp
    have h₂ : (τ.prod τ).real (Prod.snd ⁻¹' marked S k) = τ.real (marked S k) := by
      rw [← map_measureReal_apply measurable_snd hm, Measure.map_snd_prod]
      simp
    refine (measureReal_union_le _ _).trans ?_
    rw [h₁, h₂, pow_succ]
    change τ.real (marked S k) ≤ _ at ih
    linarith

private noncomputable def blockEval {α : Type*} (B : ℝ) (f : α → ℝ) :
    (k : ℕ) → BlockTree α k → ℝ
  | 0 => f
  | k + 1 => fun e => (blockEval B f k e.1 * blockEval B f k e.2 + (B - 1)) / B

private theorem blockEval_envBlocks (B h : ℝ) (n : ℕ) :
    ∀ k (e : Env (n + k)), blockEval B (evalR B h n) k (envBlocks n k e) =
      evalR B h (n + k) e := by
  intro k
  induction k with
  | zero => intro e; rfl
  | succ k ih =>
    intro e
    change (blockEval B (evalR B h n) k (envBlocks n k e.1) *
      blockEval B (evalR B h n) k (envBlocks n k e.2) + (B - 1)) / B =
        (evalR B h (n + k) e.1 * evalR B h (n + k) e.2 + (B - 1)) / B
    rw [ih, ih]

private theorem measurable_blockEval {α : Type*} [MeasurableSpace α]
    (B : ℝ) {f : α → ℝ} (hf : Measurable f) :
    (k : ℕ) → Measurable (blockEval B f k)
  | 0 => hf
  | k + 1 =>
    have hm := measurable_blockEval B hf k
    (((hm.comp measurable_fst).mul (hm.comp measurable_snd)).add_const (B - 1)).div_const B

private theorem integrable_log_blockEval {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    Integrable (fun e => Real.log (blockEval B (evalR B h n) k e))
      (blockMeasure (envMeasure μ n) k) := by
  rw [← (measurePreserving_envBlocks μ n k).map_eq]
  apply (integrable_map_measure (Real.measurable_log.comp
    (measurable_blockEval B (measurable_evalR B h n) k)).aestronglyMeasurable
    (envBlocks n k).measurable.aemeasurable).2
  have heq : (fun e => Real.log (blockEval B (evalR B h n) k (envBlocks n k e))) =
      fun e => Real.log (evalR B h (n + k) e) := by
    funext e
    rw [blockEval_envBlocks]
  change Integrable (fun e => Real.log (blockEval B (evalR B h n) k (envBlocks n k e))) _
  rw [heq]
  apply (integrable_map_measure Real.measurable_log.aestronglyMeasurable
    (measurable_evalR B h (n + k)).aemeasurable).1
  rw [map_evalR_envMeasure μ B h (n + k)]
  exact integrable_log_lawR_of hpos hmean hB h (by omega)

private theorem ae_floor_blockEval {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n k : ℕ) :
    ∀ᵐ e ∂blockMeasure (envMeasure μ n) k, floorSeq B n ≤ blockEval B (evalR B h n) k e := by
  have mp := measurePreserving_envBlocks μ n k
  have hm : MeasurableSet {e | floorSeq B n ≤ blockEval B (evalR B h n) k e} :=
    measurableSet_le measurable_const (measurable_blockEval B (measurable_evalR B h n) k)
  have hh := ae_floorSeq_le_lawR hpos hB h (n + k)
  have heval : MeasurePreserving (evalR B h (n + k)) (envMeasure μ (n + k)) (lawR μ B h (n + k)) :=
    ⟨measurable_evalR B h (n + k), map_evalR_envMeasure μ B h (n + k)⟩
  rw [← mp.map_eq]
  apply (ae_map_iff mp.measurable.aemeasurable hm).2
  filter_upwards [heval.quasiMeasurePreserving.ae hh] with e he
  rw [blockEval_envBlocks]
  exact (floorSeq_monotone hB (Nat.le_add_right n k)).trans he

/-- The log excess above the fixed floor at a node with a favorable descendant. -/
private noncomputable def markedExcess {α : Type*} (S : Set α) (B b : ℝ) (f : α → ℝ)
    (k : ℕ) : BlockTree α k → ℝ :=
  (marked S k).indicator (fun e => Real.log (blockEval B f k e) - Real.log b)

private theorem markedExcess_step {α : Type*} {S : Set α} {B b : ℝ} {f : α → ℝ}
    (hB : 0 < B) (hc : 0 ≤ B - 1) (hb : 0 < b) (k : ℕ) (e : BlockTree α (k + 1))
    (h₁ : b ≤ blockEval B f k e.1) (h₂ : b ≤ blockEval B f k e.2) :
    markedExcess S B b f k e.1 + markedExcess S B b f k e.2 -
        Real.log (B / b) * (marked S (k + 1)).indicator (fun _ => (1 : ℝ)) e ≤
      markedExcess S B b f (k + 1) e := by
  classical
  by_cases he : e ∈ marked S (k + 1)
  · have hx := hb.trans_le h₁
    have hy := hb.trans_le h₂
    have hxy := mul_pos hx hy
    have hlog : Real.log (blockEval B f k e.1 * blockEval B f k e.2 / B) ≤
        Real.log (blockEval B f (k + 1) e) := by
      apply Real.log_le_log (div_pos hxy hB)
      change _ ≤ (_ + (B - 1)) / B
      gcongr
      linarith
    rw [Real.log_div hxy.ne' hB.ne', Real.log_mul hx.ne' hy.ne'] at hlog
    have hchild (u : BlockTree α k) (hu : b ≤ blockEval B f k u) :
        markedExcess S B b f k u ≤ Real.log (blockEval B f k u) - Real.log b := by
      by_cases hum : u ∈ marked S k
      · simp [markedExcess, Set.indicator_of_mem hum]
      · simpa [markedExcess, Set.indicator_of_notMem hum] using
          sub_nonneg.mpr (Real.log_le_log hb hu)
    have hparent : markedExcess S B b f (k + 1) e =
        Real.log (blockEval B f (k + 1) e) - Real.log b := Set.indicator_of_mem he _
    rw [hparent, Set.indicator_of_mem he, mul_one, Real.log_div hB.ne' hb.ne']
    linarith [hchild e.1 h₁, hchild e.2 h₂]
  · have hleft : e.1 ∉ marked S k := fun hm => he (Or.inl hm)
    have hright : e.2 ∉ marked S k := fun hm => he (Or.inr hm)
    simp [markedExcess, Set.indicator_of_notMem he, Set.indicator_of_notMem hleft,
      Set.indicator_of_notMem hright]

private theorem markedExcess_integral_step {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {S : Set α} (hS : MeasurableSet S)
    {B b : ℝ} {f : α → ℝ} (hB : 0 < B) (hc : 0 ≤ B - 1) (hb : 0 < b)
    (hlog : ∀ k, Integrable (fun e => Real.log (blockEval B f k e)) (blockMeasure ν k))
    (hfloor : ∀ k, ∀ᵐ e ∂blockMeasure ν k, b ≤ blockEval B f k e) (k : ℕ) :
    2 * (∫ e, markedExcess S B b f k e ∂blockMeasure ν k) -
        Real.log (B / b) * (blockMeasure ν (k + 1)).real (marked S (k + 1)) ≤
      ∫ e, markedExcess S B b f (k + 1) e ∂blockMeasure ν (k + 1) := by
  let τ := blockMeasure ν k
  let : IsProbabilityMeasure τ := blockMeasureProbability ν k
  let g := markedExcess S B b f k
  have hi (j : ℕ) : Integrable (markedExcess S B b f j) (blockMeasure ν j) :=
    ((hlog j).sub (integrable_const _)).indicator (measurableSet_marked hS j)
  have hf : MeasurePreserving Prod.fst (τ.prod τ) τ := measurePreserving_fst
  have hs : MeasurePreserving Prod.snd (τ.prod τ) τ := measurePreserving_snd
  have hi₁ : Integrable (fun e : BlockTree α k × BlockTree α k => g e.1) (τ.prod τ) :=
    hf.integrable_comp_of_integrable (hi k)
  have hi₂ : Integrable (fun e : BlockTree α k × BlockTree α k => g e.2) (τ.prod τ) :=
    hs.integrable_comp_of_integrable (hi k)
  have hum : @MeasurableSet (BlockTree α k × BlockTree α k) _ (marked S (k + 1)) :=
    measurableSet_marked hS (k + 1)
  have hi₃ : Integrable ((marked S (k + 1)).indicator (fun _ => (1 : ℝ))) (τ.prod τ) :=
    (integrable_const (μ := τ.prod τ) (1 : ℝ)).indicator hum
  have hw : ∀ᵐ e ∂τ.prod τ, g e.1 + g e.2 -
      Real.log (B / b) * (marked S (k + 1)).indicator (fun _ => (1 : ℝ)) e ≤
        markedExcess S B b f (k + 1) e := by
    filter_upwards [hf.quasiMeasurePreserving.ae (hfloor k), hs.quasiMeasurePreserving.ae (hfloor k)] with e h₁ h₂
    exact markedExcess_step hB hc hb k e h₁ h₂
  have hI := integral_mono_ae ((hi₁.add hi₂).sub (hi₃.const_mul _)) (hi (k + 1)) hw
  change (∫ e : BlockTree α k × BlockTree α k, (g e.1 + g e.2) -
      Real.log (B / b) * (marked S (k + 1)).indicator (fun _ => (1 : ℝ)) e ∂τ.prod τ) ≤
    _ at hI
  have hi₁₂ : Integrable (fun e : BlockTree α k × BlockTree α k => g e.1 + g e.2)
      (τ.prod τ) := hi₁.add hi₂
  have hi₃' : Integrable (fun e : BlockTree α k × BlockTree α k =>
      Real.log (B / b) * (marked S (k + 1)).indicator (fun _ => (1 : ℝ)) e) (τ.prod τ) :=
    hi₃.const_mul _
  have hmI : (∫ e : BlockTree α k × BlockTree α k,
      (marked S (k + 1)).indicator (fun _ => (1 : ℝ)) e ∂τ.prod τ) =
      (τ.prod τ).real (marked S (k + 1)) := integral_indicator_one hum
  rw [integral_sub hi₁₂ hi₃', integral_add hi₁ hi₂, integral_const_mul, hmI] at hI
  have ie₁ : (∫ e : BlockTree α k × BlockTree α k, g e.1 ∂τ.prod τ) =
      ∫ e, g e ∂τ := by
    have he := integral_map (μ := τ.prod τ) (φ := Prod.fst) (f := g)
      measurable_fst.aemeasurable (by rw [hf.map_eq]; exact (hi k).aestronglyMeasurable)
    rw [hf.map_eq] at he
    exact he.symm
  have ie₂ : (∫ e : BlockTree α k × BlockTree α k, g e.2 ∂τ.prod τ) =
      ∫ e, g e ∂τ := by
    have he := integral_map (μ := τ.prod τ) (φ := Prod.snd) (f := g)
      measurable_snd.aemeasurable (by rw [hs.map_eq]; exact (hi k).aestronglyMeasurable)
    rw [hs.map_eq] at he
    exact he.symm
  rw [ie₁, ie₂, ← two_mul] at hI
  exact hI

private theorem markedExcess_integral_le_log {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {S : Set (Env n)} (hS : MeasurableSet S) (k : ℕ) :
    (∫ e, markedExcess S B (floorSeq B n) (evalR B h n) k e
      ∂blockMeasure (envMeasure μ n) k) ≤ logMoment μ B h (n + k) - Real.log (floorSeq B n) := by
  let b := floorSeq B n
  have hi := (integrable_log_blockEval hpos hmean hB h hn k).sub (integrable_const (Real.log b))
  have hle := integral_mono_ae (hi.indicator (measurableSet_marked hS k)) hi
    (show ∀ᵐ e ∂blockMeasure (envMeasure μ n) k, markedExcess S B b (evalR B h n) k e ≤
      Real.log (blockEval B (evalR B h n) k e) - Real.log b from by
      filter_upwards [ae_floor_blockEval hpos hB h n k] with e he
      by_cases hm : e ∈ marked S k
      · simp [markedExcess, Set.indicator_of_mem hm]
      · simpa [markedExcess, Set.indicator_of_notMem hm] using sub_nonneg.mpr
          (Real.log_le_log ((floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)) he))
  refine hle.trans_eq ?_
  change (∫ e, Real.log (blockEval B (evalR B h n) k e) - Real.log b
    ∂blockMeasure (envMeasure μ n) k) = _
  rw [integral_sub (integrable_log_blockEval hpos hmean hB h hn k) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  rw [← (measurePreserving_envBlocks μ n k).integral_comp']
  simp only [blockEval_envBlocks, logMoment]
  rw [← map_evalR_envMeasure μ B h (n + k),
    integral_map (measurable_evalR B h (n + k)).aemeasurable
      Real.measurable_log.aestronglyMeasurable]

private theorem marked_cost_bound (p : ℝ) (m j : ℕ) :
    (∑ i ∈ Finset.range (m + j), min p ((1 / 2 : ℝ) ^ (i + 1))) ≤
      (m : ℝ) * p + (1 / 2 : ℝ) ^ m - (1 / 2 : ℝ) ^ (m + j) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, add_sub_cancel_right]
    simpa using Finset.sum_le_sum (s := Finset.range m)
      (fun i _ => min_le_left p ((1 / 2 : ℝ) ^ (i + 1)))
  | succ j ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, pow_succ (1 / 2 : ℝ) (m + j)]
    have hw := min_le_right p ((1 / 2 : ℝ) ^ (m + j + 1))
    rw [pow_succ] at hw
    linarith

private theorem critical_tail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (hF : freeEnergy μ B h = 0) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : floorSeq B n ≤ t) :
    (lawR μ B h n).real (Ici t) ≤
      min 1 (4 * (floorSeq B n / t) ^ (Real.log 2 / Real.log (B / floorSeq B n))) := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  let b := floorSeq B n
  let p := (lawR μ B h n).real (Ici t)
  let D := Real.log (B / b)
  have hB0 : 0 < B := by linarith
  have hb : 0 < b := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have ht0 := hb.trans_le ht
  have hD : 0 < D := Real.log_pos ((one_lt_div hb).2 ((floorSeq_lt_one hB n).trans (by linarith)))
  apply le_min measureReal_le_one
  by_cases hp : p = 0
  · change p ≤ _
    rw [hp]
    positivity
  have hp0 : 0 < p := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
  let L := -Real.log p / Real.log 2
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := div_nonneg (neg_nonneg.mpr (Real.log_nonpos hp0.le measureReal_le_one)) h₂.le
  -- Below this height use the union bound, and above it use the probability bound one.
  let m := ⌊L⌋₊
  let r : ℝ := 1 / 2
  have hmp : r ^ m ≤ 2 * p := by
    have hm := Nat.lt_floor_add_one L
    have hlog : -(m : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log p := by
      have hh := (div_lt_iff₀ h₂).1 hm
      linarith
    rw [show r ^ m = Real.exp (-(m : ℝ) * Real.log 2) by
      rw [show r = Real.exp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact one_div _]
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    exact (Real.exp_le_exp.mpr hlog).trans_eq (by rw [Real.exp_add, Real.exp_log hp0, Real.exp_log (by norm_num : (0 : ℝ) < 2)])
  let ν := envMeasure μ n
  let f := evalR B h n
  let S := f ⁻¹' Ici t
  have hS : MeasurableSet S := measurableSet_Ici.preimage (measurable_evalR B h n)
  have hSp : ν.real S = p := by
    rw [← map_measureReal_apply (measurable_evalR B h n) measurableSet_Ici,
      map_evalR_envMeasure μ B h n]
  let X := fun k => r ^ k * (∫ e, markedExcess S B b f k e ∂blockMeasure ν k)
  have hbase : p * (Real.log t - Real.log b) ≤ X 0 := by
    have hlog₀ : Integrable (fun e : Env n => Real.log (f e)) ν :=
      integrable_log_blockEval hpos hmean hB h hn 0
    have hi : Integrable (markedExcess S B b f 0) ν :=
      (hlog₀.sub (integrable_const _)).indicator hS
    have hc : Integrable (S.indicator (fun _ => Real.log t - Real.log b)) ν :=
      (integrable_const _).indicator hS
    have hw := integral_mono hc hi (fun e => by
      change S.indicator (fun _ => Real.log t - Real.log b) e ≤
        S.indicator (fun e => Real.log (f e) - Real.log b) e
      by_cases he : e ∈ S
      · simp only [Set.indicator_of_mem he]
        exact sub_le_sub_right (Real.log_le_log ht0 he) _
      · simp [Set.indicator_of_notMem he])
    change p * (Real.log t - Real.log b) ≤
      r ^ (0 : ℕ) * (∫ e : Env n, markedExcess S B b f 0 e ∂ν)
    simpa [integral_indicator hS, hSp, smul_eq_mul] using hw
  have hstep (k : ℕ) :
      X k - D * min p (r ^ (k + 1)) ≤ X (k + 1) := by
    let a := (blockMeasure ν (k + 1)).real (marked S (k + 1))
    have ham : r ^ (k + 1) * a ≤ min p (r ^ (k + 1)) := by
      apply le_min
      · have ha := blockMeasure_marked_le ν hS (k + 1)
        rw [hSp] at ha
        calc
          r ^ (k + 1) * a ≤ r ^ (k + 1) * ((2 : ℝ) ^ (k + 1) * p) :=
            mul_le_mul_of_nonneg_left ha (by positivity)
          _ = p := by simp [r, one_div]
      · have := blockMeasureProbability ν (k + 1)
        exact mul_le_of_le_one_right (by positivity) (show a ≤ 1 from measureReal_le_one)
    have hs := markedExcess_integral_step ν hS hB0 (by linarith) hb
      (integrable_log_blockEval hpos hmean hB h hn) (ae_floor_blockEval hpos hB h n) k
    have hw := mul_le_mul_of_nonneg_left hs (show 0 ≤ r ^ (k + 1) by positivity)
    have he : r ^ (k + 1) * 2 = r ^ k := by rw [pow_succ]; dsimp [r]; ring
    change r ^ (k + 1) * (2 * (∫ e, markedExcess S B b f k e ∂blockMeasure ν k) - D * a) ≤ _ at hw
    rw [mul_sub, ← mul_assoc _ 2, he, mul_left_comm _ D] at hw
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_left ham hD.le) _).trans hw
  have hsum (k : ℕ) : X 0 - D * (∑ i ∈ Finset.range k, min p (r ^ (i + 1))) ≤ X k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ← sub_sub]
      exact (sub_le_sub_right ih _).trans (hstep k)
  have hlim : Tendsto (fun k => r ^ k * (logMoment μ B h (n + k) - Real.log b)) atTop (𝓝 0) := by
    have hF' := (freeEnergy_tendsto_aux hpos hmean hB h).comp (show Tendsto (fun k : ℕ => n + k) atTop atTop from by simpa [Nat.add_comm] using tendsto_add_atTop_nat n)
    rw [hF] at hF'
    have hlog : Tendsto (fun k => r ^ k * logMoment μ B h (n + k)) atTop (𝓝 0) := by
      have hw := hF'.const_mul ((2 : ℝ) ^ n)
      rw [mul_zero] at hw
      convert hw using 1
      ext k
      change r ^ k * logMoment μ B h (n + k) =
        (2 : ℝ) ^ n * (((2 : ℝ) ^ (n + k))⁻¹ * logMoment μ B h (n + k))
      rw [show r = (2 : ℝ)⁻¹ by norm_num [r], inv_pow, pow_add, mul_inv, ← mul_assoc]
      congr 1
      field_simp
    simpa only [mul_sub, zero_mul, sub_zero] using hlog.sub
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ r by norm_num [r])
        (show r < 1 by norm_num [r])).mul_const (Real.log b))
  have hf : X 0 - D * ((m : ℝ) * p + r ^ m) ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlim.comp (show Tendsto (fun k : ℕ => m + k) atTop atTop from by simpa [Nat.add_comm] using tendsto_add_atTop_nat m))
    apply Eventually.of_forall
    intro j
    have hc := marked_cost_bound p m j
    have hcost : (∑ i ∈ Finset.range (m + j), min p (r ^ (i + 1))) ≤ (m : ℝ) * p + r ^ m :=
      hc.trans (sub_le_self _ (by positivity))
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hcost hD.le) _).trans
      ((hsum (m + j)).trans (mul_le_mul_of_nonneg_left
        (markedExcess_integral_le_log hpos hmean hB h hn hS (m + j))
        (pow_nonneg (show 0 ≤ r by norm_num [r]) _)))
  have hlog : Real.log t - Real.log b ≤ D * (L + 2) := by
    have hmp' := add_le_add (mul_le_mul_of_nonneg_right (Nat.floor_le hL) hp0.le) hmp
    have hw : p * (Real.log t - Real.log b) ≤ D * (L * p + 2 * p) :=
      (hbase.trans (sub_nonpos.mp hf)).trans (mul_le_mul_of_nonneg_left hmp' hD.le)
    apply le_of_mul_le_mul_left _ hp0
    convert hw using 1
    ring
  change p ≤ 4 * (b / t) ^ (Real.log 2 / D)
  have htlog : Real.log (b / t) = Real.log b - Real.log t := Real.log_div hb.ne' ht0.ne'
  have hfinal : Real.log p ≤ Real.log 4 + Real.log (b / t) * (Real.log 2 / D) := by
    have hw := mul_le_mul_of_nonneg_right hlog (div_nonneg h₂.le hD.le)
    rw [show D * (L + 2) * (Real.log 2 / D) = -Real.log p + 2 * Real.log 2 by
      dsimp [L]
      field_simp [hD.ne', h₂.ne']] at hw
    rw [htlog, show Real.log (4 : ℝ) = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring]
    linarith
  calc
    p = Real.exp (Real.log p) := (Real.exp_log hp0).symm
    _ ≤ Real.exp (Real.log 4 + Real.log (b / t) * (Real.log 2 / D)) := Real.exp_le_exp.mpr hfinal
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4),
      Real.rpow_def_of_pos (div_pos hb ht0)]

private theorem power_dom {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖x ^ q‖ ≤ 1 + x := by
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_one hx.le h hq).trans (by linarith)
  · exact (show x ^ q ≤ x by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le h hq1).trans (by linarith)

private theorem integrable_power {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hpos : ∀ᵐ x ∂ν, 0 < x) (hmean : Integrable (fun x => x) ν)
    {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1) :
    Integrable (fun x => x ^ q) ν := by
  apply ((integrable_const (1 : ℝ)).add hmean).mono'
    (Real.continuous_rpow_const hq).measurable.aestronglyMeasurable
  filter_upwards [hpos] with x hx
  exact power_dom hx hq hq'

private theorem power_integral_bound {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hpos : ∀ᵐ x ∂ν, 0 < x) (hmean : Integrable (fun x => x) ν) {q s : ℝ}
    (hq : 0 < q) (hqs : q < s) (hq1 : q ≤ 1)
    (htail : ∀ x : ℝ, 1 ≤ x → ν.real (Ici x) ≤ 4 * x ^ (-s)) :
    (∫ x, x ^ q ∂ν) ≤ ∫ t in Ioi (0 : ℝ),
      if t ≤ 1 then 1 else 4 * t ^ (-s / q) := by
  let T := fun t : ℝ => ν.real {x | t ≤ x ^ q}
  let U := fun t : ℝ => if t ≤ 1 then 1 else 4 * t ^ (-s / q)
  have hT : Measurable T := Antitone.measurable fun t u htu =>
    measureReal_mono (fun _ hx => htu.trans hx)
  have hU : IntegrableOn U (Ioi (0 : ℝ)) := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 by ext x; simp,
      integrableOn_union]
    constructor
    · refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun ?_ measurableSet_Ioc
      intro t ht
      simp [U, ht.2]
    · have hi : -s / q < -1 := (div_lt_iff₀ hq).2 (by linarith)
      have hw : IntegrableOn (fun t : ℝ => 4 * t ^ (-s / q)) (Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt hi zero_lt_one).const_mul 4
      refine hw.congr_fun ?_ measurableSet_Ioi
      intro t ht
      simp [U, not_le.mpr ht]
  have hle (t : ℝ) : T t ≤ U t := by
    by_cases ht : t ≤ 1
    · rw [show U t = 1 by simp [U, ht]]
      exact measureReal_le_one
    have ht1 : 1 < t := lt_of_not_ge ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hset : {x | t ≤ x ^ q} =ᵐ[ν] Ici (t ^ (1 / q)) := by
      filter_upwards [hpos] with x hx
      change (t ≤ x ^ q) = (t ^ (1 / q) ≤ x)
      rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg ht0.le _) hx.le hq,
        ← Real.rpow_mul ht0.le, one_div_mul_cancel hq.ne', Real.rpow_one]
    have hp := htail (t ^ (1 / q)) (Real.one_le_rpow ht1.le (by positivity))
    rw [← Real.rpow_mul ht0.le, show (1 / q) * -s = -s / q by ring] at hp
    simpa [T, U, ht, measureReal_congr hset] using hp
  have hTi : IntegrableOn T (Ioi (0 : ℝ)) := by
    apply hU.mono' hT.aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (measureReal_nonneg (μ := ν))]
      exact hle t
  rw [(integrable_power hpos hmean hq.le hq1).integral_eq_integral_meas_le
    (by filter_upwards [hpos] with x hx using Real.rpow_nonneg hx.le q)]
  exact integral_mono hTi hU hle

private theorem eventual_subcritical_moment_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (hF : freeEnergy μ B h = 0) {q : ℝ} (hq : 0 < q) (hqθ : q < theta B) :
    ∃ K : ℝ, ∀ᶠ n in atTop, realMoment μ B h n q ≤ K := by
  obtain ⟨s, hqs, hsθ⟩ := exists_between hqθ
  have hB0 : 0 < B := by linarith
  have hden : Real.log B ≠ 0 := (Real.log_pos (by linarith : 1 < B)).ne'
  have hlim : Tendsto (fun n => Real.log 2 / Real.log (B / floorSeq B n))
      atTop (𝓝 (theta B)) := by
    have hh := (tendsto_const_nhds (x := B)).div (tendsto_floorSeq hB) one_ne_zero
    rw [div_one] at hh
    exact tendsto_const_nhds.div ((Real.continuousAt_log hB0.ne').tendsto.comp hh) hden
  refine ⟨∫ t in Ioi (0 : ℝ), if t ≤ 1 then 1 else 4 * t ^ (-s / q), ?_⟩
  filter_upwards [hlim.eventually (lt_mem_nhds hsθ), eventually_ge_atTop 1] with n hn hn1
  have hn' : s < Real.log 2 / Real.log (B / floorSeq B n) := hn
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  apply power_integral_bound (ae_pos_lawR hpos hB h n)
    (integrable_lawR_of hpos hmean hB h n) hq hqs (hqθ.le.trans (theta_lt_one hB).le)
  intro x hx
  have hbn := floorSeq_le_one hB n
  have hb0 := floorSeq_nonneg hB n
  have hh := (critical_tail hpos hmean hB h hF hn1 (hbn.trans hx)).trans (min_le_right _ _)
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  calc
    (floorSeq B n / x) ^ (Real.log 2 / Real.log (B / floorSeq B n))
      ≤ (1 / x) ^ (Real.log 2 / Real.log (B / floorSeq B n)) :=
        Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hbn (by linarith))
          (hq.le.trans (hqs.le.trans hn'.le))
    _ = x ^ (-(Real.log 2 / Real.log (B / floorSeq B n))) := by
      rw [one_div, Real.inv_rpow (by linarith : 0 ≤ x), Real.rpow_neg (by linarith : 0 ≤ x)]
    _ ≤ x ^ (-s) := Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hn'.le)

private theorem subcritical_moment_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (hF : freeEnergy μ B h = 0) {q : ℝ} (hq : 0 < q) (hqθ : q < theta B)
    (n : ℕ) : realMoment μ B h n q ≤ (B - 1) ^ q := by
  let c := B - 1
  let G := fun k => realMoment μ B h k q
  let S := fun k => G k ^ (1 / q)
  have hG (k : ℕ) : 0 ≤ G k := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_pos_lawR hpos hB h k] with x hx
    exact Real.rpow_nonneg hx.le q
  have hS (k : ℕ) : 0 ≤ S k := Real.rpow_nonneg (hG k) _
  have hc : 0 < c := by dsimp [c]; linarith
  have hB0 : 0 < B := by linarith
  have hq1 := hqθ.trans (theta_lt_one hB)
  by_contra! hn
  have hs : c < S n := by
    have hh := Real.rpow_lt_rpow (Real.rpow_nonneg hc.le q) hn (by positivity : 0 < 1 / q)
    rw [← Real.rpow_mul hc.le, mul_one_div_cancel hq.ne', Real.rpow_one] at hh
    exact hh
  let d := 2 * c / B
  have hd : 1 < d := (one_lt_div hB0).2 (by dsimp [c]; linarith)
  have hgrowth (k : ℕ) : d ^ k * (S n - c) ≤ S (n + k) - c := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hsk : 0 ≤ S (n + k) - c := (by positivity : 0 ≤ d ^ k * (S n - c)).trans ih
      have hj := jensen_step_aux hpos hmean hB h hq hq1 (n + k)
      change (S (n + k) ^ 2 + c) / B ≤ S (n + k + 1) at hj
      have hid (x : ℝ) : (x ^ 2 + c) / B - c = d * (x - c) + (x - c)^2 / B := by
        dsimp [d, c]
        field_simp
        ring
      rw [Nat.add_succ, pow_succ, mul_right_comm]
      calc
        d ^ k * (S n - c) * d ≤ (S (n + k) - c) * d := mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ S (n + k + 1) - c := by
          have hh := sub_le_sub_right hj c
          rw [hid] at hh
          nlinarith [div_nonneg (sq_nonneg (S (n + k) - c)) hB0.le]
  obtain ⟨K, hK⟩ := eventual_subcritical_moment_bound hpos hmean hB h hF hq hqθ
  have hKb : ∀ᶠ k in atTop, S (n + k) ≤ (max K 0) ^ (1 / q) := by
    filter_upwards [(show Tendsto (fun k : ℕ => n + k) atTop atTop from by simpa [Nat.add_comm] using tendsto_add_atTop_nat n).eventually hK] with k hk
    exact Real.rpow_le_rpow (hG _) (hk.trans (le_max_left _ _)) (by positivity)
  have hl := ((tendsto_pow_atTop_atTop_of_one_lt hd).atTop_mul_const
    (sub_pos.mpr hs)).eventually (eventually_gt_atTop ((max K 0) ^ (1 / q) - c))
  obtain ⟨k, hk, hk'⟩ := (hl.and hKb).exists
  exact (not_lt_of_ge (sub_le_sub_right hk' c)) (hk.trans_le (hgrowth k))

private noncomputable def logKernel (B q x : ℝ) : ℝ :=
  x ^ q * (Real.log x - 2 * Real.log B)

private noncomputable def kernelDeriv (B q x : ℝ) : ℝ :=
  x ^ (q - 1) * (q * (Real.log x - 2 * Real.log B) + 1)

private theorem hasDerivAt_logKernel (B q : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logKernel B q) (kernelDeriv B q x) x := by
  have hd := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hx.ne')).mul
    ((Real.hasDerivAt_log hx.ne').sub_const (2 * Real.log B))
  convert hd using 1
  · rfl
  · unfold kernelDeriv
    rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv]
    ring

private theorem B_rpow_theta {B : ℝ} (hB : 2 < B) : B ^ theta B = 2 := by
  have hb : 0 < B := by linarith
  have hl := Real.log_pos (show 1 < B by linarith)
  rw [Real.rpow_def_of_pos hb, theta, ← mul_div_assoc, mul_div_cancel_left₀ _ hl.ne',
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem logKernel_shift_nonneg {B q x : ℝ} (hB : 2 < B)
    (hq : 0 ≤ q) (hqθ : q ≤ theta B) (hx : 1 ≤ x) :
    logKernel B q x ≤ logKernel B q (x + (B - 1)) := by
  have hB1 : 1 ≤ B := by linarith
  have ha := Real.log_pos (show 1 < B by linarith)
  let g := fun r : ℝ => q * (Real.log r - 2 * Real.log B) + 1
  have hg : MonotoneOn g (Ioi (0 : ℝ)) := by
    intro u hu v _ huv
    exact add_le_add_left (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.log_le_log hu huv) _) hq) _
  have hqB : q * Real.log B ≤ Real.log 2 := by
    have hw := mul_le_mul_of_nonneg_right hqθ ha.le
    rwa [theta, div_mul_cancel₀ _ ha.ne'] at hw
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    linarith [Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)]
  have hgB : 0 ≤ g B := by dsimp [g]; nlinarith
  have hmono (u : ℝ) (hu : 0 < u) (hgu : 0 ≤ g u) :
      MonotoneOn (logKernel B q) (Ici u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici u)
    · exact fun r hr => (hasDerivAt_logKernel B q (hu.trans_le hr)).continuousAt.continuousWithinAt
    · intro r hr
      exact (hasDerivAt_logKernel B q
        (hu.trans_le (mem_Ici.mp (interior_subset hr)))).differentiableAt.differentiableWithinAt
    · intro r hr
      have hur : u ≤ r := mem_Ici.mp (interior_subset hr)
      rw [(hasDerivAt_logKernel B q (hu.trans_le hur)).deriv]
      exact mul_nonneg (Real.rpow_nonneg (hu.trans_le hur).le _)
        (hgu.trans (hg hu (hu.trans_le hur) hur))
  have hBcmp : logKernel B q 1 ≤ logKernel B q B := by
    have hp := Real.rpow_le_rpow_of_exponent_le hB1 hqθ
    rw [B_rpow_theta hB] at hp
    unfold logKernel
    simp only [Real.one_rpow, Real.log_one]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) ha.le]
  have hx0 := zero_lt_one.trans_le hx
  by_cases hgx : 0 ≤ g x
  · have hx' : x ≤ x + (B - 1) := by linarith
    exact hmono x hx0 hgx (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx') hx'
  · have hanti : AntitoneOn (logKernel B q) (Icc 1 x) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 1 x)
      · exact fun r hr => (hasDerivAt_logKernel B q
          (zero_lt_one.trans_le hr.1)).continuousAt.continuousWithinAt
      · intro r hr
        have hr' : r ∈ Icc 1 x := interior_subset hr
        exact (hasDerivAt_logKernel B q
          (zero_lt_one.trans_le hr'.1)).differentiableAt.differentiableWithinAt
      · intro r hr
        have hr' : r ∈ Icc 1 x := interior_subset hr
        have hr0 := zero_lt_one.trans_le hr'.1
        rw [(hasDerivAt_logKernel B q hr0).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hr0.le _)
          ((hg hr0 hx0 hr'.2).trans (le_of_not_ge hgx))
    have hBx : B ≤ x + (B - 1) := by linarith
    exact (hanti ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx).trans
      (hBcmp.trans (hmono B (by linarith) hgB (mem_Ici.mpr le_rfl) (mem_Ici.mpr hBx) hBx))

private theorem kernel_error {B : ℝ} (hB : 2 < B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ q ∈ Icc 0 (theta B), ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      floorSeq B n ^ 2 ≤ x →
      -(E * (2 / B) ^ n) ≤ logKernel B q (x + (B - 1)) - logKernel B q x := by
  let b := floorSeq B 1 ^ 2
  have hb : 0 < b := pow_pos (floorSeq_one_pos hB) _
  have hb1 : b ≤ 1 := by
    simpa [b] using pow_le_pow_left₀ (floorSeq_nonneg hB 1) (floorSeq_le_one hB 1) 2
  let A := Icc b B ×ˢ Icc 0 (theta B)
  have hA : IsCompact A := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => kernelDeriv B p.2 p.1) A := by
    intro p hp
    obtain hp0 : 0 < p.1 := hb.trans_le hp.1.1
    have hm : ContinuousAt (fun p : ℝ × ℝ => p.1 ^ (p.2 - 1)) p :=
      (Real.continuousAt_rpow (p.1, p.2 - 1) (Or.inl hp0.ne')).comp₂
        continuousAt_fst (continuousAt_snd.sub continuousAt_const)
    have hl : ContinuousAt (fun p : ℝ × ℝ => Real.log p.1) p :=
      (Real.continuousAt_log hp0.ne').comp continuousAt_fst
    exact (hm.mul ((continuousAt_snd.mul (hl.sub continuousAt_const)).add
      continuousAt_const)).continuousWithinAt
  obtain ⟨K, hK⟩ := hA.exists_bound_of_continuousOn hcont
  let C := max K 0
  have hLip (q : ℝ) (hq : q ∈ Icc 0 (theta B)) {x y : ℝ}
      (hx : x ∈ Icc b B) (hy : y ∈ Icc b B) :
      |logKernel B q y - logKernel B q x| ≤ C * |y - x| := by
    have hder (r : ℝ) (hr : r ∈ Icc b B) :=
      hasDerivAt_logKernel B q (hb.trans_le hr.1)
    have hn (r : ℝ) (hr : r ∈ Icc b B) : ‖deriv (logKernel B q) r‖ ≤ C := by
      rw [(hder r hr).deriv]
      exact (hK (r, q) ⟨hr, hq⟩).trans (le_max_left _ _)
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun r hr => (hder r hr).differentiableAt) hn (convex_Icc b B) hx hy
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨4 * C, by positivity, fun q hq n hn x hx => ?_⟩
  have hρ : 0 ≤ (2 / B) ^ n := by positivity
  by_cases hx1 : 1 ≤ x
  · exact (neg_nonpos.mpr (mul_nonneg (by positivity) hρ)).trans
      (sub_nonneg.mpr (logKernel_shift_nonneg hB hq.1 hq.2 hx1))
  have hx1' := le_of_not_ge hx1
  have hfloor : b ≤ floorSeq B n ^ 2 :=
    pow_le_pow_left₀ (floorSeq_nonneg hB 1) (floorSeq_one_le hB hn) 2
  have hxb := hfloor.trans hx
  have hbnd : 1 - x ≤ 2 * (2 / B) ^ n := by
    have hf := floorSeq_le_one hB n
    have hh := one_sub_floorSeq_le hB n
    nlinarith [sq_nonneg (1 - floorSeq B n)]
  have h₁ := hLip q hq (x := x) (y := 1) ⟨hxb, by linarith⟩ ⟨hb1, by linarith⟩
  have h₂ := hLip q hq (x := x + (B - 1)) (y := B)
    ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hx1')] at h₁
  rw [show B - (x + (B - 1)) = 1 - x by ring,
    abs_of_nonneg (sub_nonneg.mpr hx1')] at h₂
  have h₀ := logKernel_shift_nonneg hB hq.1 hq.2 (x := 1) le_rfl
  rw [show 1 + (B - 1) = B by ring] at h₀
  have hc : 0 ≤ C := le_max_right _ _
  nlinarith [neg_abs_le (logKernel B q 1 - logKernel B q x),
    le_abs_self (logKernel B q B - logKernel B q (x + (B - 1))),
    mul_le_mul_of_nonneg_left hbnd hc]

private noncomputable def weightedLog (B q x : ℝ) : ℝ :=
  x ^ q * (Real.log x - Real.log B)

private noncomputable def signedMoment (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  ∫ x, weightedLog B q x ∂lawR μ B h n

private theorem measurable_weightedLog (B : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    Measurable (weightedLog B q) :=
  (Real.continuous_rpow_const hq).measurable.mul (Real.measurable_log.sub_const _)

private theorem integrable_abs_weighted_theta {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    Integrable (fun x => |weightedLog B (theta B) x|) (lawR μ B h n) := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  have h₁ := integrable_tiltedLogPower_of hpos hmean hB h n (q := 1) (by norm_num)
  simp only [Real.rpow_one] at h₁
  have h₂ := integrable_power (ae_pos_lawR hpos hB h n)
    (integrable_lawR_of hpos hmean hB h n) (theta_pos hB).le (theta_lt_one hB).le
  apply (h₁.add (h₂.const_mul |Real.log B|)).mono'
    (continuous_abs.measurable.comp (measurable_weightedLog B (theta_pos hB).le)).aestronglyMeasurable
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  change ‖|weightedLog B (theta B) x|‖ ≤ x ^ theta B * |Real.log x| + |Real.log B| * x ^ theta B
  rw [Real.norm_eq_abs, abs_abs, weightedLog, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  rw [mul_comm |Real.log B|, ← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.rpow_nonneg hx.le _)

private noncomputable def lowerLogBound (B : ℝ) : ℝ :=
  Real.log B - Real.log (floorSeq B 1)

private theorem weightedLog_abs_le_floor {B q x : ℝ} (hB : 2 < B) (hq : 0 ≤ q)
    (hx : floorSeq B 1 ≤ x) (hx1 : x ≤ 1) :
    |weightedLog B q x| ≤ lowerLogBound B := by
  have hx0 := (floorSeq_one_pos hB).trans_le hx
  have ha := Real.log_pos (show 1 < B by linarith)
  have hlog := Real.log_nonpos hx0.le hx1
  rw [weightedLog, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
    abs_of_nonpos (sub_nonpos.mpr (hlog.trans ha.le))]
  calc
    x ^ q * -(Real.log x - Real.log B) ≤ 1 * -(Real.log x - Real.log B) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_one hx0.le hx1 hq) (by linarith)
    _ ≤ lowerLogBound B := by
      change _ ≤ Real.log B - Real.log (floorSeq B 1)
      linarith only [Real.log_le_log (floorSeq_one_pos hB) hx]

private theorem lowerLogBound_nonneg {B : ℝ} (hB : 2 < B) :
    0 ≤ lowerLogBound B :=
  (abs_nonneg _).trans (weightedLog_abs_le_floor hB (q := 0) le_rfl
    (floorSeq_le_one hB 1) le_rfl)

private theorem weightedLog_dom_theta {B q x : ℝ} (hB : 2 < B) (hq : 0 ≤ q)
    (hqθ : q ≤ theta B) (hx : floorSeq B 1 ≤ x) :
    |weightedLog B q x| ≤ lowerLogBound B + |weightedLog B (theta B) x| := by
  rcases le_total x 1 with h | h
  · exact (weightedLog_abs_le_floor hB hq hx h).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have hx0 : 0 ≤ x := zero_le_one.trans h
    simp only [weightedLog, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0 _)]
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h hqθ) (abs_nonneg _)).trans
      (le_add_of_nonneg_left (lowerLogBound_nonneg hB))

private theorem integrable_weightedLog {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 0 ≤ q) (hqθ : q ≤ theta B) :
    Integrable (weightedLog B q) (lawR μ B h n) := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  apply ((integrable_const (lowerLogBound B)).add
    (integrable_abs_weighted_theta hpos hmean hB h n)).mono'
    (measurable_weightedLog B hq).aestronglyMeasurable
  filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
  rw [Real.norm_eq_abs]
  exact weightedLog_dom_theta hB hq hqθ ((floorSeq_one_le hB hn).trans hx)

private theorem signedMoment_bounded {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (hF : freeEnergy μ B h = 0) {q : ℝ} (hq : 0 < q) (hqθ : q < theta B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → signedMoment μ B h n q ≤ K := by
  obtain ⟨s, hqs, hsθ⟩ := exists_between hqθ
  let L := (s - q)⁻¹ + Real.log B
  have hL : 0 ≤ L := add_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hqs.le))
    (Real.log_nonneg (by linarith))
  let D := lowerLogBound B
  have hD : 0 ≤ D := lowerLogBound_nonneg hB
  have hc : 0 ≤ B - 1 := by linarith
  refine ⟨D + L * (B - 1) ^ s, by positivity, fun n hn => ?_⟩
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  have hi := integrable_power (ae_pos_lawR hpos hB h n) (integrable_lawR_of hpos hmean hB h n)
    (hq.le.trans hqs.le) (hsθ.le.trans (theta_lt_one hB).le)
  have hdom : ∀ᵐ x ∂lawR μ B h n, weightedLog B q x ≤ D + L * x ^ s := by
    filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
    have hxf := (floorSeq_one_le hB hn).trans hx
    have hx0 := (floorSeq_one_pos hB).trans_le hxf
    rcases le_total x 1 with hsmall | hlarge
    · exact ((le_abs_self _).trans (weightedLog_abs_le_floor hB hq.le hxf hsmall)).trans
        (le_add_of_nonneg_right (mul_nonneg hL (Real.rpow_nonneg hx0.le _)))
    · have hh := Real.log_le_rpow_div hx0.le (sub_pos.mpr hqs)
      have ha : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
      refine le_trans ?_ (le_add_of_nonneg_left hD)
      calc
        weightedLog B q x ≤ x ^ q * (x ^ (s - q) / (s - q)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx0.le _)
        _ = (s - q)⁻¹ * x ^ s := by
          rw [div_eq_mul_inv, ← mul_assoc, ← Real.rpow_add hx0, add_sub_cancel]
          ring
        _ ≤ L * x ^ s := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha) (Real.rpow_nonneg hx0.le _)
  have hi' : Integrable (fun x : ℝ => D + L * x ^ s) (lawR μ B h n) :=
    (integrable_const D).add (hi.const_mul L)
  unfold signedMoment
  refine (integral_mono_ae (integrable_weightedLog hpos hmean hB h hn hq.le hqθ.le) hi' hdom).trans ?_
  have hii : Integrable (fun x : ℝ => L * x ^ s) (lawR μ B h n) := hi.const_mul L
  rw [integral_add (integrable_const D) hii, integral_const,
    probReal_univ, one_smul, integral_const_mul]
  exact add_le_add_right (mul_le_mul_of_nonneg_left
    (subcritical_moment_le hpos hmean hB h hF (hq.trans hqs) hsθ n) hL) D

private noncomputable def kernelShift (B q x : ℝ) : ℝ :=
  logKernel B q (x + (B - 1)) - logKernel B q x

/-- The exact signed-moment recurrence, including integrability of its kernel term. -/
private theorem signedMoment_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 0 ≤ q) (hqθ : q ≤ theta B) :
    let ν := lawR μ B h n
    Integrable (fun p : ℝ × ℝ => kernelShift B q (p.1 * p.2)) (ν.prod ν) ∧
    signedMoment μ B h (n + 1) q =
      2 * B ^ (-q) * realMoment μ B h n q * signedMoment μ B h n q +
      B ^ (-q) * ∫ p : ℝ × ℝ, kernelShift B q (p.1 * p.2) ∂ν.prod ν := by
  intro ν
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR (μ := μ) B h n
  have hB0 : 0 < B := by linarith
  let w := weightedLog B q
  let f := fun x : ℝ => x ^ q
  let V := fun p : ℝ × ℝ => (p.1 * p.2 + (B - 1)) / B
  let ψ := fun p : ℝ × ℝ => kernelShift B q (p.1 * p.2)
  have hiw : Integrable w ν := integrable_weightedLog hpos hmean hB h hn hq hqθ
  have hif : Integrable f ν := integrable_power (ae_pos_lawR hpos hB h n)
    (integrable_lawR_of hpos hmean hB h n) hq (hqθ.trans (theta_lt_one hB).le)
  have hV : Measurable V := by fun_prop
  have hiV : Integrable (w ∘ V) (ν.prod ν) := by
    apply (integrable_map_measure (measurable_weightedLog B hq).aestronglyMeasurable hV.aemeasurable).1
    change Integrable w (lawR μ B h (n + 1))
    exact integrable_weightedLog hpos hmean hB h (by omega) hq hqθ
  have hp : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, 0 < p.1 ∧ 0 < p.2 := by
    have h₁ := measurePreserving_fst (μ := ν) (ν := ν)
    have h₂ := measurePreserving_snd (μ := ν) (ν := ν)
    filter_upwards [h₁.quasiMeasurePreserving.ae (ae_pos_lawR hpos hB h n),
      h₂.quasiMeasurePreserving.ae (ae_pos_lawR hpos hB h n)] with p hp₁ hp₂
    exact ⟨hp₁, hp₂⟩
  have hwp : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν,
      B ^ q * w (V p) = w p.1 * f p.2 + f p.1 * w p.2 + ψ p := by
    filter_upwards [hp] with p hp
    have hs := mul_pos hp.1 hp.2
    have hsc : 0 < p.1 * p.2 + (B - 1) := by linarith
    have hfac : (B ^ q) ≠ 0 := (Real.rpow_pos_of_pos hB0 q).ne'
    dsimp [w, V, f, ψ, weightedLog, kernelShift, logKernel]
    rw [Real.div_rpow hsc.le hB0.le, Real.log_div hsc.ne' hB0.ne',
      Real.log_mul hp.1.ne' hp.2.ne', Real.mul_rpow hp.1.le hp.2.le]
    field_simp
    ring
  have hi₁ : Integrable (fun p : ℝ × ℝ => w p.1 * f p.2) (ν.prod ν) := hiw.mul_prod hif
  have hi₂ : Integrable (fun p : ℝ × ℝ => f p.1 * w p.2) (ν.prod ν) := hif.mul_prod hiw
  have hψ : Integrable ψ (ν.prod ν) := by
    refine ((hiV.const_mul (B ^ q)).sub (hi₁.add hi₂)).congr ?_
    filter_upwards [hwp] with p hp
    change B ^ q * w (V p) - (w p.1 * f p.2 + f p.1 * w p.2) = ψ p
    linarith
  refine ⟨hψ, ?_⟩
  have he := integral_congr_ae hwp
  have hi₁₂ : Integrable (fun p : ℝ × ℝ => w p.1 * f p.2 + f p.1 * w p.2) (ν.prod ν) :=
    hi₁.add hi₂
  rw [integral_const_mul, integral_add hi₁₂ hψ, integral_add hi₁ hi₂,
    integral_prod_mul w f, integral_prod_mul f w] at he
  have hIV : (∫ p : ℝ × ℝ, w (V p) ∂ν.prod ν) = signedMoment μ B h (n + 1) q := by
    unfold signedMoment
    rw [lawR_succ, integral_map hV.aemeasurable (measurable_weightedLog B hq).aestronglyMeasurable]
  rw [hIV] at he
  change B ^ q * signedMoment μ B h (n + 1) q =
    signedMoment μ B h n q * realMoment μ B h n q +
    realMoment μ B h n q * signedMoment μ B h n q + _ at he
  rw [Real.rpow_neg hB0.le]
  field_simp [(Real.rpow_pos_of_pos hB0 q).ne']
  nlinarith only [he]

private theorem realMoment_floor_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    floorSeq B n ≤ realMoment μ B h n q := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  have hi := integrable_power (ae_pos_lawR hpos hB h n)
    (integrable_lawR_of hpos hmean hB h n) hq hq1
  have hle := integral_mono_ae (integrable_const (floorSeq B n)) hi
    (show ∀ᵐ x ∂lawR μ B h n, floorSeq B n ≤ x ^ q from by
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
      have hb := floorSeq_nonneg hB n
      have hh : floorSeq B n ≤ floorSeq B n ^ q := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_ge' hb (floorSeq_le_one hB n) hq hq1
      exact hh.trans (Real.rpow_le_rpow hb hx hq))
  simpa only [integral_const, probReal_univ, one_smul, realMoment] using hle

private theorem signedMoment_recurrence {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {E : ℝ} (hE : 0 ≤ E)
    (herror : ∀ q ∈ Icc 0 (theta B), ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      floorSeq B n ^ 2 ≤ x → -(E * (2 / B) ^ n) ≤ kernelShift B q x)
    {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 0 ≤ q) (hqθ : q ≤ theta B) :
    2 * B ^ (-q) * realMoment μ B h n q * signedMoment μ B h n q - E * (2 / B) ^ n ≤
      signedMoment μ B h (n + 1) q := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR (μ := μ) B h n
  obtain ⟨hi, he⟩ := signedMoment_step hpos hmean hB h hn hq hqθ
  have h₁ := measurePreserving_fst (μ := ν) (ν := ν)
  have h₂ := measurePreserving_snd (μ := ν) (ν := ν)
  have hp : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν,
      -(E * (2 / B) ^ n) ≤ kernelShift B q (p.1 * p.2) := by
    filter_upwards [h₁.quasiMeasurePreserving.ae (ae_floorSeq_le_lawR hpos hB h n),
      h₂.quasiMeasurePreserving.ae (ae_floorSeq_le_lawR hpos hB h n)] with p hp₁ hp₂
    apply herror q ⟨hq, hqθ⟩ n hn
    have hb := floorSeq_nonneg hB n
    rw [pow_two]
    exact mul_le_mul hp₁ hp₂ hb (hb.trans hp₁)
  have hI := integral_mono_ae (integrable_const _) hi hp
  simp only [integral_const, probReal_univ, one_smul] at hI
  have hB0 : 0 ≤ B := by linarith
  have hρ : 0 ≤ (2 / B) ^ n := by positivity
  have hqB : B ^ (-q) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hq)
  rw [he]
  have hlo : -(E * (2 / B) ^ n) ≤
      B ^ (-q) * (∫ p : ℝ × ℝ, kernelShift B q (p.1 * p.2) ∂ν.prod ν) := calc
    -(E * (2 / B) ^ n) = 1 * -(E * (2 / B) ^ n) := by ring
    _ ≤ B ^ (-q) * -(E * (2 / B) ^ n) :=
      mul_le_mul_of_nonpos_right hqB (neg_nonpos.mpr (mul_nonneg hE hρ))
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (Real.rpow_nonneg hB0 _)
  linarith only [hlo]

private theorem backward_bound {H : ℕ → ℝ} {r d E K : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hd : 1 < d) (hE : 0 ≤ E)
    (hK : ∀ n, 1 ≤ n → H n ≤ K)
    (hstep : ∀ n, 1 ≤ n → d * H n ≤ H (n + 1) + E * r ^ n) :
    ∀ n, 1 ≤ n → H n ≤ (E / (1 - r)) * r ^ n := by
  let T := fun n : ℕ => (E / (1 - r)) * r ^ n
  have hT (n : ℕ) : 0 ≤ T n := mul_nonneg (div_nonneg hE (by linarith)) (pow_nonneg hr _)
  have hid (n : ℕ) : T n = T (n + 1) + E * r ^ n := by
    dsimp [T]
    rw [pow_succ]
    field_simp [ne_of_gt (sub_pos.mpr hr1)]
    ring
  intro n hn
  change H n ≤ T n
  by_contra! hh
  have hproj (k : ℕ) : d ^ k * (H n - T n) ≤ H (n + k) - T (n + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hstep (n + k) (by omega)
      have hle := mul_le_mul_of_nonneg_right ih (show 0 ≤ d by linarith)
      have hdT : T (n + k) ≤ d * T (n + k) :=
        le_mul_of_one_le_left (hT _) hd.le
      have hid' := hid (n + k)
      rw [pow_succ, mul_right_comm]
      change d ^ k * (H n - T n) * d ≤ H (n + k + 1) - T (n + k + 1)
      calc
        d ^ k * (H n - T n) * d ≤ (H (n + k) - T (n + k)) * d := hle
        _ = d * H (n + k) - d * T (n + k) := by ring
        _ ≤ H (n + k + 1) - T (n + k + 1) := by linarith only [h, hdT, hid']
  have htop := (tendsto_pow_atTop_atTop_of_one_lt hd).atTop_mul_const (sub_pos.mpr hh)
  obtain ⟨k, hk⟩ := (htop.eventually (eventually_gt_atTop K)).exists
  exact (not_lt_of_ge ((hproj k).trans
    ((sub_le_self _ (hT _)).trans (hK (n + k) (by omega))))) hk

private theorem signedMoment_upper {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ᵐ w ∂μ, 0 < w) → (∫ w, w ∂μ) = 1 → ∀ h : ℝ, freeEnergy μ B h = 0 →
      ∀ q : ℝ, 0 < q → q < theta B → ∀ n : ℕ, 1 ≤ n →
        signedMoment μ B h n q ≤ C * (2 / B) ^ n := by
  obtain ⟨E, hE, herr⟩ := kernel_error hB
  let r := 2 / B
  let b := floorSeq B 1
  have hB0 : 0 < B := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := (div_lt_one hB0).2 hB
  have hb : 0 < b := floorSeq_one_pos hB
  let A := 1 / (b * (1 - r))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  -- Compensate for the product of the floors by a geometric bound on their log deficits.
  let W := fun n : ℕ => Real.exp (-A * r ^ n)
  have hW (n : ℕ) : 0 < W n := Real.exp_pos _
  have hW1 (n : ℕ) : W n ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (pow_nonneg hr _))
  have hWlo (n : ℕ) : Real.exp (-A) ≤ W n := by
    apply Real.exp_le_exp.mpr
    have hh := pow_le_one₀ hr hr1.le (n := n)
    nlinarith only [mul_nonneg hA (sub_nonneg.mpr hh)]
  have hWstep (n : ℕ) (hn : 1 ≤ n) : W n ≤ W (n + 1) * floorSeq B n := by
    let u := floorSeq B n
    have hbu : b ≤ u := floorSeq_one_le hB hn
    have hu := hb.trans_le hbu
    have hu1 : u ≤ 1 := floorSeq_le_one hB n
    have herr' : 1 - u ≤ r ^ n := one_sub_floorSeq_le hB n
    have hlog : -Real.log u ≤ r ^ n / b := calc
      -Real.log u = Real.log u⁻¹ := (Real.log_inv u).symm
      _ ≤ u⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
      _ = (1 - u) / u := by field_simp
      _ ≤ (1 - u) / b := div_le_div_of_nonneg_left (sub_nonneg.mpr hu1) hb hbu
      _ ≤ r ^ n / b := div_le_div_of_nonneg_right herr' hb.le
    change Real.exp (-A * r ^ n) ≤ Real.exp (-A * r ^ (n + 1)) * u
    rw [← Real.exp_log hu, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hid : A * r ^ n - A * r ^ (n + 1) = r ^ n / b := by
      dsimp [A]
      rw [pow_succ]
      field_simp [hb.ne', ne_of_gt (sub_pos.mpr hr1)]
    linarith
  let C := E / (1 - r) / Real.exp (-A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun μ _ hpos hmean h hF q hq hqθ n hn => ?_⟩
  let d := 2 * B ^ (-q)
  have hd : 1 < d := by
    have hpow := Real.rpow_lt_rpow_of_exponent_lt (show 1 < B by linarith) hqθ
    rw [B_rpow_theta hB] at hpow
    change 1 < 2 * B ^ (-q)
    rw [Real.rpow_neg hB0.le, ← div_eq_mul_inv, one_lt_div (Real.rpow_pos_of_pos hB0 q)]
    exact hpow
  let H := fun j => signedMoment μ B h j q
  let G := fun j => realMoment μ B h j q
  let Y := fun j => W j * max (H j) 0
  obtain ⟨K, hK, hHK⟩ := signedMoment_bounded hpos hmean hB h hF hq hqθ
  have hY (j : ℕ) (hj : 1 ≤ j) : Y j ≤ K := calc
    Y j ≤ 1 * max (H j) 0 := mul_le_mul_of_nonneg_right (hW1 j) (le_max_right _ _)
    _ ≤ K := by rw [one_mul]; exact max_le (hHK j hj) hK
  have hstep (j : ℕ) (hj : 1 ≤ j) : d * Y j ≤ Y (j + 1) + E * r ^ j := by
    have hrj := pow_nonneg hr j
    have hG := realMoment_floor_le hpos hmean hB h j hq.le (hqθ.le.trans (theta_lt_one hB).le)
    have hwg : W j ≤ W (j + 1) * G j :=
      (hWstep j hj).trans (mul_le_mul_of_nonneg_left hG (hW _).le)
    have hw := mul_le_mul_of_nonneg_right hwg (show 0 ≤ d * max (H j) 0 by positivity)
    have hE' := mul_le_mul_of_nonneg_right (hW1 (j + 1)) (mul_nonneg hE hrj)
    rw [one_mul] at hE'
    have hrec := signedMoment_recurrence hpos hmean hB h hE
      (fun q hq j hj x hx => herr q hq j hj x hx) hj hq.le hqθ.le
    change d * G j * H j - E * r ^ j ≤ H (j + 1) at hrec
    have hposrec : d * G j * max (H j) 0 ≤ max (H (j + 1)) 0 + E * r ^ j := by
      rcases le_total (H j) 0 with hh | hh
      · rw [max_eq_right hh, mul_zero]
        positivity
      · rw [max_eq_left hh]
        linarith only [hrec, le_max_left (H (j + 1)) 0]
    have hi := mul_le_mul_of_nonneg_left hposrec (hW (j + 1)).le
    dsimp only [Y]
    nlinarith only [hw, hi, hE']
  have hfinal := backward_bound hr hr1 hd hE hY hstep n hn
  have hwm := mul_le_mul_of_nonneg_right (hWlo n) (le_max_right (H n) 0)
  have hle : max (H n) 0 ≤ C * r ^ n := by
    have hle' := hwm.trans hfinal
    change max (H n) 0 ≤ (E / (1 - r) / Real.exp (-A)) * r ^ n
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (Real.exp_pos (-A))).2
    exact (mul_comm _ _).le.trans hle'
  exact (le_max_left _ _).trans hle

private theorem endpoint_limits {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hqθ : ∀ j, q j ≤ theta B) (hlim : Tendsto q atTop (𝓝 (theta B))) :
    Tendsto (fun j => realMoment μ B h n (q j)) atTop (𝓝 (tiltedMass μ B h n)) ∧
      Tendsto (fun j => signedMoment μ B h n (q j)) atTop (𝓝 (signedMoment μ B h n (theta B))) := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hθ := integrable_abs_weighted_theta hpos hmean hB h n
  have hp : ∀ᵐ x ∂lawR μ B h n, Tendsto (fun j => x ^ q j) atTop (𝓝 (x ^ theta B)) := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    exact (Real.continuousAt_const_rpow hx.ne').tendsto.comp hlim
  constructor
  · unfold realMoment tiltedMass
    apply tendsto_integral_of_dominated_convergence (fun x => 1 + x) ?_
      ((integrable_const 1).add hi) ?_ hp
    · exact fun j => (Real.continuous_rpow_const (hq j)).measurable.aestronglyMeasurable
    · intro j
      filter_upwards [ae_pos_lawR hpos hB h n] with x hx
      exact power_dom hx (hq j) ((hqθ j).trans (theta_lt_one hB).le)
  · unfold signedMoment
    apply tendsto_integral_of_dominated_convergence
      (fun x => lowerLogBound B + |weightedLog B (theta B) x|)
      (fun j => (measurable_weightedLog B (hq j)).aestronglyMeasurable)
      ((integrable_const _).add hθ) ?_ ?_
    · intro j
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
      rw [Real.norm_eq_abs]
      exact weightedLog_dom_theta hB (hq j) (hqθ j) ((floorSeq_one_le hB hn).trans hx)
    · filter_upwards [hp] with x hx
      exact hx.mul_const (Real.log x - Real.log B)

private theorem endpoint_abs_bound {B x : ℝ} (hB : 2 < B) (hx : floorSeq B 1 ≤ x) :
    |weightedLog B (theta B) x| ≤ weightedLog B (theta B) x + 4 * lowerLogBound B := by
  have hx0 := (floorSeq_one_pos hB).trans_le hx
  have hD := lowerLogBound_nonneg hB
  have hq := theta_pos hB
  by_cases hw : 0 ≤ weightedLog B (theta B) x
  · rw [abs_of_nonneg hw]
    linarith
  have hl : Real.log x - Real.log B < 0 :=
    lt_of_not_ge fun h => hw (mul_nonneg (Real.rpow_nonneg hx0.le _) h)
  have hxB : x ≤ B := by
    by_contra! h
    linarith [Real.log_lt_log (show 0 < B by linarith) h]
  have hp : x ^ theta B ≤ 2 := by rw [← B_rpow_theta hB]; exact Real.rpow_le_rpow hx0.le hxB hq.le
  have hlog : 0 ≤ Real.log B - Real.log x := by linarith
  have hlog' : Real.log B - Real.log x ≤ lowerLogBound B :=
    sub_le_sub_left (Real.log_le_log (floorSeq_one_pos hB) hx) _
  have hc := (mul_le_mul_of_nonneg_right hp hlog).trans
    (mul_le_mul_of_nonneg_left hlog' (by norm_num : 0 ≤ (2 : ℝ)))
  rw [abs_of_nonpos (le_of_not_ge hw)]
  unfold weightedLog
  linarith only [hc, show x ^ theta B * (Real.log B - Real.log x) =
    -(x ^ theta B * (Real.log x - Real.log B)) by ring]

/-- Critical fractional and logarithmic moment bounds with a disorder-independent constant. -/
theorem criticalMoments_aux {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], (∀ᵐ w ∂μ, 0 < w) →
      ∫ w, w ∂μ = 1 → ∀ h : ℝ, freeEnergy μ B h = 0 →
        (∀ n : ℕ, 1 ≤ n →
          tiltedMass μ B h n ≤ (B - 1) ^ theta B ∧
          tiltedLogMoment μ B h 1 n ≤ C * (2 / B) ^ n) ∧
        ∃ M : ℝ, ∀ n : ℕ, absTiltedLogMoment μ B h 1 n ≤ M := by
  obtain ⟨C, hC, hupper⟩ := signedMoment_upper hB
  refine ⟨C, fun μ _ hpos hmean h hF => ?_⟩
  let q := fun j : ℕ => theta B - theta B / 2 * (1 / 2 : ℝ) ^ j
  have hθ := theta_pos hB
  have hqθ (j : ℕ) : q j < theta B := sub_lt_self _ (by positivity)
  have hq (j : ℕ) : 0 < q j := by
    have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hw := mul_le_mul_of_nonneg_left hp (show 0 ≤ theta B / 2 by positivity)
    dsimp [q]
    linarith
  have hlim : Tendsto q atTop (𝓝 (theta B)) := by
    have hw := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (theta B / 2)
    simpa [q] using (tendsto_const_nhds (x := theta B)).sub hw
  have hmain (n : ℕ) (hn : 1 ≤ n) :
      tiltedMass μ B h n ≤ (B - 1) ^ theta B ∧
      signedMoment μ B h n (theta B) ≤ C * (2 / B) ^ n := by
    obtain ⟨hm, hl⟩ := endpoint_limits hpos hmean hB h hn (fun j => (hq j).le)
      (fun j => (hqθ j).le) hlim
    have hc := (Real.continuousAt_const_rpow (a := B - 1) (by linarith)).tendsto.comp hlim
    exact ⟨le_of_tendsto_of_tendsto hm hc (Eventually.of_forall fun j =>
      subcritical_moment_le hpos hmean hB h hF (hq j) (hqθ j) n),
      le_of_tendsto_of_tendsto hl tendsto_const_nhds (Eventually.of_forall fun j =>
        hupper μ hpos hmean h hF (q j) (hq j) (hqθ j) n hn)⟩
  refine ⟨fun n hn => ⟨(hmain n hn).1, ?_⟩, ?_⟩
  · simpa only [tiltedLogMoment, pow_one, signedMoment, weightedLog] using (hmain n hn).2
  refine ⟨max (absTiltedLogMoment μ B h 1 0) (C + 4 * lowerLogBound B), fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    exact le_max_left _ _
  have hn1 : 1 ≤ n := by omega
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  have hi := integrable_weightedLog hpos hmean hB h hn1 hθ.le le_rfl
  have hia := integrable_abs_weighted_theta hpos hmean hB h n
  have habs : (∫ x, |weightedLog B (theta B) x| ∂lawR μ B h n) =
      absTiltedLogMoment μ B h 1 n := by
    unfold absTiltedLogMoment
    apply integral_congr_ae
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    rw [weightedLog, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _), pow_one]
  have hle := integral_mono_ae hia (hi.add (integrable_const (4 * lowerLogBound B)))
    (show ∀ᵐ x ∂lawR μ B h n,
      |weightedLog B (theta B) x| ≤ weightedLog B (theta B) x + 4 * lowerLogBound B from by
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
      exact endpoint_abs_bound hB ((floorSeq_one_le hB hn1).trans hx))
  change (∫ x, |weightedLog B (theta B) x| ∂lawR μ B h n) ≤
    (∫ x, weightedLog B (theta B) x + 4 * lowerLogBound B ∂lawR μ B h n) at hle
  rw [habs, integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul] at hle
  have hρ : (2 / B : ℝ) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (by linarith : 0 < B)).2 hB.le)
  have hu := (hmain n hn1).2.trans
    (mul_le_of_le_one_right hC hρ)
  exact hle.trans ((by
    change signedMoment μ B h n (theta B) + 4 * lowerLogBound B ≤ C + 4 * lowerLogBound B
    linarith : _ ≤ _).trans (le_max_right _ _))

end DiamondPinning
