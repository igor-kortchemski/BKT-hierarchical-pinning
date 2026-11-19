module

public import DiamondPinning.Proofs.HardEscape
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The pair-counting lemma `escape:pairs`

Proof of `escape:pairs` (`source/escape.tex`, lines 52–94). The theorem
`escape_pairs_aux` proves `DiamondPinning.escape_pairs` (in
`DiamondPinning.Statements.Escape`).

The hard recursion is realized on perfect binary trees `HardTree n` (with
`HardTree 0 = ℕ` and `HardTree (n + 1) = HardTree n × HardTree n`) carrying
independent leaf values of law `ν`; the evaluator `hardTreeEval` has law
`hardLaw ν n` (`map_hardTreeEval`). The proof is the source's second-moment
argument, organized recursively on the tree:

* `leafCnt m n t` counts the leaves of value `m`;
* `pairCnt L k I n t` counts (twice) the unordered pairs of leaves with values
  `m, ℓ ∈ I` whose common ancestor has height `d = m + ℓ - L - k + 1`; if it is
  nonzero, then `hardTreeEval n t ≥ L + k - n` (`le_eval_of_pairCnt`);
* the first moment of `pairCnt` is computed exactly, and its second moment is
  bounded by `2 F + F² + 4 S`, where `S ≤ 2^{-k} M_I F` collects the pairs of
  pairs sharing one leaf (the source's partner bound);
* the Paley–Zygmund inequality then gives the claim.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory
open scoped ENNReal

/-! ### Trees, their law and the evaluator -/

/-- Perfect binary trees of height `n` with leaf values in `ℕ`. -/
def HardTree : ℕ → Type
  | 0 => ℕ
  | n + 1 => HardTree n × HardTree n

/-- The product (discrete) σ-algebra on trees. -/
instance HardTree.instMeasurableSpace : (n : ℕ) → MeasurableSpace (HardTree n)
  | 0 => (inferInstance : MeasurableSpace ℕ)
  | n + 1 => @Prod.instMeasurableSpace _ _ (HardTree.instMeasurableSpace n)
      (HardTree.instMeasurableSpace n)

/-- Trees of every finite height with natural leaf values form a countable type. -/
instance HardTree.instCountable : (n : ℕ) → Countable (HardTree n)
  | 0 => inferInstanceAs (Countable ℕ)
  | n + 1 => @instCountableProd _ _ (HardTree.instCountable n) (HardTree.instCountable n)

/-- Every singleton in a finitely generated hard tree is measurable. -/
instance HardTree.instMeasurableSingletonClass :
    (n : ℕ) → MeasurableSingletonClass (HardTree n)
  | 0 => inferInstanceAs (MeasurableSingletonClass ℕ)
  | n + 1 => @Prod.instMeasurableSingletonClass _ _ (HardTree.instMeasurableSpace n)
      (HardTree.instMeasurableSpace n) (HardTree.instMeasurableSingletonClass n)
      (HardTree.instMeasurableSingletonClass n)

/-- The law of a tree of height `n` with independent leaves of law `ν`. -/
noncomputable def hardTreeMeasure (ν : Measure ℕ) : (n : ℕ) → Measure (HardTree n)
  | 0 => ν
  | n + 1 => (hardTreeMeasure ν n).prod (hardTreeMeasure ν n)

/-- Independent leaves of a probability law make the tree law a probability
measure at every height. -/
instance hardTreeMeasure.instIsProbabilityMeasure (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    (n : ℕ) → IsProbabilityMeasure (hardTreeMeasure ν n)
  | 0 => inferInstanceAs (IsProbabilityMeasure ν)
  | n + 1 =>
    have _ := hardTreeMeasure.instIsProbabilityMeasure ν n
    inferInstanceAs (IsProbabilityMeasure ((hardTreeMeasure ν n).prod (hardTreeMeasure ν n)))

/-- The hard recursion evaluated on a tree: the leaf value at height `0`, and
`Y₁ + Y₂ - 1` (in `ℕ`) at a node whose subtrees evaluate to `Y₁, Y₂`. -/
def hardTreeEval : (n : ℕ) → HardTree n → ℕ
  | 0, x => (show ℕ from x)
  | n + 1, t => hardTreeEval n t.1 + hardTreeEval n t.2 - 1

/-- Every function out of a hard tree is measurable for its countable measurable space. -/
theorem measurable_hardTree {n : ℕ} {β : Type*} [MeasurableSpace β]
    (f : HardTree n → β) : Measurable f :=
  measurable_of_countable f

/-- The evaluator of a tree with independent leaves of law `ν` has law `hardLaw ν n`. -/
theorem map_hardTreeEval (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    ∀ n : ℕ, (hardTreeMeasure ν n).map (hardTreeEval n) = hardLaw ν n := by
  intro n
  induction n with
  | zero => exact Measure.map_id'
  | succ n ih =>
      let f : HardTree n × HardTree n → ℕ × ℕ :=
        fun e => (hardTreeEval n e.1, hardTreeEval n e.2)
      let g : ℕ × ℕ → ℕ := fun p => p.1 + p.2 - 1
      have hf : Measurable f := measurable_of_countable f
      have hg : Measurable g := measurable_of_countable g
      change ((hardTreeMeasure ν n).prod (hardTreeMeasure ν n)).map (g ∘ f) =
        ((hardLaw ν n).prod (hardLaw ν n)).map g
      calc
        ((hardTreeMeasure ν n).prod (hardTreeMeasure ν n)).map (g ∘ f) =
            (((hardTreeMeasure ν n).prod (hardTreeMeasure ν n)).map f).map g := by
              rw [← Measure.map_map hg hf]
        _ = (((hardTreeMeasure ν n).map (hardTreeEval n)).prod
              ((hardTreeMeasure ν n).map (hardTreeEval n))).map g := by
              congr 1
              rw [Measure.map_prod_map (hardTreeMeasure ν n) (hardTreeMeasure ν n)
                (measurable_hardTree _) (measurable_hardTree _)]
              rfl
        _ = ((hardLaw ν n).prod (hardLaw ν n)).map g := by rw [ih]

/-! ### Integration on trees -/

section Integrals

variable (ν : Measure ℕ)

/-- Lower integration over a hard-tree law commutes with addition of
extended-nonnegative functions. -/
theorem lintegral_hardTree_add {n : ℕ} (f g : HardTree n → ℝ≥0∞) :
    ∫⁻ t, f t + g t ∂(hardTreeMeasure ν n) =
      ∫⁻ t, f t ∂(hardTreeMeasure ν n) + ∫⁻ t, g t ∂(hardTreeMeasure ν n) :=
  lintegral_add_left (measurable_hardTree f) g

/-- Lower integration over a hard-tree law commutes with multiplication by a constant. -/
theorem lintegral_hardTree_const_mul {n : ℕ} (c : ℝ≥0∞) (f : HardTree n → ℝ≥0∞) :
    ∫⁻ t, c * f t ∂(hardTreeMeasure ν n) = c * ∫⁻ t, f t ∂(hardTreeMeasure ν n) :=
  lintegral_const_mul c (measurable_hardTree f)

/-- Lower integration over a hard-tree law commutes with finite sums. -/
theorem lintegral_hardTree_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → HardTree n → ℝ≥0∞) :
    ∫⁻ t, ∑ i ∈ s, f i t ∂(hardTreeMeasure ν n) =
      ∑ i ∈ s, ∫⁻ t, f i t ∂(hardTreeMeasure ν n) :=
  lintegral_finsetSum s fun i _ => measurable_hardTree (f i)

/-- Functions of the two independent subtrees integrate to the product of
their separate integrals. -/
theorem lintegral_hardTree_mul {n : ℕ} (f g : HardTree n → ℝ≥0∞) :
    ∫⁻ t : HardTree (n + 1), f t.1 * g t.2 ∂(hardTreeMeasure ν (n + 1)) =
      (∫⁻ x, f x ∂(hardTreeMeasure ν n)) * ∫⁻ x, g x ∂(hardTreeMeasure ν n) :=
  lintegral_prod_mul (measurable_hardTree f).aemeasurable (measurable_hardTree g).aemeasurable

/-- A function of the first subtree has the same integral under the product tree law. -/
theorem lintegral_hardTree_fst [IsProbabilityMeasure ν] {n : ℕ} (f : HardTree n → ℝ≥0∞) :
    ∫⁻ t : HardTree (n + 1), f t.1 ∂(hardTreeMeasure ν (n + 1)) =
      ∫⁻ x, f x ∂(hardTreeMeasure ν n) := by
  have h := lintegral_hardTree_mul ν f (fun _ => 1)
  simpa using h

/-- A function of the second subtree has the same integral under the product tree law. -/
theorem lintegral_hardTree_snd [IsProbabilityMeasure ν] {n : ℕ} (f : HardTree n → ℝ≥0∞) :
    ∫⁻ t : HardTree (n + 1), f t.2 ∂(hardTreeMeasure ν (n + 1)) =
      ∫⁻ x, f x ∂(hardTreeMeasure ν n) := by
  have h := lintegral_hardTree_mul ν (fun _ => 1) f
  simpa using h

/-- Integrals of finite sums of products split across the two independent
subtrees. -/
theorem lintegral_hardTree_sum_mul {n : ℕ} {ι : Type*} (s : Finset ι)
    (f g : ι → HardTree n → ℝ≥0∞) :
    ∫⁻ t : HardTree (n + 1), ∑ i ∈ s, f i t.1 * g i t.2 ∂(hardTreeMeasure ν (n + 1)) =
      ∑ i ∈ s, (∫⁻ x, f i x ∂(hardTreeMeasure ν n)) *
        ∫⁻ x, g i x ∂(hardTreeMeasure ν n) := by
  rw [lintegral_hardTree_sum]
  exact Finset.sum_congr rfl fun i _ => lintegral_hardTree_mul ν (f i) (g i)

end Integrals

/-! ### Leaf counts -/

/-- The number of leaves of value `m` of a tree. -/
noncomputable def leafCnt (m : ℕ) : (n : ℕ) → HardTree n → ℝ≥0∞
  | 0, x => if (show ℕ from x) = m then 1 else 0
  | n + 1, t => leafCnt m n t.1 + leafCnt m n t.2

/-- At a branching node, the leaf count is the sum of the counts in its two subtrees. -/
theorem leafCnt_succ (m n : ℕ) (t : HardTree (n + 1)) :
    leafCnt m (n + 1) t = leafCnt m n t.1 + leafCnt m n t.2 := rfl

/-- A leaf of value `m` at depth `n` forces the value `m - n` at the root. -/
theorem le_eval_of_leafCnt (m : ℕ) :
    ∀ (n : ℕ) (t : HardTree n), leafCnt m n t ≠ 0 → m - n ≤ hardTreeEval n t
  | 0, x, h => by
      have key : ∀ y : ℕ, (if y = m then (1 : ℝ≥0∞) else 0) ≠ 0 → m - 0 ≤ y := by
        intro y hy
        split_ifs at hy with hym
        · omega
        · exact absurd rfl hy
      exact key x h
  | n + 1, t, h => by
      rw [leafCnt_succ] at h
      have h' : leafCnt m n t.1 ≠ 0 ∨ leafCnt m n t.2 ≠ 0 := by
        by_contra hc
        rw [not_or, not_not, not_not] at hc
        exact h (by rw [hc.1, hc.2, add_zero])
      change m - (n + 1) ≤ hardTreeEval n t.1 + hardTreeEval n t.2 - 1
      rcases h' with h1 | h2
      · have := le_eval_of_leafCnt m n t.1 h1
        omega
      · have := le_eval_of_leafCnt m n t.2 h2
        omega

section LeafMoments

variable (ν : Measure ℕ) [IsProbabilityMeasure ν]

/-- The mean number of leaves of value `m` at height `n` is `2^n ν {m}`. -/
theorem lintegral_leafCnt (m : ℕ) : ∀ n : ℕ,
    ∫⁻ t, leafCnt m n t ∂(hardTreeMeasure ν n) = 2 ^ n * ν {m}
  | 0 => by
      have h : (fun x : ℕ => if x = m then (1 : ℝ≥0∞) else 0) = Set.indicator {m} 1 := by
        ext x
        simp [Set.indicator_apply]
      change ∫⁻ x : ℕ, (if x = m then (1 : ℝ≥0∞) else 0) ∂ν = 2 ^ 0 * ν {m}
      rw [h, lintegral_indicator_one (measurableSet_singleton m)]
      simp
  | n + 1 => by
      simp only [leafCnt_succ]
      rw [lintegral_hardTree_add, lintegral_hardTree_fst ν (leafCnt m n),
        lintegral_hardTree_snd ν (leafCnt m n), lintegral_leafCnt m n]
      ring

/-- Second moments of leaf counts: `E[A_m A_{m'}] ≤ 1{m = m'} 2^n p_m + 4^n p_m p_{m'}`. -/
theorem lintegral_leafCnt_mul_le (m m' : ℕ) : ∀ n : ℕ,
    ∫⁻ t, leafCnt m n t * leafCnt m' n t ∂(hardTreeMeasure ν n) ≤
      (if m = m' then 2 ^ n * ν {m} else 0) + (2 ^ n * ν {m}) * (2 ^ n * ν {m'})
  | 0 => by
      change ∫⁻ x : ℕ, (if x = m then (1 : ℝ≥0∞) else 0) *
        (if x = m' then 1 else 0) ∂ν ≤ _
      by_cases hmm : m = m'
      · subst hmm
        have h : (fun x : ℕ => (if x = m then (1 : ℝ≥0∞) else 0) *
            (if x = m then 1 else 0)) =
            Set.indicator {m} 1 := by
          ext x
          by_cases hx : x = m <;> simp [hx]
        rw [h, lintegral_indicator_one (measurableSet_singleton m)]
        simp
      · have h : (fun x : ℕ => (if x = m then (1 : ℝ≥0∞) else 0) *
            (if x = m' then 1 else 0)) =
            fun _ => 0 := by
          ext x
          by_cases hx : x = m
          · subst hx
            simp [hmm]
          · simp [hx]
        rw [h]
        simp
  | n + 1 => by
      have hpt : ∀ t : HardTree (n + 1), leafCnt m (n + 1) t * leafCnt m' (n + 1) t =
          leafCnt m n t.1 * leafCnt m' n t.1 + leafCnt m n t.2 * leafCnt m' n t.2 +
          (leafCnt m n t.1 * leafCnt m' n t.2 + leafCnt m' n t.1 * leafCnt m n t.2) := by
        intro t
        rw [leafCnt_succ, leafCnt_succ]
        ring
      simp_rw [hpt]
      rw [lintegral_hardTree_add, lintegral_hardTree_add, lintegral_hardTree_add,
        lintegral_hardTree_fst ν (fun x => leafCnt m n x * leafCnt m' n x),
        lintegral_hardTree_snd ν (fun x => leafCnt m n x * leafCnt m' n x),
        lintegral_hardTree_mul ν (leafCnt m n) (leafCnt m' n),
        lintegral_hardTree_mul ν (leafCnt m' n) (leafCnt m n),
        lintegral_leafCnt, lintegral_leafCnt]
      have ih := lintegral_leafCnt_mul_le m m' n
      calc _ ≤ ((if m = m' then 2 ^ n * ν {m} else 0) + (2 ^ n * ν {m}) * (2 ^ n * ν {m'})) +
            ((if m = m' then 2 ^ n * ν {m} else 0) + (2 ^ n * ν {m}) * (2 ^ n * ν {m'})) +
            ((2 ^ n * ν {m}) * (2 ^ n * ν {m'}) + (2 ^ n * ν {m'}) * (2 ^ n * ν {m})) := by
              gcongr
        _ = _ := by split_ifs <;> ring

/-- The bilinear bound for linear forms in the leaf counts:
`E[(∑ c_i A_i)(∑ d_j A_j)] ≤ ∑ c_i d_i α_i + (∑ c_i α_i)(∑ d_j α_j)`,
`α_i = 2^n p_i`. -/
theorem lintegral_linLeaf_mul_le (n : ℕ) (s : Finset ℕ) (c d : ℕ → ℝ≥0∞) :
    ∫⁻ t, (∑ i ∈ s, c i * leafCnt i n t) * (∑ j ∈ s, d j * leafCnt j n t)
        ∂(hardTreeMeasure ν n) ≤
      ∑ i ∈ s, c i * d i * (2 ^ n * ν {i}) +
        (∑ i ∈ s, c i * (2 ^ n * ν {i})) * ∑ j ∈ s, d j * (2 ^ n * ν {j}) := by
  have hpt : ∀ t, (∑ i ∈ s, c i * leafCnt i n t) * (∑ j ∈ s, d j * leafCnt j n t) =
      ∑ i ∈ s, ∑ j ∈ s, c i * d j * (leafCnt i n t * leafCnt j n t) := by
    intro t
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  rw [lintegral_hardTree_sum]
  calc ∑ i ∈ s, ∫⁻ t, ∑ j ∈ s, c i * d j * (leafCnt i n t * leafCnt j n t)
        ∂(hardTreeMeasure ν n)
      = ∑ i ∈ s, ∑ j ∈ s, c i * d j *
          ∫⁻ t, leafCnt i n t * leafCnt j n t ∂(hardTreeMeasure ν n) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_hardTree_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_hardTree_const_mul]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, c i * d j *
          ((if i = j then 2 ^ n * ν {i} else 0) + (2 ^ n * ν {i}) * (2 ^ n * ν {j})) := by
        gcongr with i _ j _
        exact lintegral_leafCnt_mul_le ν i j n
    _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          simp_rw [mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp [hi]
        · rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end LeafMoments

/-! ### Pair counts

Fix `L, k` and the band `I`. A leaf of value `m` and a leaf of value `ℓ` in the
two subtrees of a node of height `n + 1` form a counted pair when
`m + ℓ = n + L + k`, that is, when the node has height
`d = m + ℓ - L - k + 1` (the source's choice, which makes the root value at
least `k` at height `L`). -/

/-- The pair indicator `1{m + ℓ = n + L + k}`. -/
noncomputable def pairInd (L k n m ℓ : ℕ) : ℝ≥0∞ := if m + ℓ = n + L + k then 1 else 0

/-- The pair indicator is unchanged by exchanging the two leaf values. -/
theorem pairInd_comm (L k n m ℓ : ℕ) : pairInd L k n m ℓ = pairInd L k n ℓ m := by
  simp only [pairInd, add_comm m ℓ]

/-- The pair indicator is idempotent under multiplication. -/
theorem pairInd_mul_self (L k n m ℓ : ℕ) :
    pairInd L k n m ℓ * pairInd L k n m ℓ = pairInd L k n m ℓ := by
  unfold pairInd
  split_ifs <;> simp

/-- The number of leaves of `t` (height `n`) that pair with a leaf of value `m`
at a node of height `n + 1`. -/
noncomputable def partnerCnt (L k : ℕ) (I : Finset ℕ) (n m : ℕ)
    (t : HardTree n) : ℝ≥0∞ :=
  ∑ ℓ ∈ I, pairInd L k n m ℓ * leafCnt ℓ n t

/-- Twice the number of counted unordered pairs of leaves of a tree. -/
noncomputable def pairCnt (L k : ℕ) (I : Finset ℕ) : (n : ℕ) → HardTree n → ℝ≥0∞
  | 0, _ => 0
  | n + 1, t => pairCnt L k I n t.1 + pairCnt L k I n t.2 +
      2 * ∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2

/-- A height-zero tree contains no counted pair. -/
theorem pairCnt_zero (L k : ℕ) (I : Finset ℕ) (t : HardTree 0) : pairCnt L k I 0 t = 0 := rfl

/-- The pair count at a branching node adds the two subtree counts and the new cross-pairs. -/
theorem pairCnt_succ (L k : ℕ) (I : Finset ℕ) (n : ℕ) (t : HardTree (n + 1)) :
    pairCnt L k I (n + 1) t = pairCnt L k I n t.1 + pairCnt L k I n t.2 +
      2 * ∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2 := rfl

/-- A counted pair in a tree of height `n` forces the value `L + k - n` at its root
(when all values of the band are at most `L`). -/
theorem le_eval_of_pairCnt {L k : ℕ} {I : Finset ℕ} (hI : ∀ ℓ ∈ I, ℓ ≤ L) :
    ∀ (n : ℕ) (t : HardTree n), pairCnt L k I n t ≠ 0 → L + k - n ≤ hardTreeEval n t
  | 0, _, h => absurd rfl h
  | n + 1, t, h => by
      rw [pairCnt_succ] at h
      change L + k - (n + 1) ≤ hardTreeEval n t.1 + hardTreeEval n t.2 - 1
      by_cases h1 : pairCnt L k I n t.1 = 0
      · by_cases h2 : pairCnt L k I n t.2 = 0
        · rw [h1, h2, zero_add, zero_add] at h
          have hs : ∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2 ≠ 0 :=
            right_ne_zero_of_mul h
          obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
          have hA : leafCnt m n t.1 ≠ 0 := left_ne_zero_of_mul hm0
          have hR : partnerCnt L k I n m t.2 ≠ 0 := right_ne_zero_of_mul hm0
          obtain ⟨ℓ, hℓ, hℓ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hR
          have hind : pairInd L k n m ℓ ≠ 0 := left_ne_zero_of_mul hℓ0
          have hB : leafCnt ℓ n t.2 ≠ 0 := right_ne_zero_of_mul hℓ0
          have hsum : m + ℓ = n + L + k := by
            by_contra hc
            exact hind (by simp [pairInd, hc])
          have e1 := le_eval_of_leafCnt m n t.1 hA
          have e2 := le_eval_of_leafCnt ℓ n t.2 hB
          have hmL := hI m hm
          have hℓL := hI ℓ hℓ
          omega
        · have := le_eval_of_pairCnt hI n t.2 h2
          omega
      · have := le_eval_of_pairCnt hI n t.1 h1
        omega

/-! ### Deterministic weights -/

/-- `δ_n(m) = ∑_{ℓ ∈ I} 1{m + ℓ = n + L + k} 2^n p_ℓ`, the mean partner count. -/
noncomputable def partnerW (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ)
    (n m : ℕ) : ℝ≥0∞ :=
  ∑ ℓ ∈ I, pairInd L k n m ℓ * (2 ^ n * ν {ℓ})

/-- `γ_n(m) = ∑_{j < n} δ_j(m)`: the mean number of partners of a leaf of value
`m` in a tree of height `n`. -/
noncomputable def partnerAcc (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ) :
    ℕ → ℕ → ℝ≥0∞
  | 0, _ => 0
  | n + 1, m => partnerAcc ν L k I n m + partnerW ν L k I n m

/-- The accumulated partner weight gains the current node weight at each height. -/
theorem partnerAcc_succ (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ) (n m : ℕ) :
    partnerAcc ν L k I (n + 1) m = partnerAcc ν L k I n m + partnerW ν L k I n m := rfl

/-- `F_n = ∑_{m ∈ I} 2^n p_m γ_n(m)`, the mean of `pairCnt`. -/
noncomputable def pairMean (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ I, 2 ^ n * ν {m} * partnerAcc ν L k I n m

/-- `S_n = ∑_{m ∈ I} 2^n p_m γ_n(m)²`, the mean contribution of pairs of pairs
sharing a leaf. -/
noncomputable def pairShare (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ)
    (n : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ I, 2 ^ n * ν {m} * partnerAcc ν L k I n m ^ 2

/-- `E_n = ∑_{m ∈ I} 2^n p_m δ_n(m)`, the mean number of new pairs at a node. -/
noncomputable def pairCross (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ)
    (n : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ I, 2 ^ n * ν {m} * partnerW ν L k I n m

/-- The mean pair count satisfies the height recursion `Fₙ₊₁ = 2Fₙ + 2Eₙ`. -/
theorem pairMean_succ (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ) (n : ℕ) :
    pairMean ν L k I (n + 1) = 2 * pairMean ν L k I n + 2 * pairCross ν L k I n := by
  simp only [pairMean, pairCross, partnerAcc_succ]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- The shared-leaf second-moment weight expands recursively into accumulated
and current partner weights. -/
theorem pairShare_succ (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ) (n : ℕ) :
    pairShare ν L k I (n + 1) = 2 * pairShare ν L k I n +
      4 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerAcc ν L k I n m * partnerW ν L k I n m +
      2 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerW ν L k I n m ^ 2 := by
  simp only [pairShare, partnerAcc_succ]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- Exchanging the two leaves of a pair:
`∑_m 2^n p_m ∑_ℓ 1{m+ℓ=N} f(ℓ) = ∑_ℓ f(ℓ) δ_n(ℓ)`. -/
theorem sum_pairInd_swap (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ)
    (n : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑ m ∈ I, 2 ^ n * ν {m} * ∑ ℓ ∈ I, pairInd L k n m ℓ * f ℓ =
      ∑ ℓ ∈ I, f ℓ * partnerW ν L k I n ℓ := by
  simp only [partnerW, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun m _ => ?_
  rw [pairInd_comm]
  ring

/-! ### First moments -/

section FirstMoments

variable (ν : Measure ℕ) [IsProbabilityMeasure ν] (L k : ℕ) (I : Finset ℕ)

/-- The expected partner count equals the deterministic partner weight. -/
theorem lintegral_partnerCnt (n m : ℕ) :
    ∫⁻ t, partnerCnt L k I n m t ∂(hardTreeMeasure ν n) = partnerW ν L k I n m := by
  unfold partnerCnt partnerW
  rw [lintegral_hardTree_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [lintegral_hardTree_const_mul, lintegral_leafCnt]

/-- The first moment of the pair count: `E Z_n = F_n`. -/
theorem lintegral_pairCnt : ∀ n : ℕ,
    ∫⁻ t, pairCnt L k I n t ∂(hardTreeMeasure ν n) = pairMean ν L k I n
  | 0 => by
      simp [pairCnt_zero, pairMean, partnerAcc]
  | n + 1 => by
      simp only [pairCnt_succ]
      rw [lintegral_hardTree_add, lintegral_hardTree_add, lintegral_hardTree_const_mul,
        lintegral_hardTree_fst ν (pairCnt L k I n), lintegral_hardTree_snd ν (pairCnt L k I n),
        lintegral_hardTree_sum_mul ν I (fun m => leafCnt m n)
          (fun m => partnerCnt L k I n m), lintegral_pairCnt n, pairMean_succ]
      simp only [lintegral_leafCnt, lintegral_partnerCnt, pairCross]
      ring

/-! ### Mixed moments -/

/-- `E[R_m A_r] ≤ 1{m + r = N} α_r + δ_m α_r` for `r ∈ I`. -/
theorem lintegral_partnerCnt_mul_leafCnt_le (n m r : ℕ) (hr : r ∈ I) :
    ∫⁻ t, partnerCnt L k I n m t * leafCnt r n t ∂(hardTreeMeasure ν n) ≤
      pairInd L k n m r * (2 ^ n * ν {r}) + partnerW ν L k I n m * (2 ^ n * ν {r}) := by
  have hpt : ∀ t, partnerCnt L k I n m t * leafCnt r n t =
      ∑ ℓ ∈ I, pairInd L k n m ℓ * (leafCnt ℓ n t * leafCnt r n t) := by
    intro t
    rw [partnerCnt, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  simp_rw [hpt]
  rw [lintegral_hardTree_sum]
  calc ∑ ℓ ∈ I, ∫⁻ t, pairInd L k n m ℓ * (leafCnt ℓ n t * leafCnt r n t)
        ∂(hardTreeMeasure ν n)
      = ∑ ℓ ∈ I, pairInd L k n m ℓ *
          ∫⁻ t, leafCnt ℓ n t * leafCnt r n t ∂(hardTreeMeasure ν n) :=
        Finset.sum_congr rfl fun ℓ _ => lintegral_hardTree_const_mul ν _ _
    _ ≤ ∑ ℓ ∈ I, pairInd L k n m ℓ *
          ((if ℓ = r then 2 ^ n * ν {ℓ} else 0) + (2 ^ n * ν {ℓ}) * (2 ^ n * ν {r})) := by
        gcongr with ℓ _
        exact lintegral_leafCnt_mul_le ν ℓ r n
    _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq' I r, ite_eq_left hr, partnerW, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- `∑_m E[A_m A_r] δ_m ≤ α_r δ_r + α_r E_n` for `r ∈ I`. -/
theorem sum_lintegral_leafCnt_mul_le (n r : ℕ) (hr : r ∈ I) :
    ∑ m ∈ I, (∫⁻ t, leafCnt m n t * leafCnt r n t ∂(hardTreeMeasure ν n)) *
        partnerW ν L k I n m ≤
      2 ^ n * ν {r} * partnerW ν L k I n r + 2 ^ n * ν {r} * pairCross ν L k I n := by
  calc _ ≤ ∑ m ∈ I, ((if m = r then 2 ^ n * ν {m} else 0) +
        (2 ^ n * ν {m}) * (2 ^ n * ν {r})) *
        partnerW ν L k I n m := by
        gcongr with m _
        exact lintegral_leafCnt_mul_le ν m r n
    _ = _ := by
        simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq' I r, ite_eq_left hr, pairCross, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun m _ => by ring

/-- `∑_m α_m E[R_m A_r] ≤ α_r δ_r + α_r E_n` for `r ∈ I`. -/
theorem sum_lintegral_partnerCnt_mul_le (n r : ℕ) (hr : r ∈ I) :
    ∑ m ∈ I, 2 ^ n * ν {m} *
        ∫⁻ t, partnerCnt L k I n m t * leafCnt r n t ∂(hardTreeMeasure ν n) ≤
      2 ^ n * ν {r} * partnerW ν L k I n r + 2 ^ n * ν {r} * pairCross ν L k I n := by
  calc _ ≤ ∑ m ∈ I, 2 ^ n * ν {m} *
        (pairInd L k n m r * (2 ^ n * ν {r}) + partnerW ν L k I n m * (2 ^ n * ν {r})) := by
        gcongr with m _
        exact lintegral_partnerCnt_mul_leafCnt_le ν L k I n m r hr
    _ = _ := by
        rw [show partnerW ν L k I n r = ∑ m ∈ I, pairInd L k n r m * (2 ^ n * ν {m}) from rfl,
          pairCross, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [pairInd_comm]
        ring

/-- The mixed moment `E[Z_n A_r] ≤ α_r F_n + 2 α_r γ_n(r)` for `r ∈ I`. -/
theorem lintegral_pairCnt_mul_leafCnt_le (r : ℕ) (hr : r ∈ I) : ∀ n : ℕ,
    ∫⁻ t, pairCnt L k I n t * leafCnt r n t ∂(hardTreeMeasure ν n) ≤
      2 ^ n * ν {r} * pairMean ν L k I n + 2 * (2 ^ n * ν {r} * partnerAcc ν L k I n r)
  | 0 => by simp [pairCnt_zero]
  | n + 1 => by
      have hpt : ∀ t : HardTree (n + 1), pairCnt L k I (n + 1) t * leafCnt r (n + 1) t =
          pairCnt L k I n t.1 * leafCnt r n t.1 + pairCnt L k I n t.2 * leafCnt r n t.2 +
          pairCnt L k I n t.1 * leafCnt r n t.2 + leafCnt r n t.1 * pairCnt L k I n t.2 +
          2 * ∑ m ∈ I, (leafCnt m n t.1 * leafCnt r n t.1) * partnerCnt L k I n m t.2 +
          2 * ∑ m ∈ I, leafCnt m n t.1 * (partnerCnt L k I n m t.2 * leafCnt r n t.2) := by
        intro t
        rw [pairCnt_succ, leafCnt_succ]
        have h1 : (∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2) * leafCnt r n t.1 =
            ∑ m ∈ I, (leafCnt m n t.1 * leafCnt r n t.1) * partnerCnt L k I n m t.2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => by ring
        have h2 : (∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2) * leafCnt r n t.2 =
            ∑ m ∈ I, leafCnt m n t.1 * (partnerCnt L k I n m t.2 * leafCnt r n t.2) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => by ring
        rw [← h1, ← h2]
        ring
      simp_rw [hpt]
      rw [lintegral_hardTree_add, lintegral_hardTree_add, lintegral_hardTree_add,
        lintegral_hardTree_add, lintegral_hardTree_add,
        lintegral_hardTree_const_mul, lintegral_hardTree_const_mul,
        lintegral_hardTree_fst ν (fun x => pairCnt L k I n x * leafCnt r n x),
        lintegral_hardTree_snd ν (fun x => pairCnt L k I n x * leafCnt r n x),
        lintegral_hardTree_mul ν (pairCnt L k I n) (leafCnt r n),
        lintegral_hardTree_mul ν (leafCnt r n) (pairCnt L k I n),
        lintegral_hardTree_sum_mul ν I (fun m x => leafCnt m n x * leafCnt r n x)
          (fun m => partnerCnt L k I n m),
        lintegral_hardTree_sum_mul ν I (fun m => leafCnt m n)
          (fun m x => partnerCnt L k I n m x * leafCnt r n x),
        lintegral_pairCnt, lintegral_leafCnt]
      simp only [lintegral_partnerCnt, lintegral_leafCnt]
      have ih := lintegral_pairCnt_mul_leafCnt_le r hr n
      have hX := sum_lintegral_leafCnt_mul_le ν L k I n r hr
      have hY := sum_lintegral_partnerCnt_mul_le ν L k I n r hr
      calc _ ≤ (2 ^ n * ν {r} * pairMean ν L k I n +
              2 * (2 ^ n * ν {r} * partnerAcc ν L k I n r)) +
            (2 ^ n * ν {r} * pairMean ν L k I n +
              2 * (2 ^ n * ν {r} * partnerAcc ν L k I n r)) +
            pairMean ν L k I n * (2 ^ n * ν {r}) + 2 ^ n * ν {r} * pairMean ν L k I n +
            2 * (2 ^ n * ν {r} * partnerW ν L k I n r + 2 ^ n * ν {r} * pairCross ν L k I n) +
            2 * (2 ^ n * ν {r} * partnerW ν L k I n r +
              2 ^ n * ν {r} * pairCross ν L k I n) := by
            gcongr
        _ = _ := by
            rw [pairMean_succ, partnerAcc_succ]
            ring

/-! ### Second moments -/

/-- `E[Z_n R_m] ≤ δ_m F_n + 2 ∑_ℓ 1{m + ℓ = N} α_ℓ γ_n(ℓ)`. -/
theorem lintegral_pairCnt_mul_partnerCnt_le (n m : ℕ) :
    ∫⁻ t, pairCnt L k I n t * partnerCnt L k I n m t ∂(hardTreeMeasure ν n) ≤
      partnerW ν L k I n m * pairMean ν L k I n +
        2 * ∑ ℓ ∈ I, pairInd L k n m ℓ *
          (2 ^ n * ν {ℓ} * partnerAcc ν L k I n ℓ) := by
  have hpt : ∀ t, pairCnt L k I n t * partnerCnt L k I n m t =
      ∑ ℓ ∈ I, pairInd L k n m ℓ * (pairCnt L k I n t * leafCnt ℓ n t) := by
    intro t
    rw [partnerCnt, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  simp_rw [hpt]
  rw [lintegral_hardTree_sum]
  calc ∑ ℓ ∈ I, ∫⁻ t, pairInd L k n m ℓ * (pairCnt L k I n t * leafCnt ℓ n t)
        ∂(hardTreeMeasure ν n)
      = ∑ ℓ ∈ I, pairInd L k n m ℓ *
          ∫⁻ t, pairCnt L k I n t * leafCnt ℓ n t ∂(hardTreeMeasure ν n) :=
        Finset.sum_congr rfl fun ℓ _ => lintegral_hardTree_const_mul ν _ _
    _ ≤ ∑ ℓ ∈ I, pairInd L k n m ℓ * (2 ^ n * ν {ℓ} * pairMean ν L k I n +
          2 * (2 ^ n * ν {ℓ} * partnerAcc ν L k I n ℓ)) := by
        gcongr with ℓ hℓ
        exact lintegral_pairCnt_mul_leafCnt_le ν L k I ℓ hℓ n
    _ = _ := by
        rw [partnerW, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- `E[R_m²] ≤ δ_m + δ_m²`. -/
theorem lintegral_partnerCnt_sq_le (n m : ℕ) :
    ∫⁻ t, partnerCnt L k I n m t * partnerCnt L k I n m t ∂(hardTreeMeasure ν n) ≤
      partnerW ν L k I n m + partnerW ν L k I n m * partnerW ν L k I n m := by
  have h := lintegral_linLeaf_mul_le ν n I (pairInd L k n m) (pairInd L k n m)
  simp only [pairInd_mul_self] at h
  exact h

omit [IsProbabilityMeasure ν] in
/-- `∑_m R_m α_m = ∑_ℓ δ_ℓ A_ℓ`. -/
theorem sum_partnerCnt_mul_eq (n : ℕ) (t : HardTree n) :
    ∑ m ∈ I, partnerCnt L k I n m t * (2 ^ n * ν {m}) =
      ∑ ℓ ∈ I, partnerW ν L k I n ℓ * leafCnt ℓ n t := by
  simp only [partnerCnt, partnerW, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun m _ => ?_
  rw [pairInd_comm]
  ring

/-- `E[(∑_m α_m R_m)²] ≤ ∑_ℓ α_ℓ δ_ℓ² + E_n²`. -/
theorem lintegral_sum_partnerCnt_sq_le (n : ℕ) :
    ∫⁻ t, (∑ m ∈ I, partnerCnt L k I n m t * (2 ^ n * ν {m})) *
        (∑ m ∈ I, partnerCnt L k I n m t * (2 ^ n * ν {m})) ∂(hardTreeMeasure ν n) ≤
      ∑ ℓ ∈ I, 2 ^ n * ν {ℓ} * partnerW ν L k I n ℓ ^ 2 +
        pairCross ν L k I n * pairCross ν L k I n := by
  simp_rw [sum_partnerCnt_mul_eq ν L k I n]
  calc _ ≤ _ := lintegral_linLeaf_mul_le ν n I (partnerW ν L k I n) (partnerW ν L k I n)
    _ = _ := by
      simp only [pairCross]
      congr 1
      · exact Finset.sum_congr rfl fun ℓ _ => by ring
      · congr 1 <;> exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- The new pairs at the root:
`E[(∑_m A_m(t₁) R_m(t₂))²] ≤ E_n + 2 ∑_m α_m δ_m² + E_n²`. -/
theorem lintegral_cross_sq_le (n : ℕ) :
    ∫⁻ t : HardTree (n + 1), (∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2) ^ 2
        ∂(hardTreeMeasure ν (n + 1)) ≤
      pairCross ν L k I n + 2 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerW ν L k I n m ^ 2 +
        pairCross ν L k I n ^ 2 := by
  change ∫⁻ p : HardTree n × HardTree n,
      (∑ m ∈ I, leafCnt m n p.1 * partnerCnt L k I n m p.2) ^ 2
        ∂((hardTreeMeasure ν n).prod (hardTreeMeasure ν n)) ≤ _
  rw [lintegral_prod_symm _ (measurable_of_countable _).aemeasurable]
  calc _ ≤ ∫⁻ b, (∑ m ∈ I, partnerCnt L k I n m b * partnerCnt L k I n m b *
        (2 ^ n * ν {m}) +
          (∑ m ∈ I, partnerCnt L k I n m b * (2 ^ n * ν {m})) *
            ∑ m ∈ I, partnerCnt L k I n m b * (2 ^ n * ν {m})) ∂(hardTreeMeasure ν n) := by
        refine lintegral_mono fun b => ?_
        dsimp only
        have hsq : ∀ a : HardTree n, (∑ m ∈ I, leafCnt m n a * partnerCnt L k I n m b) ^ 2 =
            (∑ m ∈ I, partnerCnt L k I n m b * leafCnt m n a) *
              (∑ m ∈ I, partnerCnt L k I n m b * leafCnt m n a) := by
          intro a
          rw [sq]
          congr 1 <;> exact Finset.sum_congr rfl fun m _ => mul_comm _ _
        simp_rw [hsq]
        exact lintegral_linLeaf_mul_le ν n I (fun m => partnerCnt L k I n m b)
          (fun m => partnerCnt L k I n m b)
    _ = ∑ m ∈ I, 2 ^ n * ν {m} *
            ∫⁻ b, partnerCnt L k I n m b * partnerCnt L k I n m b ∂(hardTreeMeasure ν n) +
          ∫⁻ b, (∑ m ∈ I, partnerCnt L k I n m b * (2 ^ n * ν {m})) *
            (∑ m ∈ I, partnerCnt L k I n m b * (2 ^ n * ν {m})) ∂(hardTreeMeasure ν n) := by
        rw [lintegral_hardTree_add, lintegral_hardTree_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← lintegral_hardTree_const_mul]
        congr 1
        funext b
        ring
    _ ≤ ∑ m ∈ I, 2 ^ n * ν {m} *
            (partnerW ν L k I n m + partnerW ν L k I n m * partnerW ν L k I n m) +
          (∑ ℓ ∈ I, 2 ^ n * ν {ℓ} * partnerW ν L k I n ℓ ^ 2 +
            pairCross ν L k I n * pairCross ν L k I n) := by
        gcongr with m _
        · exact lintegral_partnerCnt_sq_le ν L k I n m
        · exact lintegral_sum_partnerCnt_sq_le ν L k I n
    _ = _ := by
        rw [show ∑ m ∈ I, 2 ^ n * ν {m} *
            (partnerW ν L k I n m + partnerW ν L k I n m * partnerW ν L k I n m) =
            pairCross ν L k I n + ∑ m ∈ I, 2 ^ n * ν {m} * partnerW ν L k I n m ^ 2 by
          rw [pairCross, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun m _ => by ring]
        ring

/-- The second moment of the pair count: `E[Z_n²] ≤ 2 F_n + F_n² + 4 S_n`. -/
theorem lintegral_pairCnt_sq_le : ∀ n : ℕ,
    ∫⁻ t, pairCnt L k I n t ^ 2 ∂(hardTreeMeasure ν n) ≤
      2 * pairMean ν L k I n + pairMean ν L k I n ^ 2 + 4 * pairShare ν L k I n
  | 0 => by simp [pairCnt_zero]
  | n + 1 => by
      have hpt : ∀ t : HardTree (n + 1), pairCnt L k I (n + 1) t ^ 2 =
          pairCnt L k I n t.1 ^ 2 + pairCnt L k I n t.2 ^ 2 +
          2 * (pairCnt L k I n t.1 * pairCnt L k I n t.2) +
          4 * ∑ m ∈ I, (pairCnt L k I n t.1 * leafCnt m n t.1) * partnerCnt L k I n m t.2 +
          4 * ∑ m ∈ I, leafCnt m n t.1 * (pairCnt L k I n t.2 * partnerCnt L k I n m t.2) +
          4 * (∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2) ^ 2 := by
        intro t
        rw [pairCnt_succ]
        have h1 : pairCnt L k I n t.1 * (∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2) =
            ∑ m ∈ I, (pairCnt L k I n t.1 * leafCnt m n t.1) * partnerCnt L k I n m t.2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        have h2 : pairCnt L k I n t.2 * (∑ m ∈ I, leafCnt m n t.1 * partnerCnt L k I n m t.2) =
            ∑ m ∈ I, leafCnt m n t.1 * (pairCnt L k I n t.2 * partnerCnt L k I n m t.2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        rw [← h1, ← h2]
        ring
      simp_rw [hpt]
      rw [lintegral_hardTree_add, lintegral_hardTree_add, lintegral_hardTree_add,
        lintegral_hardTree_add, lintegral_hardTree_add,
        lintegral_hardTree_const_mul, lintegral_hardTree_const_mul,
        lintegral_hardTree_const_mul, lintegral_hardTree_const_mul,
        lintegral_hardTree_fst ν (fun x => pairCnt L k I n x ^ 2),
        lintegral_hardTree_snd ν (fun x => pairCnt L k I n x ^ 2),
        lintegral_hardTree_mul ν (pairCnt L k I n) (pairCnt L k I n),
        lintegral_hardTree_sum_mul ν I (fun m x => pairCnt L k I n x * leafCnt m n x)
          (fun m => partnerCnt L k I n m),
        lintegral_hardTree_sum_mul ν I (fun m => leafCnt m n)
          (fun m x => pairCnt L k I n x * partnerCnt L k I n m x),
        lintegral_pairCnt]
      simp only [lintegral_partnerCnt, lintegral_leafCnt]
      have ih := lintegral_pairCnt_sq_le n
      have hA : ∑ m ∈ I,
          (∫⁻ x, pairCnt L k I n x * leafCnt m n x ∂(hardTreeMeasure ν n)) *
          partnerW ν L k I n m ≤
          pairMean ν L k I n * pairCross ν L k I n +
            2 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerAcc ν L k I n m * partnerW ν L k I n m := by
        calc _ ≤ ∑ m ∈ I, (2 ^ n * ν {m} * pairMean ν L k I n +
              2 * (2 ^ n * ν {m} * partnerAcc ν L k I n m)) * partnerW ν L k I n m := by
              gcongr with m hm
              exact lintegral_pairCnt_mul_leafCnt_le ν L k I m hm n
          _ = _ := by
              rw [pairCross, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun m _ => by ring
      have hB : ∑ m ∈ I, 2 ^ n * ν {m} *
          ∫⁻ x, pairCnt L k I n x * partnerCnt L k I n m x ∂(hardTreeMeasure ν n) ≤
          pairMean ν L k I n * pairCross ν L k I n +
            2 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerAcc ν L k I n m * partnerW ν L k I n m := by
        have hs := sum_pairInd_swap ν L k I n
          (fun ℓ => 2 ^ n * ν {ℓ} * partnerAcc ν L k I n ℓ)
        calc _ ≤ ∑ m ∈ I, 2 ^ n * ν {m} * (partnerW ν L k I n m * pairMean ν L k I n +
              2 * ∑ ℓ ∈ I, pairInd L k n m ℓ *
                (2 ^ n * ν {ℓ} * partnerAcc ν L k I n ℓ)) := by
              gcongr with m _
              exact lintegral_pairCnt_mul_partnerCnt_le ν L k I n m
          _ = pairMean ν L k I n * pairCross ν L k I n + 2 * ∑ m ∈ I, 2 ^ n * ν {m} *
              ∑ ℓ ∈ I, pairInd L k n m ℓ *
                (2 ^ n * ν {ℓ} * partnerAcc ν L k I n ℓ) := by
              rw [pairCross, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ = _ := by rw [hs]
      have hC := lintegral_cross_sq_le ν L k I n
      calc _ ≤ (2 * pairMean ν L k I n + pairMean ν L k I n ^ 2 + 4 * pairShare ν L k I n) +
            (2 * pairMean ν L k I n + pairMean ν L k I n ^ 2 + 4 * pairShare ν L k I n) +
            2 * (pairMean ν L k I n * pairMean ν L k I n) +
            4 * (pairMean ν L k I n * pairCross ν L k I n +
              2 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerAcc ν L k I n m * partnerW ν L k I n m) +
            4 * (pairMean ν L k I n * pairCross ν L k I n +
              2 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerAcc ν L k I n m * partnerW ν L k I n m) +
            4 * (pairCross ν L k I n +
              2 * ∑ m ∈ I, 2 ^ n * ν {m} * partnerW ν L k I n m ^ 2 +
              pairCross ν L k I n ^ 2) := by
            gcongr
        _ = _ := by
            rw [pairMean_succ, pairShare_succ]
            ring

end FirstMoments

/-! ### The weights at height `L` -/

/-- Closed form:
`2^k γ_n(m) = ∑_{ℓ ∈ I, L + k ≤ m + ℓ < n + L + k} 2^{m + ℓ - L} p_ℓ`. -/
theorem two_pow_mul_partnerAcc (ν : Measure ℕ) (L k : ℕ) (I : Finset ℕ) (m : ℕ) :
    ∀ n : ℕ, 2 ^ k * partnerAcc ν L k I n m =
      ∑ ℓ ∈ I, if L + k ≤ m + ℓ ∧ m + ℓ < n + L + k then
        2 ^ (m + ℓ - L) * ν {ℓ} else 0
  | 0 => by
      rw [show partnerAcc ν L k I 0 m = 0 from rfl, mul_zero]
      symm
      exact Finset.sum_eq_zero fun ℓ _ => ite_eq_right (by omega)
  | n + 1 => by
      rw [partnerAcc_succ, mul_add, two_pow_mul_partnerAcc ν L k I m n, partnerW, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      unfold pairInd
      by_cases h1 : m + ℓ = n + L + k
      · have he : m + ℓ - L = k + n := by omega
        rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left (by omega), he, pow_add]
        ring
      · rw [ite_eq_right h1]
        by_cases h2 : L + k ≤ m + ℓ ∧ m + ℓ < n + L + k
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
          ring
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
          ring

/-- Membership in the upper band `{⌈3L/4⌉, …, L}`. -/
theorem le_of_mem_upperBand {L m : ℕ} (hm : m ∈ upperBand L) : 3 * L ≤ 4 * m ∧ m ≤ L := by
  rw [upperBand, Finset.mem_Icc] at hm
  refine ⟨?_, hm.2⟩
  have h := Nat.ceil_le.mp hm.1
  have h' : (3 * L : ℝ) ≤ 4 * m := by linarith
  exact_mod_cast h'

/-- The partner bound: `2^k γ_n(m) ≤ M_I` for `m ≤ L` (the source's `g(m) ≤ 2^{-k} M_I`). -/
theorem two_pow_mul_partnerAcc_le (ν : Measure ℕ) {L k : ℕ} (I : Finset ℕ) {m : ℕ}
    (hmL : m ≤ L) (n : ℕ) :
    2 ^ k * partnerAcc ν L k I n m ≤ ∑ r ∈ I, 2 ^ r * ν {r} := by
  rw [two_pow_mul_partnerAcc]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  split_ifs with h
  · gcongr
    · norm_num
    · omega
  · exact zero_le

/-- The weighted contribution `2^k S_L` of pairs sharing a leaf is at most
`M_I F_L` (the source's partner bound). -/
theorem two_pow_mul_pairShare_le (ν : Measure ℕ) {L k : ℕ} {I : Finset ℕ}
    (hIL : ∀ m ∈ I, m ≤ L) (n : ℕ) :
    2 ^ k * pairShare ν L k I n ≤ (∑ r ∈ I, 2 ^ r * ν {r}) * pairMean ν L k I n := by
  rw [pairShare, pairMean, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  calc 2 ^ k * (2 ^ n * ν {m} * partnerAcc ν L k I n m ^ 2) =
        (2 ^ k * partnerAcc ν L k I n m) * (2 ^ n * ν {m} * partnerAcc ν L k I n m) := by ring
    _ ≤ (∑ r ∈ I, 2 ^ r * ν {r}) * (2 ^ n * ν {m} * partnerAcc ν L k I n m) := by
        gcongr
        exact two_pow_mul_partnerAcc_le ν I (hIL m hm) n

/-- At height `L` every pair of band values meets at a height in `[1, L]`, so
`2^k F_L = M_I²` (the source's `E Z = 2^{-k-1} M_I²` for unordered pairs). -/
theorem two_pow_mul_pairMean_top (ν : Measure ℕ) {L : ℕ} {I : Finset ℕ}
    (hI : I ⊆ upperBand L) {k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L / 2) :
    2 ^ k * pairMean ν L k I L = (∑ r ∈ I, 2 ^ r * ν {r}) ^ 2 := by
  rw [pairMean, Finset.mul_sum, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show 2 ^ k * (2 ^ L * ν {m} * partnerAcc ν L k I L m) =
      2 ^ L * ν {m} * (2 ^ k * partnerAcc ν L k I L m) by ring,
    two_pow_mul_partnerAcc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have h1 := le_of_mem_upperBand (hI hm)
  have h2 := le_of_mem_upperBand (hI hℓ)
  rw [ite_eq_left (by omega)]
  have he : (2 : ℝ≥0∞) ^ L * 2 ^ (m + ℓ - L) = 2 ^ m * 2 ^ ℓ := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc 2 ^ L * ν {m} * (2 ^ (m + ℓ - L) * ν {ℓ}) =
        (2 ^ L * 2 ^ (m + ℓ - L)) * (ν {m} * ν {ℓ}) := by ring
    _ = _ := by rw [he]; ring

/-! ### Paley–Zygmund and the conclusion -/

theorem two_mul_le_sq_add_ite (c z : ℝ≥0∞) (hc : c ≠ ∞) :
    2 * c * z ≤ z ^ 2 + c ^ 2 * (if z = 0 then 0 else 1) := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, mul_one]
    by_cases hzt : z = ∞
    · simp [hzt]
    · lift c to NNReal using hc
      lift z to NNReal using hzt
      have h := two_mul_le_add_sq c z
      have h' : ((2 * c * z : NNReal) : ℝ≥0∞) ≤
          ((z ^ 2 + c ^ 2 : NNReal) : ℝ≥0∞) := by
        exact_mod_cast h.trans_eq (add_comm _ _)
      push_cast at h'
      exact h'

/-- The Paley–Zygmund inequality in the form `2 c E Z ≤ E Z² + c² P(Z ≠ 0)`. -/
theorem paleyZygmund_hardTree (ν : Measure ℕ) {n : ℕ}
    (Z : HardTree n → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : c ≠ ∞) :
    2 * c * ∫⁻ t, Z t ∂(hardTreeMeasure ν n) ≤
      ∫⁻ t, Z t ^ 2 ∂(hardTreeMeasure ν n) +
        c ^ 2 * hardTreeMeasure ν n {t | Z t ≠ 0} := by
  have hind : ∫⁻ t, (if Z t = 0 then (0 : ℝ≥0∞) else 1) ∂(hardTreeMeasure ν n) =
      hardTreeMeasure ν n {t | Z t ≠ 0} := by
    rw [← lintegral_indicator_one (Set.to_countable _).measurableSet]
    congr 1
    funext t
    by_cases h : Z t = 0 <;> simp [h]
  rw [← hind, ← lintegral_hardTree_const_mul, ← lintegral_hardTree_const_mul,
    ← lintegral_hardTree_add]
  exact lintegral_mono fun t => two_mul_le_sq_add_ite c (Z t) hc

/-- Nonvanishing of the pair count embeds in the event that the height-`L`
hard value is at least `k`. -/
theorem pairCnt_measure_le (ν : Measure ℕ) [IsProbabilityMeasure ν] {L k : ℕ} {I : Finset ℕ}
    (hIL : ∀ ℓ ∈ I, ℓ ≤ L) :
    hardTreeMeasure ν L {t | pairCnt L k I L t ≠ 0} ≤ hardLaw ν L {y | k ≤ y} := by
  rw [← map_hardTreeEval ν L,
    Measure.map_apply (measurable_hardTree _) (Set.to_countable _).measurableSet]
  refine measure_mono fun t ht => ?_
  have := le_eval_of_pairCnt hIL L t ht
  change k ≤ hardTreeEval L t
  omega

/-- The final real inequality: from `x F = M²`, `x S ≤ M F`, `G ≤ 2F + F² + 4S` and
`2 c F ≤ G + c² P` for every `c ≥ 0`, with `x ≥ 2`, deduce
`x⁻¹ · 2 (M/(M+2))² ≤ P`. -/
theorem pairs_final_arith {x M f s g p : ℝ} (hx : 2 ≤ x) (hM : 0 ≤ M)
    (hf : x * f = M ^ 2) (hs : x * s ≤ M * f) (hg : g ≤ 2 * f + f ^ 2 + 4 * s)
    (hpz : ∀ c : ℝ, 0 ≤ c → 2 * c * f ≤ g + c ^ 2 * p) :
    x⁻¹ * 2 * (M / (M + 2)) ^ 2 ≤ p := by
  have hx0 : 0 < x := by linarith
  have hfe : f = M ^ 2 / x := by
    rw [eq_div_iff hx0.ne']
    linarith
  have hf0 : 0 ≤ f := by
    rw [hfe]
    positivity
  set c := 2 + f + 4 * M / x with hc
  have hc0 : 0 < c := by positivity
  have hgc : g ≤ c * f := by
    have h4 : 4 * s ≤ 4 * M * f / x := by
      rw [le_div_iff₀ hx0]
      nlinarith [hs]
    calc g ≤ 2 * f + f ^ 2 + 4 * s := hg
      _ ≤ 2 * f + f ^ 2 + 4 * M * f / x := by linarith
      _ = c * f := by rw [hc]; ring
  have hcf : f ≤ c * p := by
    have h1 := hpz c hc0.le
    have h2 : c * f ≤ c * (c * p) := by nlinarith
    exact le_of_mul_le_mul_left h2 hc0
  have hfc : f / c ≤ p := by
    rw [div_le_iff₀ hc0, mul_comm]
    exact hcf
  refine le_trans ?_ hfc
  have hT : x⁻¹ * 2 * (M / (M + 2)) ^ 2 = 2 * M ^ 2 / (x * (M + 2) ^ 2) := by
    rw [div_pow]
    field_simp
  have hfc' : f / c = M ^ 2 / (2 * x + M ^ 2 + 4 * M) := by
    rw [hc, hfe]
    field_simp
  rw [hT, hfc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg M) (sub_nonneg.2 hx))
    (by positivity : (0 : ℝ) ≤ M ^ 2 + 4 * M)]

/-- The pair tail bound: for `M_I = E[2^{Y_0} 1{Y_0 ∈ I}]`, the probability
that the height-`L` hard value is at least `k` is at least
`2⁻ᵏ · 2 (M_I / (M_I + 2))²`. This proves `DiamondPinning.escape_pairs` (in
`DiamondPinning.Statements.Escape`), covering
`escape:pair-tail` in `source/escape.tex`, lines 52–61. -/
theorem escape_pairs_aux (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ} (hL : 2 ≤ L)
    {I : Finset ℕ} (hI : I ⊆ upperBand L) {k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L / 2) :
    ((2 : ℝ) ^ k)⁻¹ * 2 * (bandMoment ν I / (bandMoment ν I + 2)) ^ 2 ≤
      (hardLaw ν L).real {y | k ≤ y} := by
  -- Since `1 ≤ k ≤ L / 2`, the other hypotheses already imply `2 ≤ L`.
  have _ := hL
  have hIL : ∀ ℓ ∈ I, ℓ ≤ L := fun ℓ hℓ => (le_of_mem_upperBand (hI hℓ)).2
  have hterm : ∀ r : ℕ, (2 : ℝ≥0∞) ^ r * ν {r} ≠ ∞ := fun r =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (measure_ne_top ν _)
  have hM'fin : (∑ r ∈ I, (2 : ℝ≥0∞) ^ r * ν {r}) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun r _ => hterm r
  have hF := two_pow_mul_pairMean_top ν hI hk hkL
  have hS := two_pow_mul_pairShare_le ν (k := k) hIL L
  have hG := lintegral_pairCnt_sq_le ν L k I L
  have hPZ : ∀ c : ℝ≥0∞, c ≠ ∞ → 2 * c * pairMean ν L k I L ≤
      ∫⁻ t, pairCnt L k I L t ^ 2 ∂(hardTreeMeasure ν L) +
        c ^ 2 * hardTreeMeasure ν L {t | pairCnt L k I L t ≠ 0} := by
    intro c hc
    have h := paleyZygmund_hardTree ν (pairCnt L k I L) c hc
    rwa [lintegral_pairCnt] at h
  have hP := pairCnt_measure_le ν (k := k) hIL
  have h2k : (2 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hFfin : pairMean ν L k I L ≠ ∞ := by
    intro hF'
    rw [hF', ENNReal.mul_top h2k] at hF
    exact ENNReal.pow_ne_top hM'fin hF.symm
  have hSfin : pairShare ν L k I L ≠ ∞ := by
    intro hS'
    rw [hS', ENNReal.mul_top h2k, top_le_iff] at hS
    exact ENNReal.mul_ne_top hM'fin hFfin hS
  have hRfin :
      2 * pairMean ν L k I L + pairMean ν L k I L ^ 2 + 4 * pairShare ν L k I L ≠ ∞ := by
    finiteness
  have hGfin := ne_top_of_le_ne_top hRfin hG
  have hPfin : hardTreeMeasure ν L {t | pairCnt L k I L t ≠ 0} ≠ ∞ := measure_ne_top _ _
  have hx : ((2 : ℝ≥0∞) ^ k).toReal = (2 : ℝ) ^ k := by simp
  have hMband : bandMoment ν I = (∑ r ∈ I, (2 : ℝ≥0∞) ^ r * ν {r}).toReal := by
    rw [bandMoment, ENNReal.toReal_sum fun r _ => hterm r]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, measureReal_def]
    simp
  rw [hMband]
  refine le_trans (pairs_final_arith (x := (2 : ℝ) ^ k)
    (M := (∑ r ∈ I, (2 : ℝ≥0∞) ^ r * ν {r}).toReal)
    (f := (pairMean ν L k I L).toReal) (s := (pairShare ν L k I L).toReal)
    (g := (∫⁻ t, pairCnt L k I L t ^ 2 ∂(hardTreeMeasure ν L)).toReal)
    (p := (hardTreeMeasure ν L {t | pairCnt L k I L t ≠ 0}).toReal) ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  · exact ENNReal.toReal_nonneg
  · rw [← hx, ← ENNReal.toReal_mul, hF, ENNReal.toReal_pow]
  · rw [← hx, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hM'fin hFfin) hS
  · have h := ENNReal.toReal_mono hRfin hG
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow] at h
    simpa using h
  · intro c hc
    have h := ENNReal.toReal_mono (by finiteness) (hPZ (ENNReal.ofReal c) ENNReal.ofReal_ne_top)
    rw [ENNReal.toReal_add hGfin (by finiteness)] at h
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc] using h
  · have := hardLaw_isProbability ν L
    rw [measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hP

end DiamondPinning
