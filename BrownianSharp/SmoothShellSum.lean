import BrownianSharp.SmoothGaussian
import BrownianSharp.GenericShellSum

/-! Exact common-prefix shell summation for the actual smooth Gaussian row
correlations, reusing the generic finite-grid kernel machinery. -/

open scoped BigOperators

namespace BrownianSharp

def smoothGoodRowPredicate {d n : ℕ} (q : MidpointGridIndex d n) : Prop :=
  smoothVarianceMeanLowerBound d n / 2 ≤ smoothLayerVariance q

noncomputable def smoothGoodPairKernelGrid {d n : ℕ} (p : ℕ)
    (x : MidpointPairGrid d n) : ℝ :=
  genericGoodPairKernelGrid p (smoothGoodRowPredicate (d := d) (n := n))
    smoothRowCorrelation x

theorem smoothRowCorrelation_nonneg {d n : ℕ} (q q' : MidpointGridIndex d n)
    (hq : 0 < smoothLayerVariance q) (hq' : 0 < smoothLayerVariance q') :
    0 ≤ smoothRowCorrelation q q' := by
  unfold smoothRowCorrelation
  exact div_nonneg (smoothRowCovarianceNumerator_nonneg q q') (by positivity)

theorem smoothGoodRowCorrelation_abs_le_overlapCap {d n h : ℕ}
    (hd : 0 < d) (q q' : MidpointGridIndex d n)
    (hq : smoothGoodRowPredicate q) (hq' : smoothGoodRowPredicate q')
    (hgrade : midpointCommonPrefixGrade (fun i => (q i, q' i)) = n + h) :
    |smoothRowCorrelation q q'| ≤ shapeOverlapCap d n h (2 ^ (d + 1)) := by
  let c := midpointCommonPrefixCaps q q'
  have hc : c.sum (fun _ x => x) = n + h := by
    simpa [c, midpointCommonPrefixGrade] using hgrade
  have hp : MidpointCommonPrefixProfile q q' c := by
    simpa [c] using midpointCommonPrefixCaps_profile q q'
  have hcorr := smoothRowCorrelation_le_prefix hd q q' c hc hp hq hq'
  have hcap :
      2 ^ (d + 1) *
        (Nat.min (Nat.choose (n + d - 1) (d - 1))
          (Nat.choose (h + d - 1) (d - 1)) : ℝ) /
            (Nat.choose (n + d - 1) (d - 1) : ℝ) =
        shapeOverlapCap d n h (2 ^ (d + 1)) := by
    simp [shapeOverlapCap, hyperbolicCount, div_eq_mul_inv, mul_comm, mul_left_comm]
  have hcorr' : smoothRowCorrelation q q' ≤
      shapeOverlapCap d n h (2 ^ (d + 1)) := by
    rw [← hcap]
    exact hcorr
  have hvq : 0 < smoothLayerVariance q :=
    (half_pos (smoothVarianceMeanLowerBound_pos hd)).trans_le hq
  have hvq' : 0 < smoothLayerVariance q' :=
    (half_pos (smoothVarianceMeanLowerBound_pos hd)).trans_le hq'
  have hnonneg := smoothRowCorrelation_nonneg q q' hvq hvq'
  have hcapnonneg : 0 ≤ shapeOverlapCap d n h (2 ^ (d + 1)) :=
    shapeOverlapCap_nonneg (by omega) n h (by positivity)
  rw [abs_of_nonneg hnonneg]
  exact hcorr'

theorem smoothGoodPairKernelGrid_shell_sum_mul_pow_le {d n h p : ℕ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) {κ : ℝ}
    (hκ : κ ≤ Real.log 2 /
      (4 * (2 ^ (d + 1) : ℝ) * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1)) :
    (∑ x : midpointPairShell (d := d) (n := n) (n + h),
      smoothGoodPairKernelGrid p x.1) * (2 ^ (n + h) : ℝ) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          (4 * (p : ℝ) ^ 2 *
            ((2 ^ (d + 1) : ℝ) * (Nat.factorial (d - 1) : ℝ) *
              (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1)) ^ 2 *
            Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) := by
  apply genericGoodPairKernelGrid_shell_sum_mul_pow_le hd hD hn
    (L := 2 ^ (d + 1)) (hL := by positivity) hκ hp
    (smoothGoodRowPredicate (d := d) (n := n)) smoothRowCorrelation
  intro q q' hq hq' hgrade
  exact smoothGoodRowCorrelation_abs_le_overlapCap hd q q' hq hq' hgrade

theorem smoothRowCorrelation_eq_zero_of_prefix_grade_lt {d n : ℕ}
    (hd : 0 < d)
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hp : MidpointCommonPrefixProfile q q' c)
    (hc : c.sum (fun _ x => x) < n)
    (hq : smoothGoodRowPredicate q) (hq' : smoothGoodRowPredicate q') :
    smoothRowCorrelation q q' = 0 := by
  have hnum : (∑ a : LayerIndex d n,
      smoothLayerAtom smoothAtom q a * smoothLayerAtom smoothAtom q' a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact smoothLayerPair_zero_of_prefix_lt (h := n) smoothAtom
      (fun x hx => smoothAtom_support x hx) q q' c hc hp a
  unfold smoothRowCorrelation
  have hvq : 0 < smoothLayerVariance q :=
    (half_pos (smoothVarianceMeanLowerBound_pos hd)).trans_le hq
  have hvq' : 0 < smoothLayerVariance q' :=
    (half_pos (smoothVarianceMeanLowerBound_pos hd)).trans_le hq'
  rw [hnum]
  simp

theorem smoothGoodPairKernelGrid_shell_eq_zero_of_grade_lt {d n u p : ℕ}
    (hd : 0 < d)
    (x : midpointPairShell (d := d) (n := n) u) (hu : u < n) :
    smoothGoodPairKernelGrid p x.1 = 0 := by
  apply genericGoodPairKernelGrid_shell_eq_zero_of_grade_lt
    (smoothGoodRowPredicate (d := d) (n := n)) smoothRowCorrelation
  · intro q q' hq hq' hlt
    let c := midpointCommonPrefixCaps q q'
    have hc : c.sum (fun _ z => z) < n := by
      simpa [c, midpointCommonPrefixGrade] using hlt
    have hp : MidpointCommonPrefixProfile q q' c := by
      simpa [c] using midpointCommonPrefixCaps_profile q q'
    exact smoothRowCorrelation_eq_zero_of_prefix_grade_lt hd q q' c hp hc hq hq'
  · exact hu

end BrownianSharp
