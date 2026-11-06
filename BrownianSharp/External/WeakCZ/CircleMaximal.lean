import BrownianSharp.AlignmentPaperCircleDoubling
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! Direct weak maximal estimate for the actual circle measure. Only finite
Vitali selection and compact inner regularity are used. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace BrownianSharp.External.WeakCZ
open BrownianSharp.AlignmentPaperCircleDoubling

abbrev circleMaximalMeasure : Measure UnitAddCircle := AddCircle.haarAddCircle

/-- A finite family of high-average balls has a controlled union. -/
theorem finite_circle_highAverage_ball_union_le {ι : Type*}
    (S : Finset ι) (center : ι → UnitAddCircle) (radius : ι → ℝ)
    (R : ℝ) (hR : ∀ i ∈ S, radius i ≤ R)
    (f : UnitAddCircle → ℂ) {level : ℝ} (hlevel : 0 < level)
    (hhigh : ∀ i ∈ S, ENNReal.ofReal level *
      circleMaximalMeasure (ball (center i) (radius i)) ≤
        ∫⁻ x in ball (center i) (radius i), ‖f x‖ₑ ∂circleMaximalMeasure) :
    circleMaximalMeasure (⋃ i ∈ S, ball (center i) (radius i)) ≤
      (5:ENNReal) * (ENNReal.ofReal level)⁻¹ *
        ∫⁻ x, ‖f x‖ₑ ∂circleMaximalMeasure := by
  classical
  obtain ⟨U,hUS,hdisj,hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (t := (S : Set ι)) center radius R hR 5 (by norm_num)
  have hUf : U.Finite := S.finite_toSet.subset hUS
  let F := hUf.toFinset
  have hFmem (i : ι) : i ∈ F ↔ i ∈ U := by simp [F]
  have hFd : Set.PairwiseDisjoint (F : Set ι)
      (fun i => ball (center i) (radius i)) := by
    simpa only [F, Set.Finite.coe_toFinset] using hdisj
  have hsub : (⋃ i ∈ S, ball (center i) (radius i)) ⊆
      ⋃ i ∈ F, ball (center i) (5*radius i) := by
    intro x hx
    rcases mem_iUnion₂.mp hx with ⟨i,hi,hxi⟩
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact mem_iUnion₂.mpr ⟨j,(hFmem j).mpr hj,hij hxi⟩
  have hlevel0 : ENNReal.ofReal level ≠ 0 := (ENNReal.ofReal_pos.mpr hlevel).ne'
  have hleveltop : ENNReal.ofReal level ≠ ⊤ := ENNReal.ofReal_ne_top
  have hball (i : ι) (hi : i ∈ F) :
      circleMaximalMeasure (ball (center i) (radius i)) ≤
        (ENNReal.ofReal level)⁻¹ *
          ∫⁻ x in ball (center i) (radius i), ‖f x‖ₑ ∂circleMaximalMeasure := by
    calc
      _ = (ENNReal.ofReal level)⁻¹ * (ENNReal.ofReal level *
          circleMaximalMeasure (ball (center i) (radius i))) :=
        (ENNReal.inv_mul_cancel_left hlevel0 hleveltop).symm
      _ ≤ _ := by
        gcongr
        exact hhigh i (hUS ((hFmem i).mp hi))
  have hsum : (∑ i ∈ F,
      ∫⁻ x in ball (center i) (radius i), ‖f x‖ₑ ∂circleMaximalMeasure) ≤
        ∫⁻ x, ‖f x‖ₑ ∂circleMaximalMeasure := by
    rw [← lintegral_biUnion_finset hFd (fun _ _ => measurableSet_ball)]
    exact setLIntegral_le_lintegral _ _
  calc
    _ ≤ circleMaximalMeasure (⋃ i ∈ F, ball (center i) (5*radius i)) := measure_mono hsub
    _ ≤ ∑ i ∈ F, circleMaximalMeasure (ball (center i) (5*radius i)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ F, (5:ENNReal) * circleMaximalMeasure (ball (center i) (radius i)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [circleMaximalMeasure, ENNReal.ofReal_ofNat] using
        haar_ball_scale_le (center i) (radius i) 5 (by norm_num)
    _ ≤ ∑ i ∈ F, (5:ENNReal) * ((ENNReal.ofReal level)⁻¹ *
        ∫⁻ x in ball (center i) (radius i), ‖f x‖ₑ ∂circleMaximalMeasure) :=
      Finset.sum_le_sum (fun i hi => by
        gcongr
        exact hball i hi)
    _ = ((5:ENNReal)*(ENNReal.ofReal level)⁻¹) *
        (∑ i ∈ F, ∫⁻ x in ball (center i) (radius i), ‖f x‖ₑ ∂circleMaximalMeasure) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (mul_assoc _ _ _).symm
    _ ≤ _ := by
      gcongr

/-- All positive-radius balls with mean norm strictly above the level. -/
def CircleHighBall (f : UnitAddCircle → ℂ) (level : ℝ) :=
  {b : UnitAddCircle × ℝ // 0 < b.2 ∧
    ENNReal.ofReal level * circleMaximalMeasure (ball b.1 b.2) <
      ∫⁻ x in ball b.1 b.2, ‖f x‖ₑ ∂circleMaximalMeasure}

/-- The uncentered bad set, with the union taken over the actual high balls. -/
def circleHighAverageSet (f : UnitAddCircle → ℂ) (level : ℝ) : Set UnitAddCircle :=
  ⋃ b : CircleHighBall f level, ball b.val.1 b.val.2

theorem isOpen_circleHighAverageSet (f : UnitAddCircle → ℂ) (level : ℝ) :
    IsOpen (circleHighAverageSet f level) :=
  isOpen_iUnion (fun _ => isOpen_ball)

theorem circleHighAverageSet_measure_le (f : UnitAddCircle → ℂ)
    {level : ℝ} (hlevel : 0 < level) :
    circleMaximalMeasure (circleHighAverageSet f level) ≤
      (5:ENNReal) * (ENNReal.ofReal level)⁻¹ *
        ∫⁻ x, ‖f x‖ₑ ∂circleMaximalMeasure := by
  classical
  rw [(isOpen_circleHighAverageSet f level).measure_eq_iSup_isCompact circleMaximalMeasure]
  refine iSup_le fun K => iSup_le fun hKsub => iSup_le fun hK => ?_
  obtain ⟨S,hScover⟩ := hK.elim_finite_subcover
    (fun b : CircleHighBall f level => ball b.val.1 b.val.2)
    (fun _ => isOpen_ball) hKsub
  have hbounded : BddAbove
      ((fun b : CircleHighBall f level => b.val.2) '' (S : Set (CircleHighBall f level))) :=
    (S.finite_toSet.image (fun b : CircleHighBall f level => b.val.2)).bddAbove
  obtain ⟨R,hR⟩ := hbounded
  have hfamily := finite_circle_highAverage_ball_union_le S
    (fun b => b.val.1) (fun b => b.val.2) R
    (fun b hb => hR ⟨b,hb,rfl⟩) f hlevel (fun b _ => b.property.2.le)
  exact (measure_mono hScover).trans hfamily

/-- Outside the bad set, every ball containing the point has controlled norm
integral. No measurability or covariance hypothesis is hidden in this step. -/
theorem circle_ball_integral_le_of_notMem_highAverageSet
    (f : UnitAddCircle → ℂ) (level : ℝ) {x center : UnitAddCircle}
    (hx : x ∉ circleHighAverageSet f level) {r : ℝ} (hr : 0 < r)
    (hball : x ∈ ball center r) :
    (∫⁻ z in ball center r, ‖f z‖ₑ ∂circleMaximalMeasure) ≤
      ENNReal.ofReal level * circleMaximalMeasure (ball center r) := by
  by_contra hnot
  have hhigh := lt_of_not_ge hnot
  let b : CircleHighBall f level := ⟨(center,r),hr,hhigh⟩
  apply hx
  exact mem_iUnion.mpr ⟨b,hball⟩

theorem circleHighAverageSet_ne_univ_of_budget (f : UnitAddCircle → ℂ)
    {level : ℝ} (hlevel : 0 < level)
    (hbudget : (5:ENNReal) * (ENNReal.ofReal level)⁻¹ *
      (∫⁻ x, ‖f x‖ₑ ∂circleMaximalMeasure) < 1) :
    circleHighAverageSet f level ≠ univ := by
  intro heq
  have h := (circleHighAverageSet_measure_le f hlevel).trans_lt hbudget
  rw [heq] at h
  simpa [circleMaximalMeasure] using h

end BrownianSharp.External.WeakCZ
