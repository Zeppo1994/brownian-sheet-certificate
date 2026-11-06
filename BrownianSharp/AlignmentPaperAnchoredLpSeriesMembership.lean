import BrownianSharp.AlignmentPaperAnchoredLpGradeReconstruction
import BrownianSharp.AlignmentPaperAnchoredLp
import BrownianSharp.AlignmentPaperAnchoredLpOperator
import BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentPaperJointSamplingBudget
import BrownianSharp.AlignmentPaperJointGlobalSeries
import BrownianSharp.ShapeGrowth

/-! Membership of actual anchored paths in the global grade-series class,
from the actual mixed grade-energy estimate and the fixed-grid sample budget. -/

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpSeriesMembership

open BrownianSharp.AlignmentPaperAnchoredLpGradeReconstruction
open BrownianSharp.AlignmentPaperJointSamplingBudget
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointGlobalSeries
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPeriodicFourierReconstruction
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus

local instance seriesMembershipTorusProbability (d : ℕ) :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  rw [BrownianSharp.unitAddTorus_volume_eq_productHaar]
  infer_instance

/-- An actual per-grade mixed-energy estimate gives membership of the actual
periodicized anchored path in the decoded global grade-series class. The single
radius parameter is chosen from the sampling constant and is independent of
both the grade and the source. -/
theorem integrationPath_mem_GradeSeriesClass_of_grade_cost
    {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (D : ℝ) (hD : 0 < D)
    : ∃ A : ℝ, 0 < A ∧ ∀ (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)),
      (∀ n : ℕ,
        (∑ s : Shape d n,
          (∫ x : UnitAddTorus (Fin d),
            ‖block s.1 (periodicFoldExtension (integrationPath p hp g)) x‖ ^ p
            ∂(volume : Measure (UnitAddTorus (Fin d)))) ^ (2 / p)) ^ (p / 2) ≤
          D * (2 : ℝ) ^ (-(p * (n : ℝ)))) →
      complexifyContinuous (periodicFoldExtension (integrationPath p hp g)) ∈
        GradeSeriesClass d p A := by
  classical
  let A : ℝ := (samplingConstant d p * D) ^ (1 / p)
  have hp0 : 0 < p := by linarith
  have hsampleC : 0 < samplingConstant d p := by
    unfold samplingConstant
    positivity
  have hA : 0 < A := by
    dsimp [A]
    apply Real.rpow_pos_of_pos
    exact mul_pos hsampleC hD
  have hApow : A ^ p = samplingConstant d p * D := by
    dsimp [A]
    rw [← Real.rpow_mul (mul_nonneg hsampleC.le hD.le)]
    have hexp : (1 / p) * p = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  refine ⟨A, hA, ?_⟩
  intro g hgrade
  let f : RealPeriodic d := periodicFoldExtension (integrationPath p hp g)
  have hshapeCard (n : ℕ) :
      (Fintype.card (Shape d n) : ℝ) ≤ (n + 1 : ℝ) ^ (d - 1) := by
    rw [shape_card d n (by omega : 0 < d)]
    simpa [BrownianSharp.hyperbolicCount] using
      hyperbolicCount_upper_shift (by omega : 1 ≤ d) n
  have hshapePow (n : ℕ) :
      (Fintype.card (Shape d n) : ℝ) ^ (1 - p / 2) ≤
        (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 - p / 2)) := by
    have he : 0 < 1 - p / 2 := by linarith
    calc
      _ ≤ ((n + 1 : ℝ) ^ (d - 1)) ^ (1 - p / 2) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (hshapeCard n) (le_of_lt he)
      _ = (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 - p / 2)) := by
        rw [← Real.rpow_natCast (n + 1 : ℝ) (d - 1)]
        rw [← Real.rpow_mul (by positivity : 0 ≤ (n + 1 : ℝ))]
        rw [Nat.cast_sub (by omega : 1 ≤ d)]
        norm_num
  have hradpow (n : ℕ) :
      gradeSeriesSourceRadius d p A n ^ p =
        samplingConstant d p * D *
          (2 : ℝ) ^ (-(p - 1) * (n : ℝ)) *
          (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 - p / 2)) := by
    unfold gradeSeriesSourceRadius
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (n + 1 : ℝ))]
    rw [hApow]
    have hExp : (-(1 - 1 / p) * (n : ℝ)) * p = -(p - 1) * (n : ℝ) := by
      field_simp
    have hPoly : ((d - 1 : ℕ) : ℝ) * (1 / p - 1 / 2) * p =
        (d - 1 : ℝ) * (1 - p / 2) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      field_simp
      <;> ring
    rw [hExp, hPoly]
  have hsample (n : ℕ) :
      (∑ i : Fin (JointSampleDimension d n),
        |gradeSampleCoordinates (d := d) (n := n)
          (encodeSmoothGradeSamples f) i| ^ p) ≤
        (gradeSeriesSourceRadius d p A n) ^ p := by
    have hpq : p.HolderConjugate (p / (p - 1)) := by
      apply Real.holderConjugate_iff.mpr
      constructor
      · linarith
      · field_simp
        <;> linarith
    have hbudget := encodeSmoothGradeSamples_fin_square_budget
      (d := d) (n := n) hpq (le_of_lt hp2) f
    have hcard := hshapePow n
    have hcost := hgrade n
    have hscale :
        (2 : ℝ) ^ (n : ℕ) * (2 : ℝ) ^ (-(p * (n : ℝ))) =
          (2 : ℝ) ^ (-(p - 1) * (n : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      congr 1
      have hExp : (n : ℝ) + (-(p * (n : ℝ))) = -(p - 1) * (n : ℝ) := by ring
      rw [hExp]
    calc
      _ ≤ samplingConstant d p * (2 : ℝ) ^ n *
          (Fintype.card (Shape d n) : ℝ) ^ (1 - p / 2) *
          (∑ s : Shape d n,
            (∫ x : UnitAddTorus (Fin d),
              ‖block s.1 f x‖ ^ p
              ∂(volume : Measure (UnitAddTorus (Fin d)))) ^ (2 / p)) ^ (p / 2) := hbudget
      _ ≤ samplingConstant d p * (2 : ℝ) ^ n *
          (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 - p / 2)) *
          (D * (2 : ℝ) ^ (-(p * (n : ℝ)))) := by
            gcongr
      _ = samplingConstant d p * D *
          ((2 : ℝ) ^ n * (2 : ℝ) ^ (-(p * (n : ℝ)))) *
          (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 - p / 2)) := by ring
      _ = samplingConstant d p * D *
          (2 : ℝ) ^ (-(p - 1) * (n : ℝ)) *
          (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 - p / 2)) := by
            rw [hscale]
      _ = (gradeSeriesSourceRadius d p A n) ^ p := (hradpow n).symm
  have hmem (n : ℕ) :
      smoothGradePolynomial (d := d) (n := n) f ∈
        decodedJointLpFeatureImage (d := d) (n := n) p
          (gradeSeriesSourceRadius d p A n) := by
    apply smoothGrade_mem_decodedJointLpFeatureImage
    simpa [f, gradeSampleCoordinates] using hsample n
  have hsum : Summable (fun n : ℕ => smoothGradePolynomial (d := d) (n := n) f) :=
    gradeSeries_witness_summable hd hp hp2 hA hmem
  have hhas := smoothGradePolynomial_hasSum f hsum
  change ∃ u : ℕ → C(UnitAddTorus (Fin d), ℂ),
    (∀ n, u n ∈ decodedJointLpFeatureImage (d := d) (n := n) p
      (gradeSeriesSourceRadius d p A n)) ∧
      complexifyContinuous f = ∑' n, u n
  refine ⟨fun n => smoothGradePolynomial (d := d) (n := n) f, hmem, ?_⟩
  exact hhas.tsum_eq.symm

end BrownianSharp.AlignmentPaperAnchoredLpSeriesMembership

end
