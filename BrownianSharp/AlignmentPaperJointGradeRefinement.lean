import BrownianSharp.AlignmentPaperJointGlobalCover
import BrownianSharp.AlignmentPaperFiniteCoverRefinement

/-! Arbitrary refinement of actual decoded grade covers. The dimension cost
is that of the joint source samples, not that of the enclosing output grid. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperJointGradeRefinement
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperFiniteCoverRefinement

def decodedGradeRange (d n : ℕ) :
    Submodule ℝ C(UnitAddTorus (Fin d), ℂ) :=
  ((commonGridDecoder (d := d) (n := n)).comp
    (featureMap (d := d) (n := n))).toLinearMap.range

instance decodedGradeRange_finiteDimensional (d n : ℕ) :
    FiniteDimensional ℝ (decodedGradeRange d n) :=
  LinearMap.finiteDimensional_range _

theorem decodedGradeRange_finrank_le (d n : ℕ) :
    Module.finrank ℝ (decodedGradeRange d n) ≤ JointSampleDimension d n := by
  let L : EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →ₗ[ℝ]
      C(UnitAddTorus (Fin d), ℂ) :=
    ((commonGridDecoder (d := d) (n := n)).comp
      (featureMap (d := d) (n := n))).toLinearMap
  change Module.finrank ℝ L.range ≤ JointSampleDimension d n
  calc
    _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin (JointSampleDimension d n))) :=
      L.finrank_range_le
    _ = JointSampleDimension d n := finrank_euclideanSpace_fin

theorem decodedGrade_subset_range {d n : ℕ} (p B : ℝ) :
    decodedJointLpFeatureImage (d := d) (n := n) p B ⊆ decodedGradeRange d n := by
  rintro f ⟨z,⟨x,hx,rfl⟩,rfl⟩
  exact ⟨WithLp.toLp 2 x,rfl⟩

/-- A source-dimension refinement bound for every positive target radius.
The original cover centres need not lie in the decoded range. -/
theorem exists_decodedGrade_refined_cover {d n : ℕ} {p B : ℝ}
    {C : Set C(UnitAddTorus (Fin d), ℂ)} {ε : ℝ≥0} {η : ℝ}
    (hC : C.Finite)
    (hcover : Metric.IsCover ε
      (decodedJointLpFeatureImage (d := d) (n := n) p B) C)
    (hη : 0 < η) :
    ∃ D : Set C(UnitAddTorus (Fin d), ℂ), D.Finite ∧
      Metric.IsCover (NNReal.mk η hη.le)
        (decodedJointLpFeatureImage (d := d) (n := n) p B) D ∧
      D.encard ≤ C.encard *
        ↑(Nat.ceil ((1 + 4*(ε : ℝ)/η) ^ JointSampleDimension d n)) := by
  let V := decodedGradeRange d n
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  obtain ⟨D,hD,hcoverD,hcount⟩ := exists_refined_cover_in_subspace V
    (decodedGrade_subset_range p B) hC hcover hη
  refine ⟨D,hD,hcoverD,hcount.trans ?_⟩
  apply mul_le_mul le_rfl ?_ (by positivity) (by positivity)
  have hbase : 1 ≤ 1 + 4*(ε : ℝ)/η := by
    have hnonneg : 0 ≤ 4*(ε : ℝ)/η :=
      div_nonneg (mul_nonneg (by norm_num) ε.coe_nonneg) hη.le
    linarith
  exact_mod_cast Nat.ceil_mono (pow_le_pow_right₀
    hbase (decodedGradeRange_finrank_le d n))

end BrownianSharp.AlignmentPaperJointGradeRefinement
