import BrownianSharp.AlignmentFractionalApproximationNumbers
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Basic.ENNReal.Inv

/-! Ideal inequalities for the manuscript's strict-rank approximation numbers. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentApproximationNumberIdeal
open AlignmentFractionalApproximationNumbers
universe u
variable {X Y Z : Type u}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem zero_rank_lt (X Y : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {k : ℕ} (hk : 0 < k) :
    Module.rank ℝ (LinearMap.range (0 : X →ₗ[ℝ] Y)) < (k : Cardinal) := by
  simpa using (show (0 : Cardinal.{u}) < (k : Cardinal.{u}) by exact_mod_cast hk)

theorem approximationNumber_comp_le_left
    (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y) {k : ℕ} (hk : 0 < k) :
    approximationNumber (S.comp T) k ≤
      ENNReal.ofReal ‖S‖ * approximationNumber T k := by
  classical
  letI : Nonempty {A : X →L[ℝ] Y //
      Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (k : Cardinal)} :=
    ⟨⟨0, by simpa using zero_rank_lt X Y hk⟩⟩
  unfold approximationNumber
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro A
  have hr : Module.rank ℝ (LinearMap.range (S.comp A.val : X →ₗ[ℝ] Z)) <
      (k : Cardinal) :=
    (LinearMap.rank_comp_le_right (A.val : X →ₗ[ℝ] Y) S.toLinearMap).trans_lt A.property
  refine (iInf_le _ ⟨S.comp A.val,hr⟩).trans ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg S)]
  apply ENNReal.ofReal_le_ofReal
  have heq : S.comp T - S.comp A.val = S.comp (T-A.val) := by
    ext x
    simp
  rw [heq]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem approximationNumber_comp_le_right
    (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y) {k : ℕ} (hk : 0 < k) :
    approximationNumber (S.comp T) k ≤
      approximationNumber S k * ENNReal.ofReal ‖T‖ := by
  classical
  letI : Nonempty {A : Y →L[ℝ] Z //
      Module.rank ℝ (LinearMap.range (A : Y →ₗ[ℝ] Z)) < (k : Cardinal)} :=
    ⟨⟨0, by simpa using zero_rank_lt Y Z hk⟩⟩
  unfold approximationNumber
  rw [ENNReal.iInf_mul (by simp)]
  apply le_iInf
  intro A
  have hr : Module.rank ℝ (LinearMap.range (A.val.comp T : X →ₗ[ℝ] Z)) <
      (k : Cardinal) :=
    (LinearMap.rank_comp_le_left T.toLinearMap (A.val : Y →ₗ[ℝ] Z)).trans_lt A.property
  refine (iInf_le _ ⟨A.val.comp T,hr⟩).trans ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have heq : S.comp T - A.val.comp T = (S-A.val).comp T := by
    ext x
    simp
  rw [heq]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end BrownianSharp.AlignmentApproximationNumberIdeal
