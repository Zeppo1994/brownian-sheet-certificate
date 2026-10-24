import BrownianSharp.AlignmentFractionalApproximationNumbers
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-! A product inequality for strict-rank approximation numbers. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentApproximationNumberProduct
universe u

theorem approximationNumber_comp_le_of_approximants
    {X Y Z : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y)
    (A : Y →L[ℝ] Z) (B : X →L[ℝ] Y)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hA : Module.rank ℝ (LinearMap.range (A : Y →ₗ[ℝ] Z)) < (m : Cardinal))
    (hB : Module.rank ℝ (LinearMap.range (B : X →ₗ[ℝ] Y)) < (n : Cardinal)) :
    BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
      (S.comp T) (m+n-1) ≤
      ENNReal.ofReal (‖S-A‖ * ‖T-B‖) := by
  classical
  let C : X →L[ℝ] Z := A.comp T + (S-A).comp B
  have hC_rank : Module.rank ℝ (LinearMap.range (C : X →ₗ[ℝ] Z)) <
      ((m+n-1 : ℕ) : Cardinal) := by
    have hadd := LinearMap.rank_add_le
      (A.comp T : X →ₗ[ℝ] Z) ((S-A).comp B : X →ₗ[ℝ] Z)
    have hcompA := LinearMap.rank_comp_le_left
      (T : X →ₗ[ℝ] Y) (A : Y →ₗ[ℝ] Z)
    have hcompB := LinearMap.rank_comp_le_right
      (B : X →ₗ[ℝ] Y) ((S-A) : Y →ₗ[ℝ] Z)
    have hA' : Module.rank ℝ (LinearMap.range (A : Y →ₗ[ℝ] Z)) ≤
        ((m-1 : ℕ) : Cardinal) := by
      have hs : (m-1)+1 = m := Nat.sub_add_cancel hm
      rw [← hs] at hA
      exact Cardinal.lt_natCast_add_one_iff.mp
        (by simpa only [Nat.cast_add, Nat.cast_one] using hA)
    have hB' : Module.rank ℝ (LinearMap.range (B : X →ₗ[ℝ] Y)) ≤
        ((n-1 : ℕ) : Cardinal) := by
      have hs : (n-1)+1 = n := Nat.sub_add_cancel hn
      rw [← hs] at hB
      exact Cardinal.lt_natCast_add_one_iff.mp
        (by simpa only [Nat.cast_add, Nat.cast_one] using hB)
    change Module.rank ℝ (LinearMap.range
      ((A.comp T + (S-A).comp B : X →L[ℝ] Z) : X →ₗ[ℝ] Z)) < _
    calc
      Module.rank ℝ (LinearMap.range
          ((A.comp T : X →ₗ[ℝ] Z) + ((S-A).comp B : X →ₗ[ℝ] Z)))
          ≤ Module.rank ℝ (LinearMap.range (A.comp T : X →ₗ[ℝ] Z)) +
            Module.rank ℝ (LinearMap.range ((S-A).comp B : X →ₗ[ℝ] Z)) := hadd
      _ ≤ Module.rank ℝ (LinearMap.range (A : Y →ₗ[ℝ] Z)) +
            Module.rank ℝ (LinearMap.range (B : X →ₗ[ℝ] Y)) := by
          exact add_le_add hcompA hcompB
      _ ≤ ((m-1 : ℕ) : Cardinal) + ((n-1 : ℕ) : Cardinal) := add_le_add hA' hB'
      _ < ((m+n-1 : ℕ) : Cardinal) := by
          exact_mod_cast (show (m-1)+(n-1) < m+n-1 by omega)
  have herror : S.comp T - C = (S-A).comp (T-B) := by
    ext x
    simp [C, ContinuousLinearMap.comp_apply, sub_apply]
    module
  have hnorm : ‖S.comp T - C‖ ≤ ‖S-A‖ * ‖T-B‖ := by
    rw [herror]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hnonneg : 0 ≤ ‖S-A‖ * ‖T-B‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have happrox :=
    BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber_le_of_approximant
      (S.comp T) C hC_rank
  exact happrox.trans (ENNReal.ofReal_le_ofReal (hnorm))

end BrownianSharp.AlignmentApproximationNumberProduct
