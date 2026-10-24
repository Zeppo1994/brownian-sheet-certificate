import BrownianSharp.AlignmentFractionalSharpBudgets

/-! The elementary cancellation behind the sharp dyadic KGG error rate. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentFractionalKGGArithmetic

theorem polynomial_geometric_ratio_le {C ρ δ D : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hδ : 0 < δ)
    (k n : ℕ) (hD : δ*(2:ℝ)^n*((n+1:ℕ):ℝ)^k ≤ D) :
    (C*((n+2:ℕ):ℝ)^k*ρ^(n+1))/D ≤
      (C*(2:ℝ)^k*ρ/δ)*(ρ/2)^n := by
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hpoly : ((n+2:ℕ):ℝ)^k ≤ (2:ℝ)^k*((n+1:ℕ):ℝ)^k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith
  have hR : 0 ≤ (C*(2:ℝ)^k*ρ/δ)*(ρ/2)^n := by positivity
  apply (div_le_iff₀ hDpos).2
  calc
    _ ≤ C*((2:ℝ)^k*((n+1:ℕ):ℝ)^k)*ρ^(n+1) := by gcongr
    _ = ((C*(2:ℝ)^k*ρ/δ)*(ρ/2)^n) *
        (δ*(2:ℝ)^n*((n+1:ℕ):ℝ)^k) := by
      rw [pow_succ,div_pow]
      field_simp
      <;> ring
    _ ≤ ((C*(2:ℝ)^k*ρ/δ)*(ρ/2)^n)*D :=
      mul_le_mul_of_nonneg_left hD hR

theorem dyadic_target_sq (r : ℝ) (n : ℕ) :
    ((2:ℝ)^(-r*n)*Real.sqrt ((n+1:ℕ):ℝ))^2 =
      (((2:ℝ)^(-(2*r-1)))/2)^n*((n+1:ℕ):ℝ) := by
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hp : ((2:ℝ)^(-r*n))^2 = (2:ℝ)^(-(2*r)*n) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  rw [hp,AlignmentFractionalSharpBudgets.dyadic_decay_eq_pow]
  have hbase : (2:ℝ)^(-(2*r)) = (2:ℝ)^(-(2*r-1))/2 := by
    rw [show -(2*r-1)=-(2*r)+1 by ring,
      Real.rpow_add (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [hbase]

theorem sharp_KGG_sqrt_bound {C B L δ D J r : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hJ0 : 0 ≤ J) (k n : ℕ)
    (hD : δ*(2:ℝ)^n*((n+1:ℕ):ℝ)^k ≤ D)
    (hJ : J ≤ L*((n+1:ℕ):ℝ)) :
    Real.sqrt ((C*((n+2:ℕ):ℝ)^k*
      ((2:ℝ)^(-(2*r-1)))^(n+1)*J/D)*B) ≤
      Real.sqrt (C*(2:ℝ)^k*((2:ℝ)^(-(2*r-1)))*L*B/δ) *
        ((2:ℝ)^(-r*n)*Real.sqrt ((n+1:ℕ):ℝ)) := by
  let ρ := (2:ℝ)^(-(2*r-1))
  let V := C*(2:ℝ)^k*ρ*L*B/δ
  let target := (2:ℝ)^(-r*n)*Real.sqrt ((n+1:ℕ):ℝ)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ht : 0 ≤ target := by dsimp [target]; positivity
  have hratio := polynomial_geometric_ratio_le hC hρ hδ k n hD
  have hR : 0 ≤ (C*(2:ℝ)^k*ρ/δ)*(ρ/2)^n := by positivity
  have hs : (C*((n+2:ℕ):ℝ)^k*ρ^(n+1)*J/D)*B ≤ V*target^2 := by
    calc
      _ = ((C*((n+2:ℕ):ℝ)^k*ρ^(n+1))/D)*J*B := by ring
      _ ≤ ((C*(2:ℝ)^k*ρ/δ)*(ρ/2)^n)*(L*((n+1:ℕ):ℝ))*B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact (mul_le_mul_of_nonneg_right hratio hJ0).trans
          (mul_le_mul_of_nonneg_left hJ hR)
      _ = V*target^2 := by
        dsimp [V,target]
        rw [dyadic_target_sq]
        change _ = (C*(2:ℝ)^k*ρ*L*B/δ) * ((ρ/2)^n*((n+1:ℕ):ℝ))
        ring
  calc
    _ ≤ Real.sqrt (V*target^2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt V*target := by
      rw [Real.sqrt_mul hV,Real.sqrt_sq_eq_abs,abs_of_nonneg ht]

end BrownianSharp.AlignmentFractionalKGGArithmetic
