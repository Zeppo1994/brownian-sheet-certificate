import BrownianSharp.GenericShellSum

open scoped BigOperators

namespace BrownianSharp

/-- Density converts the raw generic full-grid shell estimate to the average
over the actual good rows. The denominator is exactly the square of the
good-row cardinality. -/
theorem genericGoodPairKernel_average_le_of_density {d n p : ℕ} {L κ δ : ℝ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 / (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1)) (hδ : 0 < δ)
    (good : MidpointGridIndex d n → Prop)
    (rho : MidpointGridIndex d n → MidpointGridIndex d n → ℝ)
    (hbelow : ∀ q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) < n → rho q q' = 0)
    (hcap : ∀ h q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) = n + h →
      |rho q q'| ≤ shapeOverlapCap d n h L)
    (hdensity : δ * (Fintype.card (MidpointGridIndex d n) : ℝ) ≤
      (Fintype.card (GenericGoodRows good) : ℝ)) :
    (∑ x : GenericGoodPair good, highPowerPairKernel p (rho x.1.1 x.2.1)) /
        (Fintype.card (GenericGoodPair good) : ℝ) ≤
      (4 * (p : ℝ) ^ 2 * (L * (Nat.factorial (d - 1) : ℝ)) ^ 2 *
        Real.sqrt 2 * shellPolynomialBudget (d - 1)) /
        (δ ^ 2 * (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1)) := by
  classical
  letI := genericGoodRowsFintype good
  have hraw := genericGoodPairKernelGrid_sum_le_budget
    (d := d) (n := n) (p := p) hd hD hn hL hκ hp good rho hbelow hcap
  rw [← genericGoodPairKernel_sum_eq_grid good rho] at hraw
  have hcardpair :
      (Fintype.card (GenericGoodPair good) : ℝ) =
        (Fintype.card (GenericGoodRows good) : ℝ) ^ 2 := by
    simp [GenericGoodPair, Fintype.card_prod]
    ring
  let R : ℝ := Fintype.card (MidpointGridIndex d n)
  let G : ℝ := Fintype.card (GenericGoodRows good)
  have hR : 0 < R := by
    dsimp [R, MidpointGridIndex, MidpointGridCoordinate]
    simp [Fintype.card_pi]
  have hG : 0 < G := lt_of_lt_of_le (mul_pos hδ hR) (by
    simpa [R, G] using hdensity)
  have hgridcard := midpointPairGrid_card_eq_midpointGrid_card_sq (d := d) (n := n)
  let C : ℝ := (4 * (p : ℝ) ^ 2 *
    (L * (Nat.factorial (d - 1) : ℝ)) ^ 2 * Real.sqrt 2 *
    shellPolynomialBudget (d - 1)) /
    ((2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1))
  have hraw' :
      (∑ x : GenericGoodPair good, highPowerPairKernel p (rho x.1.1 x.2.1)) ≤
        R ^ 2 * C := by
    have hrewrite : nativeGoodPairKernelBudgetConstant d n p L *
        shellPolynomialBudget (d - 1) = R ^ 2 * C := by
      dsimp [C, nativeGoodPairKernelBudgetConstant, R]
      rw [hgridcard]
      ring
    exact hraw.trans hrewrite.le
  have hratio : R ^ 2 / G ^ 2 ≤ 1 / δ ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hG)).2
    have hsq : (δ * R) ^ 2 ≤ G ^ 2 := by
      have hgap : 0 ≤ G - δ * R := sub_nonneg.mpr (by simpa [R, G] using hdensity)
      have hsum : 0 ≤ G + δ * R := by positivity
      nlinarith
    field_simp
    nlinarith [hsq]
  have hbudget : 0 ≤ shellPolynomialBudget (d - 1) := by
    unfold shellPolynomialBudget
    exact tsum_nonneg (fun h => by positivity)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ (R ^ 2 * C) / G ^ 2 := by
      rw [hcardpair]
      exact div_le_div_of_nonneg_right hraw' (sq_nonneg G)
    _ = (R ^ 2 / G ^ 2) * C := by ring
    _ ≤ (1 / δ ^ 2) * C := mul_le_mul_of_nonneg_right hratio hC
    _ = _ := by dsimp [C]; field_simp

end BrownianSharp
