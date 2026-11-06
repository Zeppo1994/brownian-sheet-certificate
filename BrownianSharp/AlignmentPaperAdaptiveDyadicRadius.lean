import BrownianSharp.AlignmentPaperAdaptiveCardinalityCost

/-! Actual dyadic stage-radius comparisons. All scale factors are explicit;
these estimates do not supply an entropy or approximation conclusion as an
input hypothesis. -/
noncomputable section
namespace BrownianSharp.AlignmentPaperAdaptiveDyadicRadius

def dyadicRadius (T p : ℝ) (j : ℕ) : ℝ := T * ((2:ℝ)^j)^(-1/p)
def dyadicMesh (T p : ℝ) (J j : ℕ) : ℝ :=
  dyadicRadius T p J / (2:ℝ)^(J-j)

theorem dyadicRadius_pos {T p : ℝ} (hT : 0 < T) (j : ℕ) :
    0 < dyadicRadius T p j := mul_pos hT (Real.rpow_pos_of_pos (by positivity) _)

theorem dyadicMesh_pos {T p : ℝ} (hT : 0 < T) (J j : ℕ) :
    0 < dyadicMesh T p J j := div_pos (dyadicRadius_pos hT J) (by positivity)

theorem dyadicRadius_rebase {T p : ℝ} {j J : ℕ}
    (hT : 0 ≤ T) (hp : 1 < p) (hj : j ≤ J) :
    dyadicRadius T p j ≤ dyadicRadius T p J * (2:ℝ)^(J-j) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 ≤ 1 + (-1/p) := by
    have hdiv : 1/p ≤ (1:ℝ) := (div_le_iff₀ hp0).mpr (by simpa only [one_mul] using hp.le)
    simp only [neg_div]
    linarith
  have hgap : 1 ≤ ((2:ℝ)^(J-j))^(1+(-1/p)) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) hq
  have hpow : (2:ℝ)^J = (2:ℝ)^j * (2:ℝ)^(J-j) := by
    rw [←pow_add, Nat.add_sub_of_le hj]
  calc
    dyadicRadius T p j ≤ dyadicRadius T p j * ((2:ℝ)^(J-j))^(1+(-1/p)) := by
      exact le_mul_of_one_le_right (mul_nonneg hT (Real.rpow_nonneg (by positivity) _)) hgap
    _ = dyadicRadius T p J * (2:ℝ)^(J-j) := by
      unfold dyadicRadius
      rw [hpow, Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_add (by positivity), Real.rpow_one]
      ring

theorem firstRadius_mesh_ratio {T p : ℝ} (hT : 0 < T) (hp : 1 < p) (J : ℕ) :
    (2*dyadicRadius T p 0) / dyadicMesh T p J 0 ≤ 3*(2:ℝ)^(2*J) := by
  have hbound := dyadicRadius_rebase hT.le hp (Nat.zero_le J)
  have hmesh := dyadicMesh_pos (p := p) hT J 0
  rw [div_le_iff₀ hmesh]
  unfold dyadicMesh
  simp only [Nat.sub_zero] at hbound ⊢
  have hpos : 0 < (2:ℝ)^J := by positivity
  have heq : 3*(2:ℝ)^(2*J)*(dyadicRadius T p J / (2:ℝ)^J) =
      3 * dyadicRadius T p J * (2:ℝ)^J := by
    rw [show 2*J = J+J by omega, pow_add]
    field_simp
  rw [heq]
  nlinarith [dyadicRadius_pos (p := p) hT J]

theorem adjacentRadius_mesh_ratio {T p : ℝ} {j J : ℕ}
    (hT : 0 < T) (hp : 1 < p) (hj0 : 1 ≤ j) (hj : j ≤ J) :
    (dyadicRadius T p j + dyadicRadius T p (j-1)) / dyadicMesh T p J j ≤
      3*(2:ℝ)^(2*(J-j)) := by
  have h₁ := dyadicRadius_rebase hT.le hp hj
  have h₂ := dyadicRadius_rebase hT.le hp (show j-1 ≤ J by omega)
  have hgap : J-(j-1) = (J-j)+1 := by omega
  rw [hgap, pow_succ] at h₂
  rw [div_le_iff₀ (dyadicMesh_pos (p := p) hT J j)]
  unfold dyadicMesh
  have heq : 3*(2:ℝ)^(2*(J-j))*(dyadicRadius T p J / (2:ℝ)^(J-j)) =
      3 * dyadicRadius T p J * (2:ℝ)^(J-j) := by
    rw [show 2*(J-j) = (J-j)+(J-j) by omega, pow_add]
    field_simp
  rw [heq]
  nlinarith
end BrownianSharp.AlignmentPaperAdaptiveDyadicRadius
