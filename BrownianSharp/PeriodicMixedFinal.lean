import BrownianSharp.PeriodicMixedCertified
import BrownianSharp.NativeNikolskyCertified

/-! The final periodic mixed-smoothness entropy statement, with all three
class bounds discharged by the actual native Gaussian construction. -/

noncomputable section

namespace BrownianSharp

theorem periodicMixedEntropy_certified : PeriodicMixedEntropyStatement := by
  apply periodic_mixed_entropy_of_actual_finite_theta_and_nikolsky
  intro d hd p r hp hpr
  have hr : 0 < r := lt_trans (inv_pos.mpr (by linarith)) hpr
  let m : ℕ := Nat.ceil (r + 2)
  let K : ℕ := m + m
  have hm : r + 2 ≤ (m : ℝ) := by
    dsimp [m]
    exact_mod_cast Nat.le_ceil (r + 2)
  have hK : Even K := by
    exact ⟨m, rfl⟩
  have hKpos : 0 < K := by
    have hm1 : 1 ≤ m := by
      have hmR : (1:ℝ) ≤ (m:ℝ) := by linarith
      exact_mod_cast hmR
    dsimp [K]
    omega
  have hKr : r < (K : ℝ) := by
    have hKreal : (K : ℝ) = 2 * (m : ℝ) := by
      dsimp [K]
      push_cast
      ring
    rw [hKreal]
    linarith
  simpa [logarithmicIndexRate, mul_assoc] using
    periodicNikolsky_entropy_of_native_good_event hd p r hp hr K hK hKpos hKr

end BrownianSharp
