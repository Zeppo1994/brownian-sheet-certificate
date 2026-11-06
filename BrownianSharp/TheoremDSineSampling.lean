import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

noncomputable section

namespace HaarQuarter.TheoremD.SineSampling

end HaarQuarter.TheoremD.SineSampling

namespace HaarQuarter.TheoremD.SineSampling

def midpointAngle (M j : ℕ) : ℝ :=
  Real.pi * ((j : ℝ) + 1 / 2) / M

/-- The nonconstant cosine modes vanish on the midpoint DCT grid. -/
theorem midpoint_cos_sum_eq_zero (M k : ℕ) (hM : 0 < M)
    (hk : 0 < k) (hkupper : k < 2 * M) :
    ∑ j ∈ Finset.range M, Real.cos ((k : ℝ) * midpointAngle M j) = 0 := by
  let a : ℝ := Real.pi * k / M
  have hMcast : (0 : ℝ) < M := by exact_mod_cast hM
  have hkcast : (0 : ℝ) < k := by exact_mod_cast hk
  have hkupcast : (k : ℝ) < 2 * M := by exact_mod_cast hkupper
  have hangle (j : ℕ) : a * (j : ℝ) + a / 2 = (k : ℝ) * midpointAngle M j := by
    dsimp [a, midpointAngle]
    field_simp
  have hphase : (M : ℝ) * a / 2 = (k : ℝ) * Real.pi / 2 := by
    dsimp [a]
    field_simp
  have hphase' : ((M - 1 : ℕ) : ℝ) * a / 2 + a / 2 =
      (k : ℝ) * Real.pi / 2 := by
    have hM1 : 1 ≤ M := hM
    rw [Nat.cast_sub hM1]
    dsimp [a]
    field_simp
    ring
  have hsinarg : Real.sin (Real.pi * k / (2 * M)) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · positivity
    · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
      nlinarith [Real.pi_pos, hkupcast]
  have htrig : Real.sin ((k : ℝ) * Real.pi / 2) *
      Real.cos ((k : ℝ) * Real.pi / 2) = 0 := by
    have hz : Real.sin (k * Real.pi) = 0 := Real.sin_nat_mul_pi k
    have hdouble := Real.sin_two_mul ((k : ℝ) * Real.pi / 2)
    rw [show 2 * ((k : ℝ) * Real.pi / 2) = (k : ℝ) * Real.pi by ring] at hdouble
    nlinarith
  have hsum := Real.sin_mul_sum_cos M a (a / 2)
  have hprod : Real.sin (a / 2) *
      (∑ j ∈ Finset.range M, Real.cos ((k : ℝ) * midpointAngle M j)) = 0 := by
    calc
      _ = Real.sin (a / 2) *
          (∑ j ∈ Finset.range M, Real.cos (a * (j : ℝ) + a / 2)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [← hangle]
      _ = Real.sin ((M : ℝ) * a / 2) *
          Real.cos (((M - 1 : ℕ) : ℝ) * a / 2 + a / 2) := by
            have hM1 : 1 ≤ M := hM
            have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
              rw [Nat.cast_sub hM1]
              norm_num
            rw [hcast]
            exact hsum
      _ = 0 := by rw [hphase, hphase']; exact htrig
  have ha : a / 2 = Real.pi * k / (2 * M) := by dsimp [a]; field_simp
  have hsinarg' : Real.sin (a / 2) ≠ 0 := by rw [ha]; exact hsinarg
  exact (mul_eq_zero.mp hprod).resolve_left hsinarg'

end HaarQuarter.TheoremD.SineSampling

open scoped BigOperators

namespace HaarQuarter.TheoremD.SineSampling

end HaarQuarter.TheoremD.SineSampling
