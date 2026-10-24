import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

noncomputable section

namespace HaarQuarter.TheoremD.SineSampling

/-- The selected frequencies are a shifted DCT-II cosine grid. -/
theorem selected_sine_eq_signed_cos (M j r : ℕ) (hM : 0 < M) :
    Real.sin ((M + r : ℕ) * (Real.pi * ((j : ℝ) + 1 / 2) / M)) =
      (-1 : ℝ) ^ j * Real.cos (r * (Real.pi * ((j : ℝ) + 1 / 2) / M)) := by
  let θ : ℝ := Real.pi * ((j : ℝ) + 1 / 2) / M
  have hphase : (M : ℝ) * θ = Real.pi / 2 + (j : ℝ) * Real.pi := by
    dsimp [θ]
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
    ring
  have hangle : ((M + r : ℕ) : ℝ) * θ =
      (Real.pi / 2 + (j : ℝ) * Real.pi) + (r : ℝ) * θ := by
    rw [Nat.cast_add]
    calc
      ((M : ℝ) + (r : ℝ)) * θ = (M : ℝ) * θ + (r : ℝ) * θ := by ring
      _ = _ := by rw [hphase]
  have hsin : Real.sin (Real.pi / 2 + (j : ℝ) * Real.pi) = (-1 : ℝ) ^ j := by
    rw [Real.sin_add_nat_mul_pi]
    simp
  have hcos : Real.cos (Real.pi / 2 + (j : ℝ) * Real.pi) = 0 := by
    rw [Real.cos_add_nat_mul_pi]
    simp
  rw [hangle, Real.sin_add, hsin, hcos]
  dsimp [θ]
  ring

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

/-- Finite integer sine polynomials have exact reflection antisymmetry. -/
theorem finite_sine_polynomial_reflection (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (∑ k ∈ s, a k * Real.sin ((2 * Real.pi * k) * (1 - x))) =
      -(∑ k ∈ s, a k * Real.sin ((2 * Real.pi * k) * x)) := by
  calc
    _ = ∑ k ∈ s, -(a k * Real.sin ((2 * Real.pi * k) * x)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hsin : Real.sin ((2 * Real.pi * k) * (1 - x)) =
          -Real.sin ((2 * Real.pi * k) * x) := by
        rw [show (2 * Real.pi * k) * (1 - x) =
          (k : ℝ) * (2 * Real.pi) - ((2 * Real.pi * k) * x) by ring,
          Real.sin_nat_mul_two_pi_sub]
      rw [hsin]
      ring
    _ = _ := by rw [Finset.sum_neg_distrib]

/-- An antisymmetric function's full midpoint grid has twice the absolute
mass of the first half grid. -/
theorem full_midpoint_abs_sum_eq_twice_half
    (M : ℕ) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : ∀ x, f (1 - x) = -f x) :
    (∑ j ∈ Finset.range (2 * M),
      |f (((j : ℝ) + 1 / 2) / (2 * M))|) =
      2 * ∑ j ∈ Finset.range M, |f (((j : ℝ) + 1 / 2) / (2 * M))| := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpoint (j : ℕ) (hj : j < M) :
      |f ((((M + j : ℕ) : ℝ) + 1 / 2) / (2 * M))| =
      |f ((((M - 1 - j : ℕ) : ℝ) + 1 / 2) / (2 * M))| := by
    have hnat : M - 1 - j + j + 1 = M := by omega
    have hcast : ((M - 1 - j : ℕ) : ℝ) + (j : ℝ) + 1 = M := by exact_mod_cast hnat
    have hx : ((((M + j : ℕ) : ℝ) + 1 / 2) / (2 * M)) =
        1 - ((((M - 1 - j : ℕ) : ℝ) + 1 / 2) / (2 * M)) := by
      push_cast
      field_simp
      nlinarith [hcast]
    rw [hx, hf, abs_neg]
  rw [show 2 * M = M + M by omega, Finset.sum_range_add]
  have hsum : (∑ j ∈ Finset.range M,
      |f ((((M + j : ℕ) : ℝ) + 1 / 2) / (2 * M))|) =
      ∑ j ∈ Finset.range M, |f (((j : ℝ) + 1 / 2) / (2 * M))| := by
    calc
      _ = ∑ j ∈ Finset.range M,
          |f ((((M - 1 - j : ℕ) : ℝ) + 1 / 2) / (2 * M))| := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint j (Finset.mem_range.mp hj)
      _ = _ := Finset.sum_range_reflect (fun j => |f (((j : ℝ) + 1 / 2) / (2 * M))|) M
  rw [hsum]
  ring

end HaarQuarter.TheoremD.SineSampling
