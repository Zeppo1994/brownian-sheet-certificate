import BrownianSharp.AlignmentPaperGaussianEmpiricalAssembly
import BrownianSharp.AlignmentPaperEmpiricalRateBudget

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPaperEmpiricalBudgetConversion

open BrownianSharp

/-- The extended nonnegative square root agrees with the ordinary square root
on finite nonnegative reals. -/
theorem ennrealSqrt_ofReal (x : ℝ) (hx : 0 ≤ x) :
    ennrealSqrt (ENNReal.ofReal x) = ENNReal.ofReal (Real.sqrt x) := by
  change ENNReal.ofReal x ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x)
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hx
    (by norm_num : 0 ≤ (1 / 2 : ℝ))]

/-- Convert the exact empirical budget expression used in the assembly to its
real square root. The only finiteness input is the fourth path moment M4. -/
theorem assembly_empirical_budget_eq_ofReal
    (ε : ℝ≥0) (R s K q : ℝ) (M4 : ENNReal)
    (hM4 : M4 ≠ ⊤) (hR : 0 ≤ R) (hK : 0 ≤ K) (hq : 0 ≤ q) :
    ennrealSqrt (3 * ((2 : ENNReal) *
      ((ENNReal.ofReal (3 * (ε : ℝ))) ^ 2 +
        ennrealSqrt M4 * ennrealSqrt (ENNReal.ofReal (Real.exp (-s ^ 2 / 2)))) +
      (ENNReal.ofReal (2 * R * K)) ^ 2 *
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt q))) =
      ENNReal.ofReal (Real.sqrt (3 * (2 *
        ((3 * (ε : ℝ)) ^ 2 + Real.sqrt M4.toReal * Real.exp (-s ^ 2 / 4)) +
        (2 * R * K) ^ 2 * (1 / 2 : ℝ) * Real.sqrt q))) := by
  have hM : ENNReal.ofReal M4.toReal = M4 := ENNReal.ofReal_toReal hM4
  have hMnonneg : 0 ≤ M4.toReal := ENNReal.toReal_nonneg
  have hε : 0 ≤ (ε : ℝ) := ε.2
  have htail : 0 ≤ Real.exp (-s ^ 2 / 2) := (Real.exp_pos _).le
  have htail' : Real.sqrt (Real.exp (-s ^ 2 / 2)) = Real.exp (-s ^ 2 / 4) := by
    rw [← Real.exp_half (-s ^ 2 / 2)]
    congr 1
    ring
  have hqroot : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hterm : 0 ≤ (3 * (ε : ℝ)) ^ 2 +
      Real.sqrt M4.toReal * Real.exp (-s ^ 2 / 4) := by positivity
  have hmiddle : 0 ≤ 2 *
      ((3 * (ε : ℝ)) ^ 2 + Real.sqrt M4.toReal * Real.exp (-s ^ 2 / 4)) := by positivity
  have hlast : 0 ≤ (2 * R * K) ^ 2 * (1 / 2 : ℝ) * Real.sqrt q := by positivity
  have hsum : 0 ≤ 2 *
      ((3 * (ε : ℝ)) ^ 2 + Real.sqrt M4.toReal * Real.exp (-s ^ 2 / 4)) +
      (2 * R * K) ^ 2 * (1 / 2 : ℝ) * Real.sqrt q := by positivity
  rw [← hM, ennrealSqrt_ofReal M4.toReal hMnonneg]
  rw [ennrealSqrt_ofReal (Real.exp (-s ^ 2 / 2)) htail]
  rw [htail']
  have hinner :
      3 * ((2 : ENNReal) *
        ((ENNReal.ofReal (3 * (ε : ℝ))) ^ 2 +
          ENNReal.ofReal (Real.sqrt M4.toReal) * ENNReal.ofReal (Real.exp (-s ^ 2 / 4))) +
        (ENNReal.ofReal (2 * R * K)) ^ 2 *
          ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt q)) =
      ENNReal.ofReal (3 * (2 * ((3 * (ε : ℝ)) ^ 2 +
          Real.sqrt M4.toReal * Real.exp (-s ^ 2 / 4)) +
        (2 * R * K) ^ 2 * (1 / 2 : ℝ) * Real.sqrt q)) := by
    have hpowA : ENNReal.ofReal ((3*(ε:ℝ))^2) =
        (ENNReal.ofReal (3*(ε:ℝ)))^2 := ENNReal.ofReal_pow (by positivity) 2
    have hprod : ENNReal.ofReal (Real.sqrt M4.toReal*Real.exp (-s^2/4)) =
        ENNReal.ofReal (Real.sqrt M4.toReal)*ENNReal.ofReal (Real.exp (-s^2/4)) :=
      ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    have hlastEq : ENNReal.ofReal ((2*R*K)^2*(1/2:ℝ)*Real.sqrt q) =
        (ENNReal.ofReal (2*R*K))^2*ENNReal.ofReal ((1/2:ℝ)*Real.sqrt q) := by
      rw [show (2*R*K)^2*(1/2:ℝ)*Real.sqrt q =
        (2*R*K)^2*((1/2:ℝ)*Real.sqrt q) by ring,
        ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (by positivity) 2]
    symm
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3),
      ENNReal.ofReal_add hmiddle hlast,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_add (sq_nonneg _) (by positivity),
      hpowA,hprod,hlastEq]
    norm_num
  rw [hinner]
  simp only [ENNReal.toReal_ofReal hMnonneg]
  apply ennrealSqrt_ofReal
  positivity

end BrownianSharp.AlignmentPaperEmpiricalBudgetConversion
