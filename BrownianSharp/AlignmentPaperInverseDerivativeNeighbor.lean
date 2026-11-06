import BrownianSharp.AlignmentPaperInverseFirstDerivative
import BrownianSharp.YoungLp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! Neighboring inverse-derivative blocks have the expected uniform dyadic
`L¹` size. This is the kernel estimate used with continuous dyadic source
blocks, avoiding an extension of Young's inequality to raw `Lp` classes. -/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperInverseDerivativeNeighbor

open BrownianSharp
open BrownianSharp.InverseDerivativeProfile
open BrownianSharp.AlignmentPaperInverseFirstDerivative

local instance circleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- The three neighboring inverse blocks, with the natural truncated sets at
levels zero and one. -/
def neighborScales (s : ℕ) : Finset ℕ :=
  (Finset.range (s+2)).filter (fun j => s-1 ≤ j)

def neighborInverseKernel (s : ℕ) : C(UnitAddCircle, ℂ) :=
  ∑ j ∈ neighborScales s, inverseMultiplierKernel j 1

private lemma neighborScales_eq (s : ℕ) :
    neighborScales s = {s-1, s, s+1} := by
  ext j
  simp only [neighborScales, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  omega

/-- The neighboring inverse blocks have summable `L¹` size at every level. -/
theorem exists_neighborInverseKernel_L1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ,
      (∫ x : UnitAddCircle, ‖neighborInverseKernel s x‖
        ∂AddCircle.haarAddCircle) ≤ C * ((2:ℝ)^s)⁻¹ := by
  obtain ⟨C₀, hC₀, hbase⟩ := exists_inverseFirstDerivativeKernel_allGrade_L1_bound
  refine ⟨6*C₀, by positivity, ?_⟩
  intro s
  have hsum : neighborScales s = {s-1, s, s+1} := neighborScales_eq s
  rw [neighborInverseKernel, hsum]
  have hnorm :
      (∫ x : UnitAddCircle,
        ‖∑ j ∈ ({s-1, s, s+1} : Finset ℕ), inverseMultiplierKernel j 1 x‖
          ∂AddCircle.haarAddCircle) ≤
        ∑ j ∈ ({s-1, s, s+1} : Finset ℕ),
          ∫ x : UnitAddCircle, ‖inverseMultiplierKernel j 1 x‖
            ∂AddCircle.haarAddCircle := by
    calc
      _ ≤ ∫ x : UnitAddCircle,
          ∑ j ∈ ({s-1, s, s+1} : Finset ℕ), ‖inverseMultiplierKernel j 1 x‖
            ∂AddCircle.haarAddCircle := by
          apply integral_mono
          · simpa [neighborInverseKernel, hsum] using
              (neighborInverseKernel s).continuous.norm.integrable_of_hasCompactSupport
                (μ := AddCircle.haarAddCircle)
                (HasCompactSupport.of_compactSpace _)
          · exact integrable_finsetSum ({s-1, s, s+1} : Finset ℕ)
              (fun j hj => (inverseMultiplierKernel j 1).continuous.norm
                |>.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
                  (HasCompactSupport.of_compactSpace _))
          · intro x
            exact norm_sum_le _ _
      _ = _ := by
        rw [integral_finsetSum ({s-1, s, s+1} : Finset ℕ)
          (fun j hj => (inverseMultiplierKernel j 1).continuous.norm
            |>.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
              (HasCompactSupport.of_compactSpace _))]
  have hterms : ∀ j ∈ ({s-1, s, s+1} : Finset ℕ),
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel j 1 x‖
          ∂AddCircle.haarAddCircle) ≤ C₀ * ((2:ℝ)^j)⁻¹ := by
    intro j hj
    exact hbase j
  have hpow : ∀ j ∈ ({s-1, s, s+1} : Finset ℕ),
      ((2:ℝ)^j)⁻¹ ≤ 2 * ((2:ℝ)^s)⁻¹ := by
    intro j hj
    have hjlow : s-1 ≤ j := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      omega
    have hpowmono : ((2:ℝ)^s) ≤ ((2:ℝ)^j * 2) := by
      have : s ≤ j+1 := by omega
      calc
        (2:ℝ)^s ≤ (2:ℝ)^(j+1) := by exact pow_le_pow_right₀ (by norm_num) this
        _ = (2:ℝ)^j * 2 := by rw [pow_succ]
    have hpositive : 0 < (2:ℝ)^s := by positivity
    have hjpositive : 0 < (2:ℝ)^j := by positivity
    rw [inv_eq_one_div, inv_eq_one_div]
    field_simp
    nlinarith
  calc
    _ ≤ ∑ j ∈ ({s-1, s, s+1} : Finset ℕ),
        ∫ x : UnitAddCircle, ‖inverseMultiplierKernel j 1 x‖
          ∂AddCircle.haarAddCircle := by
            simpa [neighborInverseKernel, hsum] using hnorm
    _ ≤ ∑ j ∈ ({s-1, s, s+1} : Finset ℕ), C₀ * ((2:ℝ)^j)⁻¹ := by
      exact Finset.sum_le_sum hterms
    _ ≤ ∑ j ∈ ({s-1, s, s+1} : Finset ℕ),
        C₀ * (2 * ((2:ℝ)^s)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hpow j hj) (le_of_lt hC₀)
    _ ≤ 6*C₀*((2:ℝ)^s)⁻¹ := by
      have hconst : ∀ j ∈ ({s-1, s, s+1} : Finset ℕ),
          C₀ * (2 * ((2:ℝ)^s)⁻¹) = 2*C₀*((2:ℝ)^s)⁻¹ := by
        intro j hj
        ring
      rw [Finset.sum_congr rfl hconst, Finset.sum_const]
      have hcard : ({s-1, s, s+1} : Finset ℕ).card ≤ 3 := Finset.card_le_three
      simp only [nsmul_eq_mul]
      calc
        _ ≤ 3 * (2*C₀*((2:ℝ)^s)⁻¹) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ = 6*C₀*((2:ℝ)^s)⁻¹ := by ring

end BrownianSharp.AlignmentPaperInverseDerivativeNeighbor

end
