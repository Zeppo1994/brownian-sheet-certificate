import BrownianSharp.AlignmentPaperRademacherLower
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-! Finite sign randomization transfers scalar moment bounds to the actual
square function without constants depending on the number of terms. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPaperSquareFunctionRandomization
open AlignmentPaperRademacherLower

def finiteAverage {Ω : Type*} [Fintype Ω] (F : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card Ω : ℝ≥0∞)⁻¹ * ∑ ε, F ε

theorem ofReal_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (F : Ω → ℝ) (hF : ∀ ε, 0 ≤ F ε) :
    ENNReal.ofReal (𝔼 ε : Ω, F ε) = finiteAverage (fun ε => ENNReal.ofReal (F ε)) := by
  have hc : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Fintype.expect_eq_sum_div_card,ENNReal.ofReal_div_of_pos hc,
    ENNReal.ofReal_sum_of_nonneg (fun ε _ => hF ε)]
  simp only [finiteAverage,ENNReal.ofReal_natCast,div_eq_mul_inv,mul_comm]

theorem lintegral_finiteAverage {Ω α : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace α] (μ : Measure α) (F : Ω → α → ℝ≥0∞)
    (hF : ∀ ε, Measurable (F ε)) :
    (∫⁻ x, finiteAverage (fun ε => F ε x) ∂μ) =
      finiteAverage (fun ε => ∫⁻ x, F ε x ∂μ) := by
  have hc : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold finiteAverage
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc),
    lintegral_finsetSum Finset.univ (fun ε _ => hF ε)]

theorem finiteAverage_mono {Ω : Type*} [Fintype Ω] {F G : Ω → ℝ≥0∞}
    (h : ∀ ε, F ε ≤ G ε) : finiteAverage F ≤ finiteAverage G := by
  unfold finiteAverage
  gcongr
  exact h _

theorem finiteAverage_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ≥0∞) (F : Ω → ℝ≥0∞) :
    finiteAverage (fun ε => c*F ε) = c*finiteAverage F := by
  unfold finiteAverage
  rw [← Finset.mul_sum]
  ring

/-- Scalar bounds uniform over all finite sign choices extend to finite
Hilbert families. This is the vectorization step needed for tensor coordinates. -/
theorem square_moment_le_of_signed_moments
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) {n : ℕ}
    (f : Fin n → α → ℂ) (g : Fin n → β → ℂ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    {p C : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) (_hC : 0 ≤ C)
    (hbound : ∀ ε : Fin n → Bool,
      (∫⁻ y, ENNReal.ofReal (‖complexSignRow (fun i => g i y) ε‖^p) ∂ν) ≤
        ENNReal.ofReal C *
          (∫⁻ x, ENNReal.ofReal (‖complexSignRow (fun i => f i x) ε‖^p) ∂μ)) :
    (∫⁻ y, ENNReal.ofReal ((∑ i, ‖g i y‖^2)^(p/2)) ∂ν) ≤
      (ENNReal.ofReal (24*(2 : ℝ)^(p/2)) * ENNReal.ofReal C) *
        (∫⁻ x, ENNReal.ofReal ((∑ i, ‖f i x‖^2)^(p/2)) ∂μ) := by
  let K : ℝ := 24*(2 : ℝ)^(p/2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hgm (ε : Fin n → Bool) : Measurable (fun y =>
      ENNReal.ofReal (‖complexSignRow (fun i => g i y) ε‖^p)) := by
    have hs : Measurable (fun y => complexSignRow (fun i => g i y) ε) := by
      dsimp [complexSignRow]
      fun_prop
    fun_prop
  have hfm (ε : Fin n → Bool) : Measurable (fun x =>
      ENNReal.ofReal (‖complexSignRow (fun i => f i x) ε‖^p)) := by
    have hs : Measurable (fun x => complexSignRow (fun i => f i x) ε) := by
      dsimp [complexSignRow]
      fun_prop
    fun_prop
  have hgp (y : β) : ENNReal.ofReal ((∑ i, ‖g i y‖^2)^(p/2)) ≤
      ENNReal.ofReal K * finiteAverage (fun ε : Fin n → Bool =>
        ENNReal.ofReal (‖complexSignRow (fun i => g i y) ε‖^p)) := by
    have h := ENNReal.ofReal_le_ofReal (complexSignRow_lower_moment (fun i => g i y) hp hp2)
    rw [ENNReal.ofReal_mul hK,ofReal_expect _ (fun ε => Real.rpow_nonneg (norm_nonneg _) p)] at h
    exact h
  have hfp (x : α) : finiteAverage (fun ε : Fin n → Bool =>
        ENNReal.ofReal (‖complexSignRow (fun i => f i x) ε‖^p)) ≤
      ENNReal.ofReal ((∑ i, ‖f i x‖^2)^(p/2)) := by
    rw [← ofReal_expect _ (fun ε => Real.rpow_nonneg (norm_nonneg _) p)]
    exact ENNReal.ofReal_le_ofReal (complexSignRow_upper_moment (fun i => f i x) hp.le hp2)
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal K * finiteAverage (fun ε : Fin n → Bool =>
        ENNReal.ofReal (‖complexSignRow (fun i => g i y) ε‖^p)) ∂ν := lintegral_mono hgp
    _ = ENNReal.ofReal K * finiteAverage (fun ε : Fin n → Bool =>
        ∫⁻ y, ENNReal.ofReal (‖complexSignRow (fun i => g i y) ε‖^p) ∂ν) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finiteAverage ν _ hgm]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal C * finiteAverage (fun ε : Fin n → Bool =>
        ∫⁻ x, ENNReal.ofReal (‖complexSignRow (fun i => f i x) ε‖^p) ∂μ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (finiteAverage_mono hbound).trans_eq (finiteAverage_const_mul _ _)
    _ = (ENNReal.ofReal K * ENNReal.ofReal C) *
        (∫⁻ x, finiteAverage (fun ε : Fin n → Bool =>
          ENNReal.ofReal (‖complexSignRow (fun i => f i x) ε‖^p)) ∂μ) := by
      rw [lintegral_finiteAverage μ _ hfm]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact lintegral_mono hfp

end BrownianSharp.AlignmentPaperSquareFunctionRandomization
