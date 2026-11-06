import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpAggregateBudget

/-- Finite mixed square-function budget: for `1 ≤ p ≤ 2`, the sum of the
squared Lp sizes of finitely many frequency blocks is controlled by the Lp
size of their pointwise square function. This is the aggregate estimate that
avoids taking a separate Besov-∞ bound at each dyadic block. -/
theorem finite_block_lp_square_budget {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    {M : ℕ} (f : Fin M → X → ℝ) (S : X → ℝ)
    (hf : ∀ i, Integrable (fun x => |f i x| ^ p) μ)
    (hS : Integrable (fun x => S x ^ p) μ)
    (hSnonneg : ∀ᵐ x ∂μ, 0 ≤ S x)
    (hsquare : ∀ᵐ x ∂μ, ∑ i, |f i x| ^ 2 ≤ S x ^ 2) :
    (∑ i : Fin M, (∫ x, |f i x| ^ p ∂μ) ^ (2 / p)) ^ (p / 2) ≤
      ∫ x, S x ^ p ∂μ := by
  classical
  let q : ℝ := 2 / p
  let qE : ℝ≥0∞ := ENNReal.ofReal q
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqfinite : qE ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqge1 : 1 ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hp]
    nlinarith
  have hqFact : Fact (1 ≤ qE) := by
    constructor
    simpa [qE] using ENNReal.ofReal_le_ofReal hqge1
  let u : X → PiLp qE (fun _ : Fin M => ℝ) := fun x =>
    WithLp.toLp qE (fun i => |f i x| ^ p)
  have huCoord : ∀ i, Integrable (fun x => u x i) μ := by
    intro i
    simpa [u] using hf i
  have huInt : Integrable u μ := Integrable.of_eval_piLp huCoord
  have huNormMeas : AEStronglyMeasurable (fun x => ‖u x‖) μ :=
    huInt.norm.aestronglyMeasurable
  have huNormInt : Integrable (fun x => ‖u x‖) μ := huInt.norm
  have huNormPoint : ∀ᵐ x ∂μ, ‖u x‖ ≤ S x ^ p := by
    filter_upwards [hSnonneg, hsquare] with x hSx hsq
    have hsum_nonneg : 0 ≤ ∑ i : Fin M, |f i x| ^ 2 :=
      Finset.sum_nonneg fun i hi => by positivity
    have hpow :
        (∑ i : Fin M, |f i x| ^ 2) ^ (p / 2) ≤ (S x ^ 2) ^ (p / 2) :=
      Real.rpow_le_rpow hsum_nonneg hsq (div_nonneg hp.le (by norm_num))
    have hsqpow : (S x ^ 2) ^ (p / 2) = S x ^ p := by
      rw [← Real.rpow_natCast_mul hSx 2 (p / 2)]
      congr 1 <;> ring
    have hnorm : ‖u x‖ = (∑ i : Fin M, |f i x| ^ 2) ^ (p / 2) := by
      change ‖WithLp.toLp qE (fun i => |f i x| ^ p)‖ = _
      rw [PiLp.norm_eq_sum (by
        rw [ENNReal.toReal_ofReal (le_of_lt hqpos)]
        exact hqpos) (WithLp.toLp qE (fun i => |f i x| ^ p))]
      have hqEreal : qE.toReal = q := by simp [qE, hqpos.le]
      rw [hqEreal]
      simp_rw [Real.norm_eq_abs]
      simp_rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      have hterm (i : Fin M) : (|f i x| ^ p) ^ q = |f i x| ^ 2 := by
        rw [← Real.rpow_mul (abs_nonneg _) p q]
        rw [show p * q = 2 by dsimp [q]; field_simp]
        exact Real.rpow_natCast (|f i x|) 2
      simp_rw [hterm]
      rw [show 1 / q = p / 2 by dsimp [q]; field_simp]
    rw [hnorm]
    calc
      (∑ i : Fin M, |f i x| ^ 2) ^ (p / 2) ≤ (S x ^ 2) ^ (p / 2) := hpow
      _ = S x ^ p := hsqpow
  have hnormIntegral := norm_integral_le_integral_norm (μ := μ) u
  have hpointIntegral := integral_mono_ae huNormInt hS (huNormPoint)
  have hleft :
      ‖∫ x, u x ∂μ‖ =
        (∑ i : Fin M, (∫ x, |f i x| ^ p ∂μ) ^ (2 / p)) ^ (p / 2) := by
    rw [PiLp.norm_eq_sum (by
      rw [ENNReal.toReal_ofReal (le_of_lt hqpos)]
      exact hqpos) (∫ x, u x ∂μ)]
    have hqEreal : qE.toReal = q := by simp [qE, hqpos.le]
    rw [hqEreal]
    have heval (i : Fin M) : (∫ x, u x ∂μ) i = ∫ x, |f i x| ^ p ∂μ := by
      rw [eval_integral_piLp huCoord]
    rw [show 1 / q = p / 2 by dsimp [q]; field_simp]
    simp_rw [heval, Real.norm_eq_abs]
    have hnonneg (i : Fin M) : 0 ≤ ∫ x, |f i x| ^ p ∂μ :=
      integral_nonneg (fun x => by positivity)
    simp_rw [abs_of_nonneg (hnonneg _)]
    simp [q]
  calc
    (∑ i : Fin M, (∫ x, |f i x| ^ p ∂μ) ^ (2 / p)) ^ (p / 2) =
        ‖∫ x, u x ∂μ‖ := hleft.symm
    _ ≤ ∫ x, ‖u x‖ ∂μ := hnormIntegral
    _ ≤ ∫ x, S x ^ p ∂μ := hpointIntegral

end BrownianSharp.AlignmentPaperAnchoredLpAggregateBudget
