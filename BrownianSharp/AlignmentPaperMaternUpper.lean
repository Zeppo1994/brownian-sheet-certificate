import BrownianSharp.AlignmentPaperMaternSourceEnergy
import BrownianSharp.AlignmentPaperMatern
import BrownianSharp.AlignmentMaternTensorFeature
import BrownianSharp.AlignmentMaternSpectralFeature
import BrownianSharp.AlignmentPaperMixedWeight
import BrownianSharp.AlignmentPaperCubePeriodization
import BrownianSharp.AlignmentPaperPeriodicRealPartEnergy
import BrownianSharp.AlignmentPeriodicSpectralEnergy
import BrownianSharp.AlignmentPaperPeriodicFourierReverse
import BrownianSharp.AlignmentScaledSetWidth
import BrownianSharp.AlignmentPaperWidthContraction
import BrownianSharp.AlignmentPaperContinuousSmoothing
import BrownianSharp.AlignmentPaperPeriodicCompactness
import BrownianSharp.AlignmentLatestPeriodicWidths
import BrownianSharp.AlignmentEndpointDyadicEntropy
import BrownianSharp.AlignmentAuditPeriodicBoundedness
import BrownianSharp.AlignmentPaperGaussianFeatureBridge
import BrownianSharp.AlignmentWidthRates
import Mathlib.Tactic

/-! Concrete period-eight weighted Fourier-kernel estimates for the upper
Matérn source inclusion. -/

noncomputable section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperMaternUpper

open BrownianSharp.AlignmentPaperMaternSourceEnergy
open BrownianSharp.AlignmentPaperMixedWeight
open BrownianSharp.AlignmentMaternComplexFeature
open BrownianSharp.AlignmentMaternSpectralFeature
open BrownianSharp.AlignmentPaperGaussianFeatureBridge
open BrownianSharp.AlignmentMaternSpectralWeights
open BrownianSharp.AlignmentPeriodicSpectralEnergy

/-- Square-root form of the mixed Bessel-weight moderation inequality. -/
theorem mixedWeight_sqrt_ratio_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (x y : Fin d → ℝ) :
    Real.sqrt (mixedWeight r x / mixedWeight r y) ≤
      (2 : ℝ) ^ (r * d / 2) * mixedWeight (r / 2) (x-y) := by
  have hratio := mixedWeight_ratio_le r hr x y
  have hconst : (Real.rpow (2 : ℝ) (r * d / 2)) ^ (2 : ℕ) =
      Real.rpow (2 : ℝ) (r * d) := by
    calc
      (Real.rpow (2 : ℝ) (r * d / 2)) ^ (2 : ℕ) =
          Real.rpow (Real.rpow (2 : ℝ) (r * d / 2)) (2 : ℝ) :=
            (Real.rpow_natCast _ _).symm
      _ = Real.rpow (2 : ℝ) ((r * d / 2) * (2 : ℝ)) :=
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = Real.rpow (2 : ℝ) (r * d) := by congr 1 <;> ring
  have hweight : mixedWeight (r / 2) (x-y) ^ 2 = mixedWeight r (x-y) := by
    unfold mixedWeight
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    calc
      (Real.rpow (1 + (x-y) i ^ 2) (r / 2)) ^ (2 : ℕ) =
          Real.rpow (Real.rpow (1 + (x-y) i ^ 2) (r / 2)) (2 : ℝ) :=
            (Real.rpow_natCast _ _).symm
      _ = Real.rpow (1 + (x-y) i ^ 2) ((r / 2) * (2 : ℝ)) :=
            (Real.rpow_mul (by positivity) _ _).symm
      _ = Real.rpow (1 + (x-y) i ^ 2) r := by congr 1 <;> ring
  have hsq : (((2 : ℝ) ^ (r * d / 2) * mixedWeight (r / 2) (x-y)) ^ (2 : ℕ)) =
        (2 : ℝ) ^ (r * d) * mixedWeight r (x-y) := by
    change (((Real.rpow (2 : ℝ) (r * d / 2) *
      mixedWeight (r / 2) (x-y)) ^ (2 : ℕ)) =
        Real.rpow (2 : ℝ) (r * d) * mixedWeight r (x-y))
    rw [mul_pow, hconst, hweight]
  apply (Real.sqrt_le_iff).2
  constructor
  · have hpos : 0 < (2 : ℝ) ^ (r * d / 2) * mixedWeight (r / 2) (x-y) :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (mixedWeight_pos (r / 2) (x-y))
    exact hpos.le
  · rw [hsq]
    exact hratio

/-- The positive weighted kernel used in the continuous-to-discrete Schur
estimate. -/
def periodEightSchurKernel {d : ℕ} (r : ℝ)
    (k : Fin d → ℤ) (ξ : Fin d → ℝ) : ℝ :=
  Real.sqrt (mixedWeight r (fun i => (k i : ℝ) / 8) / mixedWeight r ξ) *
    ‖tensorCubeCutoffFourierKernel
      (fun i => (k i : ℝ) / 8) ξ‖

/-- Pointwise domination of the Schur kernel by the period-eight tensor
cutoff majorant whose row and column masses are already established. -/
theorem periodEightSchurKernel_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (k : Fin d → ℤ) (ξ : Fin d → ℝ) :
    periodEightSchurKernel r k ξ ≤
      (2 : ℝ) ^ (r * d / 2) *
        mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ := by
  unfold periodEightSchurKernel
  exact mul_le_mul_of_nonneg_right
    (mixedWeight_sqrt_ratio_le r hr _ _)
    (norm_nonneg _)

/-- Every finite sampled column of the weighted period-eight kernel has a
uniform bound. This is the discrete half of the Schur estimate, now for the
actual weighted cutoff kernel rather than just its Schwartz majorant. -/
theorem periodEightSchurKernel_finite_column_bound {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : Finset (Fin d → ℤ)) (ξ : Fin d → ℝ),
      ∑ k ∈ S, periodEightSchurKernel r k ξ ≤ B := by
  obtain ⟨C, hC, hbound⟩ :=
    tensorPeriodEightBesselKernel_lattice_bound (d := d) (r := r) hr N hrN
  refine ⟨(2 : ℝ) ^ (r * d / 2) * C, mul_nonneg (by positivity) hC, ?_⟩
  intro S ξ
  calc
    ∑ k ∈ S, periodEightSchurKernel r k ξ ≤
        ∑ k ∈ S, (2 : ℝ) ^ (r * d / 2) *
          mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
            ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ := by
              apply Finset.sum_le_sum
              intro k hk
              exact periodEightSchurKernel_le r hr k ξ
    _ = ∑ k ∈ S, (2 : ℝ) ^ (r * d / 2) *
        (mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
          ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
    _ = (2 : ℝ) ^ (r * d / 2) *
        ∑ k ∈ S, mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
            ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ := by
              rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (r * d / 2) * C := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsum := (hbound ξ).1.sum_le_tsum S (fun k hk => by
            exact mul_nonneg
              (mixedWeight_pos (r / 2) (fun i => (k i : ℝ) / 8 - ξ i)).le
              (norm_nonneg _))
          exact hsum.trans (hbound ξ).2

/-- The Schwartz majorant of the weighted kernel is integrable in the source
frequency variable. This establishes the analytic integrability needed before
using the continuous row side of Schur's test. -/
theorem periodEightSchurMajorant_integrable {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N)
    (k : Fin d → ℤ) :
    Integrable (fun ξ : Fin d → ℝ =>
      mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖)
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  let f : Fin d → ℝ → ℝ := fun i ξ =>
    (1 + (k i / 8 - ξ) ^ 2) ^ (r / 2) *
      ‖cubeSpatialCutoffFourierSchwartz (k i / 8 - ξ)‖
  have hf : ∀ i, Integrable (f i) volume := by
    intro i
    let a : ℝ := (k i : ℝ) / 8
    have hbase := besselWeightedCutoffKernel_integrable (r / 2) N
      (by linarith) hrN
    let e : ℝ ≃ₜ ℝ := {
      toEquiv := {
        toFun := fun x => a - x
        invFun := fun x => a - x
        left_inv := by intro x; dsimp; ring
        right_inv := by intro x; dsimp; ring }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
      Measure.measurePreserving_neg volume
    have hadd : MeasurePreserving (fun x : ℝ => x + a) volume volume := by
      exact ⟨measurable_add_const _, map_add_right_eq_self volume a⟩
    have hreflect : MeasurePreserving e volume volume := by
      convert hadd.comp hneg using 1
      funext x
      change a - x = -x + a
      ring
    have := hreflect.integrable_comp_of_integrable hbase
    simpa [Function.comp_def, f, a, e] using this
  have hprod := Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ)) hf
  have hEq (ξ : Fin d → ℝ) :
      (∏ i, f i (ξ i)) =
        mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
          ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ := by
    rw [tensorCubeCutoffFourierKernel_eq_prod]
    simp [f, mixedWeight, scalarCubeCutoffFourierKernel_eq_schwartzFourier,
      Finset.prod_mul_distrib, Complex.norm_prod]
  exact hprod.congr (Filter.Eventually.of_forall fun ξ => hEq ξ)

/-- The weighted kernel itself is integrable: moderation bounds it by a fixed
multiple of the tensor Schwartz majorant. -/
theorem periodEightSchurKernel_integrable {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) (k : Fin d → ℤ) :
    Integrable (fun ξ : Fin d → ℝ => periodEightSchurKernel r k ξ)
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  let M : (Fin d → ℝ) → ℝ := fun ξ =>
    mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
      ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖
  let C : ℝ := (2 : ℝ) ^ (r * d / 2)
  have hM : Integrable M (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    simpa [M] using periodEightSchurMajorant_integrable r hr N hrN k
  have hmeas : AEStronglyMeasurable (fun ξ => periodEightSchurKernel r k ξ)
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    have hweight : Measurable (fun ξ : Fin d → ℝ => mixedWeight r ξ) := by
      unfold mixedWeight
      fun_prop
    have hratio : Measurable (fun ξ : Fin d → ℝ =>
        Real.sqrt (mixedWeight r (fun i => (k i : ℝ) / 8) / mixedWeight r ξ)) := by
      exact (measurable_const.div hweight).sqrt
    have hkernelProd : Measurable (fun ξ : Fin d → ℝ =>
        ‖∏ i, scalarCubeCutoffFourierKernel ((k i : ℝ) / 8) (ξ i)‖) := by
      simp_rw [scalarCubeCutoffFourierKernel_eq_schwartzFourier]
      fun_prop
    have hkernel : Measurable (fun ξ : Fin d → ℝ =>
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) := by
      convert hkernelProd using 1
      funext ξ
      rw [tensorCubeCutoffFourierKernel_eq_prod]
    change AEStronglyMeasurable
      (fun ξ => (Real.sqrt (mixedWeight r (fun i => (k i : ℝ) / 8) /
        mixedWeight r ξ)) * ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) _
    exact (hratio.mul hkernel).aestronglyMeasurable
  apply Integrable.mono' (hM.const_mul C) hmeas
  filter_upwards with ξ
  have hk : 0 ≤ periodEightSchurKernel r k ξ := by
    simp only [periodEightSchurKernel]
    positivity
  have hm : 0 ≤ M ξ := by
    dsimp [M]
    exact mul_nonneg (mixedWeight_pos _ _).le (norm_nonneg _)
  have hle : periodEightSchurKernel r k ξ ≤ C * M ξ := by
    simpa [C, M, mul_assoc] using periodEightSchurKernel_le r hr k ξ
  simpa [Real.norm_of_nonneg hk, Real.norm_of_nonneg (mul_nonneg (by positivity) hm)]
    using hle

/-- Uniform pointwise boundedness of a period-eight Schur kernel. This follows
from the point-evaluation seminorm bound for the integer-weighted Schwartz
cutoff, and will supply the L∞ factor in the L² Schur application. -/
theorem periodEightSchurKernel_uniform_bound {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) (k : Fin d → ℤ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ξ, periodEightSchurKernel r k ξ ≤ D := by
  let Q : ℝ := (SchwartzMap.seminorm ℂ 0 0)
    (integerWeightedCubeCutoffFourierSchwartz N)
  let C : ℝ := (2 : ℝ) ^ (r * d / 2)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact le_trans (norm_nonneg (integerWeightedCubeCutoffFourierSchwartz N 0))
      (SchwartzMap.norm_le_seminorm ℂ (integerWeightedCubeCutoffFourierSchwartz N) 0)
  have hscalar (x : ℝ) :
      (1 + x ^ 2) ^ (r / 2) *
        ‖cubeSpatialCutoffFourierSchwartz x‖ ≤ Q := by
    have hle := besselWeightedCutoffKernel_le_integerWeighted (r / 2) N hrN x
    have hnorm := SchwartzMap.norm_le_seminorm ℂ
      (integerWeightedCubeCutoffFourierSchwartz N) x
    exact hle.trans (by simpa [Q] using hnorm)
  refine ⟨C * Q ^ d, mul_nonneg (by positivity) (pow_nonneg hQ _), ?_⟩
  intro ξ
  have hfactor :
      mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ =
        ∏ i : Fin d, ((1 + ((k i : ℝ) / 8 - ξ i) ^ 2) ^ (r / 2) *
          ‖cubeSpatialCutoffFourierSchwartz ((k i : ℝ) / 8 - ξ i)‖) := by
    rw [tensorCubeCutoffFourierKernel_eq_prod]
    simp [mixedWeight, scalarCubeCutoffFourierKernel_eq_schwartzFourier,
      Finset.prod_mul_distrib]
  have hmajor :
      mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ ≤ Q ^ d := by
    rw [hfactor]
    calc
      _ ≤ ∏ _i : Fin d, Q := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
        · intro i hi
          exact hscalar _
      _ = Q ^ d := by simp
  calc
    periodEightSchurKernel r k ξ ≤ C *
        (mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
          ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) := by
            simpa [C, mul_assoc] using periodEightSchurKernel_le r hr k ξ
    _ ≤ C * Q ^ d := mul_le_mul_of_nonneg_left hmajor (by positivity)

/-- Every actual period-eight Schur kernel has an L² square root, by the
already-proved row integrability. -/
theorem periodEightSchurKernel_sqrt_memLp_two {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) (k : Fin d → ℤ) :
    MemLp (fun ξ => Real.sqrt (periodEightSchurKernel r k ξ)) 2
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  let μ := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  let s : (Fin d → ℝ) → ℝ := fun ξ => Real.sqrt (periodEightSchurKernel r k ξ)
  have hK := periodEightSchurKernel_integrable r hr N hrN k
  have hs : AEStronglyMeasurable s μ := by
    dsimp [s, μ]
    exact Real.continuous_sqrt.measurable.aestronglyMeasurable.comp_aemeasurable
      hK.aestronglyMeasurable.aemeasurable
  have hKone : MemLp (fun ξ => periodEightSchurKernel r k ξ) 1 μ :=
    memLp_one_iff_integrable.mpr hK
  have hpow : Integrable (fun ξ => ‖s ξ‖ ^ (2 : ℝ)) μ := by
    have heq : (fun ξ => ‖s ξ‖ ^ (2 : ℝ)) =
        fun ξ => periodEightSchurKernel r k ξ := by
      funext ξ
      have hnonneg : 0 ≤ periodEightSchurKernel r k ξ := by
        simp only [periodEightSchurKernel]
        positivity
      simp [s, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]
    rw [heq]
    exact hK
  have h := (integrable_norm_rpow_iff hs (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp hpow
  simpa [s, μ] using h

/-- A source profile in L² automatically meets both kernel-root conditions of
the sampled Schur estimate: row integrability gives the L² root, while the
pointwise Schwartz seminorm bound gives an L∞ root for multiplication. -/
theorem periodEightSchurKernel_source_conditions {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N)
    (f : (Fin d → ℝ) → ℝ)
    (hf : MemLp f 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)))
    (k : Fin d → ℤ) :
    MemLp (fun ξ => Real.sqrt (periodEightSchurKernel r k ξ)) 2
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) ∧
    MemLp (fun ξ => f ξ * Real.sqrt (periodEightSchurKernel r k ξ)) 2
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  let μ := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  let s : (Fin d → ℝ) → ℝ := fun ξ => Real.sqrt (periodEightSchurKernel r k ξ)
  have hs2 := periodEightSchurKernel_sqrt_memLp_two r hr N hrN k
  obtain ⟨D, hD, hDk⟩ := periodEightSchurKernel_uniform_bound r hr N hrN k
  have hsmeas : AEStronglyMeasurable s μ := by
    have hK := periodEightSchurKernel_integrable r hr N hrN k
    dsimp [s, μ]
    exact Real.continuous_sqrt.measurable.aestronglyMeasurable.comp_aemeasurable
      hK.aestronglyMeasurable.aemeasurable
  have hmul' : MemLp (fun ξ => f ξ * s ξ) 2 μ := by
    apply hf.of_le_mul (hf.aestronglyMeasurable.mul hsmeas) (c := Real.sqrt D)
    filter_upwards with ξ
    have hsBound : s ξ ≤ Real.sqrt D := Real.sqrt_le_sqrt (hDk ξ)
    have hsPos : 0 ≤ s ξ := Real.sqrt_nonneg _
    calc
      ‖f ξ * s ξ‖ = ‖f ξ‖ * s ξ := by rw [norm_mul, Real.norm_of_nonneg hsPos]
      _ ≤ ‖f ξ‖ * Real.sqrt D := mul_le_mul_of_nonneg_left hsBound (norm_nonneg _)
      _ = Real.sqrt D * ‖f ξ‖ := by ring
  exact ⟨by simpa [s, μ] using hs2, by simpa [μ] using hmul'⟩

/-- Uniform continuous row mass of the actual weighted period-eight kernel.
Together with `periodEightSchurKernel_finite_column_bound`, this is the two
mass input for the continuous-to-discrete weighted Schur estimate. -/
theorem periodEightSchurKernel_row_integral_bound {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k : Fin d → ℤ,
      ∫ ξ : Fin d → ℝ, periodEightSchurKernel r k ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) ≤ A := by
  obtain ⟨A₀, hA₀, hA₀bound⟩ :=
    tensorPeriodEightBesselKernel_row_integral_bound (d := d) (r := r) hr N hrN
  let C : ℝ := (2 : ℝ) ^ (r * d / 2)
  refine ⟨C * A₀, mul_nonneg (by positivity) hA₀, ?_⟩
  intro k
  have hKint := periodEightSchurKernel_integrable r hr N hrN k
  have hM := periodEightSchurMajorant_integrable r hr N hrN k
  have hpoint (ξ : Fin d → ℝ) : periodEightSchurKernel r k ξ ≤
      C * (mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) := by
    simpa [C, mul_assoc] using periodEightSchurKernel_le r hr k ξ
  calc
    ∫ ξ, periodEightSchurKernel r k ξ ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) ≤
        ∫ ξ, C * (mixedWeight (r / 2) (fun i => (k i : ℝ) / 8 - ξ i) *
          ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖)
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
            apply integral_mono hKint (hM.const_mul C)
            exact hpoint
    _ = C * ∫ ξ, mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
            ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
            rw [integral_const_mul]
    _ ≤ C * A₀ := by
          apply mul_le_mul_of_nonneg_left (hA₀bound k) (by positivity)

/-- The concrete period-eight Matérn cutoff kernel satisfies the continuous
Schur estimate on every finite frequency set. The remaining source-profile
requirements are stated as `MemLp` premises so callers can discharge them
from a specific raw spectral-energy theorem without hiding a source-law
identification inside this analytic lemma. -/
theorem periodEightSchur_sampled_l2_bound {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (S : Finset (Fin d → ℤ)) (f : (Fin d → ℝ) → ℝ)
        (hf : MemLp f 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)))
        (hf_nonneg : 0 ≤ᵐ[Measure.pi fun _ : Fin d => (volume : Measure ℝ)] f),
      ∑ k : {k : Fin d → ℤ // k ∈ S},
        (∫ ξ, f ξ * periodEightSchurKernel r k.1 ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) ^ 2 ≤
        A * B * ∫ ξ, f ξ ^ 2
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
  obtain ⟨A, hA, hrow⟩ := periodEightSchurKernel_row_integral_bound r hr N hrN
  obtain ⟨B, hB, hcol⟩ := periodEightSchurKernel_finite_column_bound r hr N hrN
  refine ⟨A, B, hA, hB, ?_⟩
  intro S f hf hf_nonneg
  let I := {k : Fin d → ℤ // k ∈ S}
  let K : I → (Fin d → ℝ) → ℝ := fun k ξ => periodEightSchurKernel r k.1 ξ
  have hK : ∀ k ξ, 0 ≤ K k ξ := by
    intro k ξ
    dsimp [K]
    simp only [periodEightSchurKernel]
    positivity
  have hrow' : ∀ k : I,
      ∫ ξ, K k ξ ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) ≤ A := by
    intro k
    exact hrow k.1
  have hcol' : ∀ ξ, ∑ k : I, K k ξ ≤ B := by
    intro ξ
    calc
      ∑ k : I, K k ξ =
          ∑ k ∈ S, periodEightSchurKernel r k ξ := by
            exact (Finset.sum_subtype S (fun _ => Iff.rfl)
              (fun k => periodEightSchurKernel r k ξ)).symm
      _ ≤ B := hcol S ξ
  have hroot : ∀ k : I,
      MemLp (fun ξ => Real.sqrt (periodEightSchurKernel r k.1 ξ))
        2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    intro k
    exact (periodEightSchurKernel_source_conditions r hr N hrN f hf k.1).1
  have hweighted : ∀ k : I,
      MemLp (fun ξ => f ξ * Real.sqrt (periodEightSchurKernel r k.1 ξ))
        2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    intro k
    exact (periodEightSchurKernel_source_conditions r hr N hrN f hf k.1).2
  simpa only [K] using finiteIntegralSchur_l2_bound
    (μ := Measure.pi fun _ : Fin d => (volume : Measure ℝ))
    (K := K) (f := f) A B hK hf hf_nonneg hweighted hroot hrow' hcol' hA

/-- The actual product Matérn raw spectral source produces the L² profile
needed by the sampled Schur bound. The proof transfers integrability of the
source-side energy through the product spectral with-density identity; the
normalizing constants remain explicit. -/
theorem rawTensorMaternProfile_memLp_two {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    MemLp (fun ξ : Fin d → ℝ =>
      Real.sqrt (mixedWeight (h + 1/2) ξ) *
        ‖rawTensorFourierAmplitude κ h g ξ‖) 2
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  let μ := Measure.pi (fun i => spectralMeasure (κ i) h)
  let volPi := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  let C : ℝ := ∏ i : Fin d,
    Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2))
  let G : (Fin d → ℝ) → ℝ := fun ξ =>
    tensorMaternSourceEnergyWeight κ h ξ * ‖g ξ‖ ^ 2
  let F : (Fin d → ℝ) → ℝ := fun ξ =>
    (∏ i, besselPrecisionWeight (h + 1/2) (ξ i)) *
      ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2
  have hgInt : Integrable (fun ξ => ‖g ξ‖ ^ 2) μ :=
    (Lp.memLp g).integrable_norm_pow (p := 2) (by norm_num : (2 : ℕ) ≠ 0)
  have hcoord (i : Fin d) (x : ℝ) :
      besselPrecisionWeight (h + 1/2) x * density (κ i) h x ≤
        Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2)) := by
    exact besselWeight_mul_density_le (κ i) h x (hκ i) hh
  have hweight (ξ : Fin d → ℝ) : tensorMaternSourceEnergyWeight κ h ξ ≤ C := by
    dsimp [tensorMaternSourceEnergyWeight, C]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact mul_nonneg
        (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
        (density_pos (κ i) h (ξ i) (hκ i)).le
    · intro i hi
      exact hcoord i (ξ i)
  have hG : Integrable G μ := by
    have hB : Integrable (fun ξ => C * ‖g ξ‖ ^ 2) μ := hgInt.const_mul C
    have hmeas : AEStronglyMeasurable G μ := by
      have hweightMeas : Measurable (tensorMaternSourceEnergyWeight κ h) := by
        unfold tensorMaternSourceEnergyWeight
        apply Finset.measurable_prod
        intro i hi
        have hd : Continuous (density (κ i) h) := by
          apply continuous_iff_continuousAt.mpr
          intro x
          unfold density
          have hb : ContinuousAt (fun y : ℝ => (κ i) ^ 2 + y ^ 2) x := by fun_prop
          have hbase : 0 < (κ i) ^ 2 + x ^ 2 := by
            have hki := hκ i
            nlinarith [sq_nonneg x]
          exact hb.rpow_const (Or.inl (ne_of_gt hbase))
        have hw : Continuous (besselPrecisionWeight (h + 1/2)) := by
          unfold besselPrecisionWeight
          fun_prop (disch := positivity)
        exact ((hw.mul hd).measurable.comp (measurable_pi_apply i))
      exact hweightMeas.aestronglyMeasurable.mul hgInt.aestronglyMeasurable
    apply Integrable.mono' hB hmeas
    filter_upwards with ξ
    have hGpos : 0 ≤ G ξ := by
      dsimp [G, tensorMaternSourceEnergyWeight]
      exact mul_nonneg
        (Finset.prod_nonneg fun i hi => mul_nonneg
          (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
          (density_pos (κ i) h (ξ i) (hκ i)).le)
        (sq_nonneg _)
    have hBpos : 0 ≤ C * ‖g ξ‖ ^ 2 := mul_nonneg (by dsimp [C]; positivity)
      (sq_nonneg _)
    simpa only [Real.norm_of_nonneg hGpos, Real.norm_of_nonneg hBpos] using
      (mul_le_mul_of_nonneg_right (hweight ξ) (sq_nonneg (‖g ξ‖)))
  have hμ : μ = volPi.withDensity (tensorDensity κ h) :=
    pi_spectralMeasure_eq_withDensity κ h hκ hh
  have hDmeas : Measurable (tensorDensity κ h) := by
    unfold tensorDensity
    apply Finset.measurable_prod
    intro i hi
    have hd : Continuous (density (κ i) h) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      unfold density
      have hb : ContinuousAt (fun y : ℝ => (κ i) ^ 2 + y ^ 2) x := by fun_prop
      have hbase : 0 < (κ i) ^ 2 + x ^ 2 := by
        have hk := hκ i
        nlinarith [sq_nonneg x]
      exact hb.rpow_const (Or.inl (ne_of_gt hbase))
    exact ((hd.measurable.comp (measurable_pi_apply i)).ennreal_ofReal)
  have hDfinite : ∀ᵐ ξ ∂volPi, tensorDensity κ h ξ < ⊤ := by
    filter_upwards with ξ
    unfold tensorDensity
    exact ENNReal.prod_lt_top fun i hi => ENNReal.ofReal_lt_top
  have hGwith : Integrable G (volPi.withDensity (tensorDensity κ h)) := by
    rw [← hμ]
    exact hG
  have htransfer : Integrable (fun ξ => G ξ * (tensorDensity κ h ξ).toReal) volPi :=
    (integrable_withDensity_iff hDmeas hDfinite).mp hGwith
  have hpoint (ξ : Fin d → ℝ) :
      F ξ = G ξ * (tensorDensity κ h ξ).toReal := by
    have hρ (i : Fin d) : 0 < density (κ i) h (ξ i) := density_pos (κ i) h (ξ i) (hκ i)
    have htoReal (i : Fin d) :
        (ENNReal.ofReal (density (κ i) h (ξ i))).toReal = density (κ i) h (ξ i) :=
      ENNReal.toReal_ofReal (hρ i).le
    have hprodρ : 0 ≤ ∏ i : Fin d, density (κ i) h (ξ i) :=
      Finset.prod_nonneg fun i hi => (hρ i).le
    simp only [F, G, tensorDensity, ENNReal.toReal_prod, htoReal,
      rawTensorFourierAmplitude, ← Complex.ofReal_prod,
      Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hprodρ]
    rw [tensorMaternSourceEnergyWeight, Finset.prod_mul_distrib]
    ring
  have hF : Integrable F volPi := by
    apply htransfer.congr
    exact Filter.Eventually.of_forall fun ξ => (hpoint ξ).symm
  have hprofileMeas : AEStronglyMeasurable
      (fun ξ : Fin d → ℝ => Real.sqrt (mixedWeight (h + 1/2) ξ) *
        ‖rawTensorFourierAmplitude κ h g ξ‖) volPi := by
    have hA := rawTensorFourierAmplitude_integrable κ h hκ hh g
    have hweightMeas : Measurable (fun ξ : Fin d → ℝ => mixedWeight (h + 1/2) ξ) := by
      unfold mixedWeight
      fun_prop
    have hAmeas := hA.aestronglyMeasurable.norm
    have hsMeas : AEStronglyMeasurable
        (fun ξ : Fin d → ℝ => Real.sqrt (mixedWeight (h + 1/2) ξ)) volPi :=
      (Real.continuous_sqrt.measurable.comp hweightMeas).aestronglyMeasurable
    exact hsMeas.mul hAmeas
  have hprofileSq : Integrable
      (fun ξ : Fin d → ℝ => ‖Real.sqrt (mixedWeight (h + 1/2) ξ) *
        ‖rawTensorFourierAmplitude κ h g ξ‖‖ ^ (2 : ℝ)) volPi := by
    have heq : (fun ξ : Fin d → ℝ => ‖Real.sqrt (mixedWeight (h + 1/2) ξ) *
        ‖rawTensorFourierAmplitude κ h g ξ‖‖ ^ (2 : ℝ)) = F := by
      funext ξ
      have hw : 0 ≤ mixedWeight (h + 1/2) ξ := (mixedWeight_pos _ _).le
      calc
        ‖Real.sqrt (mixedWeight (h + 1/2) ξ) *
          ‖rawTensorFourierAmplitude κ h g ξ‖‖ ^ (2 : ℝ) =
            mixedWeight (h + 1/2) ξ *
              ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2 := by
                rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
                  (norm_nonneg _)), Real.mul_rpow
                    (x := Real.sqrt (mixedWeight (h + 1/2) ξ))
                    (y := ‖rawTensorFourierAmplitude κ h g ξ‖)
                    (z := (2 : ℝ)) (Real.sqrt_nonneg _)
                    (norm_nonneg _), Real.rpow_two, Real.sq_sqrt hw]
                rw [Real.rpow_two]
        _ = F ξ := by
              dsimp [F]
              simp [mixedWeight, besselPrecisionWeight]
    rw [heq]
    exact hF
  have hmem := (integrable_norm_rpow_iff hprofileMeas
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp hprofileSq
  simpa using hmem

/-- Each weighted period-eight Fourier coefficient of the cutoff raw source is
dominated by its Schur pairing with the weighted source profile. This is the
actual coefficient-to-Schur bridge; periodization contributes the separate
normalizing factor `8⁻ᵈ`. -/
theorem rawTensorCutoffCoefficient_le_schur {d : ℕ} (r : ℝ)
    (hr : 0 ≤ r) (k : Fin d → ℤ) (A : (Fin d → ℝ) → ℂ)
    (hA : (Fin d → ℝ) → ℝ) (hhA : ∀ ξ, hA ξ = ‖A ξ‖) :
    Real.sqrt (mixedWeight r (fun i => (k i : ℝ) / 8)) *
      ‖∫ ξ, tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ * A ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖ ≤
      ∫ ξ, hA ξ * Real.sqrt (mixedWeight r ξ) *
        periodEightSchurKernel r k ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
  let wk := mixedWeight r (fun i => (k i : ℝ) / 8)
  have hwk : 0 < wk := mixedWeight_pos r _
  calc
    Real.sqrt wk *
        ‖∫ ξ, tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ * A ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖ ≤
        Real.sqrt wk *
          ∫ ξ, ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ * A ξ‖
            ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
              exact norm_integral_le_integral_norm _
    _ = ∫ ξ, Real.sqrt wk *
          (‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ * hA ξ)
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with ξ
            rw [norm_mul, hhA]
    _ = ∫ ξ, periodEightSchurKernel r k ξ *
          (hA ξ * Real.sqrt (mixedWeight r ξ))
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
            apply integral_congr_ae
            filter_upwards with ξ
            have hwξ : 0 < mixedWeight r ξ := mixedWeight_pos r ξ
            have hsqrtξ : 0 < Real.sqrt (mixedWeight r ξ) := Real.sqrt_pos.2 hwξ
            have hratio := Real.sqrt_div (le_of_lt hwk) (mixedWeight r ξ)
            unfold periodEightSchurKernel
            dsimp [wk]
            rw [hratio]
            field_simp
            <;> ring
    _ = ∫ ξ, hA ξ * Real.sqrt (mixedWeight r ξ) *
          periodEightSchurKernel r k ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
            apply integral_congr_ae
            filter_upwards with ξ
            ring

/-- Finite weighted Fourier-coefficient energy bound for the actual raw
Matérn spectral source after the spatial cutoff. This is the concrete
continuous-frequency Schur output that can feed a period-eight periodization;
the bound covers the unnormalized Fourier integral, so a torus coefficient
of the periodization contributes the explicit factor `8⁻ᵈ`. -/
theorem rawTensorMatern_cutoffCoefficient_energy {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (N : ℕ) (hN : (h + 1/2) / 2 ≤ N) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (g : ComplexProductL2 κ h) (S : Finset (Fin d → ℤ)),
      ∑ k : {k : Fin d → ℤ // k ∈ S},
        (Real.sqrt (mixedWeight (h + 1/2)
          (fun i => (k.1 i : ℝ) / 8)) *
          ‖∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k.1 i : ℝ) / 8) ξ *
            rawTensorFourierAmplitude κ h g ξ
            ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖) ^ 2 ≤
        A * B * ∫ ξ, (Real.sqrt (mixedWeight (h + 1/2) ξ) *
          ‖rawTensorFourierAmplitude κ h g ξ‖) ^ 2
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
  obtain ⟨A, B, hA, hB, hSchurAll⟩ :=
    periodEightSchur_sampled_l2_bound (h + 1/2) (by linarith) N hN
  refine ⟨A, B, hA, hB, ?_⟩
  intro g S
  let f : (Fin d → ℝ) → ℝ := fun ξ =>
    Real.sqrt (mixedWeight (h + 1/2) ξ) *
      ‖rawTensorFourierAmplitude κ h g ξ‖
  have hf : MemLp f 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    simpa [f] using rawTensorMaternProfile_memLp_two κ h hκ hh g
  have hfnn : 0 ≤ᵐ[Measure.pi fun _ : Fin d => (volume : Measure ℝ)] f := by
    filter_upwards with ξ
    dsimp [f]
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hSchur := hSchurAll S f hf hfnn
  let I := {k : Fin d → ℤ // k ∈ S}
  have hterm (k : I) :
      (Real.sqrt (mixedWeight (h + 1/2)
        (fun i => (k.1 i : ℝ) / 8)) *
        ‖∫ ξ, tensorCubeCutoffFourierKernel
          (fun i => (k.1 i : ℝ) / 8) ξ *
          rawTensorFourierAmplitude κ h g ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖) ^ 2 ≤
      (∫ ξ, f ξ * periodEightSchurKernel (h + 1/2) k.1 ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) ^ 2 := by
    have hcoeff := rawTensorCutoffCoefficient_le_schur (h + 1/2)
      (by linarith) k.1 (rawTensorFourierAmplitude κ h g)
      (fun ξ => ‖rawTensorFourierAmplitude κ h g ξ‖) (fun _ => rfl)
    have hpair_nonneg : 0 ≤ ∫ ξ, f ξ * periodEightSchurKernel
        (h + 1/2) k.1 ξ ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
      apply integral_nonneg
      intro ξ
      exact mul_nonneg (by positivity)
        (by simp [periodEightSchurKernel]; positivity)
    have hcoeff_nonneg : 0 ≤ Real.sqrt (mixedWeight (h + 1/2)
        (fun i => (k.1 i : ℝ) / 8)) *
        ‖∫ ξ, tensorCubeCutoffFourierKernel
          (fun i => (k.1 i : ℝ) / 8) ξ *
          rawTensorFourierAmplitude κ h g ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖ := by positivity
    apply (sq_le_sq₀ hcoeff_nonneg hpair_nonneg).2
    simpa [f, mul_assoc, mul_comm, mul_left_comm] using hcoeff
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k hk => hterm k)
  calc
    _ ≤ ∑ k : I,
        (∫ ξ, f ξ * periodEightSchurKernel (h + 1/2) k.1 ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) ^ 2 := hsum
    _ ≤ A * B * ∫ ξ, f ξ ^ 2
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
          calc
            _ = ∑ k ∈ S.attach,
                (∫ ξ, f ξ * periodEightSchurKernel (h + 1/2) (↑k)
                  ξ ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) ^ 2 := by
                    calc
                      _ = ∑ k ∈ S,
                          (∫ ξ, f ξ * periodEightSchurKernel (h + 1/2) k
                            ξ ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) ^ 2 :=
                              Finset.sum_coe_sort S _
                      _ = _ := (Finset.sum_attach S _).symm
            _ ≤ _ := by simpa [f] using hSchur
    _ = A * B * ∫ ξ, (Real.sqrt (mixedWeight (h + 1/2) ξ) *
        ‖rawTensorFourierAmplitude κ h g ξ‖) ^ 2
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by rfl

/-- The finite cutoff coefficient energy is bounded by the true Matérn
product spectral source norm, uniformly over all sources and frequency sets.
All constants depend only on the fixed spectral parameters, dimension, and
the selected Schwartz weight exponent. -/
theorem rawTensorMatern_cutoffCoefficient_energy_le_normSq {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (N : ℕ) (hN : (h + 1/2) / 2 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ComplexProductL2 κ h)
      (S : Finset (Fin d → ℤ)),
      ∑ k : {k : Fin d → ℤ // k ∈ S},
        (Real.sqrt (mixedWeight (h + 1/2)
          (fun i => (k.1 i : ℝ) / 8)) *
          ‖∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k.1 i : ℝ) / 8) ξ *
            rawTensorFourierAmplitude κ h g ξ
            ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖) ^ 2 ≤
        C * ‖g‖ ^ 2 := by
  obtain ⟨A, B, hA, hB, hCoeff⟩ :=
    rawTensorMatern_cutoffCoefficient_energy κ h hκ hh N hN
  let D : ℝ := ∏ i : Fin d,
    Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2))
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.prod_nonneg fun i hi => le_of_lt
      (Real.rpow_pos_of_pos (lt_min (by norm_num) (sq_pos_of_pos (hκ i))) _)
  have hC : 0 ≤ A * B * D := mul_nonneg (mul_nonneg hA hB) hD
  refine ⟨A * B * D, hC, ?_⟩
  intro g S
  have hEnergy := rawTensorFourierAmplitude_energy_le_normSq κ h hκ hh g
  have hprofileEq :
      ∫ ξ, (Real.sqrt (mixedWeight (h + 1/2) ξ) *
          ‖rawTensorFourierAmplitude κ h g ξ‖) ^ 2
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) =
      ∫ ξ, (∏ i, besselPrecisionWeight (h + 1/2) (ξ i)) *
          ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
          apply integral_congr_ae
          filter_upwards with ξ
          have hw : 0 ≤ mixedWeight (h + 1/2) ξ := (mixedWeight_pos _ _).le
          calc
            (Real.sqrt (mixedWeight (h + 1/2) ξ) *
              ‖rawTensorFourierAmplitude κ h g ξ‖) ^ 2 =
                mixedWeight (h + 1/2) ξ *
                  ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2 := by
                    rw [mul_pow, Real.sq_sqrt hw]
            _ = (∏ i, besselPrecisionWeight (h + 1/2) (ξ i)) *
                ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2 := by
                  simp [mixedWeight, besselPrecisionWeight]
  have hcoeff := hCoeff g S
  calc
    _ ≤ A * B * ∫ ξ, (Real.sqrt (mixedWeight (h + 1/2) ξ) *
          ‖rawTensorFourierAmplitude κ h g ξ‖) ^ 2
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := hcoeff
    _ = A * B * ∫ ξ, (∏ i, besselPrecisionWeight (h + 1/2) (ξ i)) *
          ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by rw [hprofileEq]
    _ ≤ A * B * (D * ‖g‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hA hB)
    _ = A * B * D * ‖g‖ ^ 2 := by ring

/-- The inverse-Fourier field generated by every true Matérn product spectral
source is a continuous function on all of Euclidean space. Dominated
convergence uses the already-proved L¹ property of the raw spectral
amplitude, so the cutoff and torus-lift steps apply to the actual feature
output. -/
theorem rawTensorFourierIntegral_continuous {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    Continuous (fun t : Fin d → ℝ =>
      ∫ ξ, star (complexSheetPhase t ξ) * rawTensorFourierAmplitude κ h g ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) := by
  let A : (Fin d → ℝ) → ℂ := rawTensorFourierAmplitude κ h g
  let μ := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  have hA : Integrable A μ := by
    simpa [A, μ] using rawTensorFourierAmplitude_integrable κ h hκ hh g
  apply continuous_of_dominated
    (F := fun t ξ => star (complexSheetPhase t ξ) * A ξ)
    (bound := fun ξ => ‖A ξ‖)
  · intro t
    exact (by
      have hp : Measurable (fun ξ : Fin d → ℝ => complexSheetPhase t ξ) := by
        unfold complexSheetPhase complexPhase
        fun_prop
      exact hp.aestronglyMeasurable.star.mul hA.aestronglyMeasurable)
  · intro t
    filter_upwards with ξ
    rw [norm_mul, norm_star, complexSheetPhase_norm, one_mul]
  · exact hA.norm
  · filter_upwards with ξ
    unfold complexSheetPhase complexPhase
    fun_prop

/-- The real normalized feature output obtained from an arbitrary product
spectral source, written on all of Euclidean space by its inverse-Fourier
integral. -/
def rawTensorMaternFeatureOutput {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (g : ComplexProductL2 κ h)
    (t : Fin d → ℝ) : ℝ :=
  complexFeatureScale κ h hκ hh *
    (∫ ξ, star (complexSheetPhase t ξ) * rawTensorFourierAmplitude κ h g ξ
      ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).re

/-- The Euclidean representative of the raw Matérn feature output is
continuous, including outside the unit cube where the spatial cutoff will be
applied. -/
theorem rawTensorMaternFeatureOutput_continuous {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    Continuous (rawTensorMaternFeatureOutput κ h hκ hh g) := by
  unfold rawTensorMaternFeatureOutput
  exact continuous_const.mul
    (Complex.continuous_re.comp (rawTensorFourierIntegral_continuous κ h hκ hh g))

/-- On the anchored cube, the Euclidean inverse-Fourier representative agrees
with the actual normalized complex Matérn feature operator. -/
theorem rawTensorMaternFeatureOutput_eq_featureOperator {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (t : HaarQuarter.BrownianCubeAnchor d) :
    rawTensorMaternFeatureOutput κ h hκ hh g t.val =
      AlignmentFractionalSheetRKHS.featureOperator
        (complexSheetFeature κ h hκ hh) g t := by
  simpa [rawTensorMaternFeatureOutput] using
    (complexSheetFeature_operator_eq_fourierIntegral κ h hκ hh g t).symm

/-- Real tensor cutoff on Euclidean space. -/
def tensorCubeSpatialCutoffReal {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∏ i, cubeSpatialCutoff (x i)

/-- The spatial cutoff is continuous and equals one on the data cube. -/
theorem tensorCubeSpatialCutoffReal_continuous {d : ℕ} :
    Continuous (tensorCubeSpatialCutoffReal (d := d)) := by
  unfold tensorCubeSpatialCutoffReal
  apply continuous_finset_prod
  intro i hi
  exact cubeSpatialCutoff_smooth.continuous.comp (continuous_apply i)

theorem tensorCubeSpatialCutoffReal_eq_one_on_cube {d : ℕ}
    (x : Fin d → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    tensorCubeSpatialCutoffReal x = 1 := by
  unfold tensorCubeSpatialCutoffReal
  apply Finset.prod_eq_one
  intro i hi
  have habs : |x i| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [(hx i).1], (hx i).2⟩
  simp [cubeSpatialCutoff, BrownianSharp.SmoothResolution.cutoff_eq_one habs]

/-- The actual normalized Matérn feature source after cutoff, as a continuous
real-valued Euclidean function. -/
def rawTensorMaternCutoffOutput {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) : C((Fin d → ℝ), ℝ) :=
  ⟨fun x => tensorCubeSpatialCutoffReal x *
      rawTensorMaternFeatureOutput κ h hκ hh g x,
    tensorCubeSpatialCutoffReal_continuous.mul
      (rawTensorMaternFeatureOutput_continuous κ h hκ hh g)⟩

/-- The Euclidean cutoff source vanishes when any coordinate leaves the
period-eight inner cube, so it is eligible for the actual continuous torus
periodization. -/
theorem rawTensorMaternCutoffOutput_vanishes_outside {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    ∀ x, (∃ i, x i ≤ -2 ∨ 2 ≤ x i) → rawTensorMaternCutoffOutput κ h hκ hh g x = 0 := by
  intro x hx
  obtain ⟨i, hi⟩ := hx
  apply mul_eq_zero_of_left
  unfold tensorCubeSpatialCutoffReal
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with hleft | hright
  · have habs : 2 ≤ |x i| := by rw [abs_of_nonpos (by linarith)]; linarith
    simp [cubeSpatialCutoff, BrownianSharp.SmoothResolution.cutoff_eq_zero habs]
  · have habs : 2 ≤ |x i| := by rw [abs_of_nonneg (by linarith)]; linarith
    simp [cubeSpatialCutoff, BrownianSharp.SmoothResolution.cutoff_eq_zero habs]

/-- Periodization of the actual continuous Matérn cutoff source. -/
def rawTensorMaternCutoffPeriodization {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) : C(UnitAddTorus (Fin d), ℝ) :=
  BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight
    (rawTensorMaternCutoffOutput κ h hκ hh g)
    (rawTensorMaternCutoffOutput_vanishes_outside κ h hκ hh g)

/-- Periodization preserves the actual normalized Matérn feature output on
the original unit cube. -/
theorem rawTensorMaternCutoffPeriodization_restrict {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (t : Fin d → ℝ)
    (ht : t ∈ Set.Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) :
    rawTensorMaternCutoffPeriodization κ h hκ hh g
      (BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus t) =
        AlignmentFractionalSheetRKHS.featureOperator
          (complexSheetFeature κ h hκ hh) g ⟨t, fun i => ⟨(Set.mem_Icc.mp ht).1 i,
            (Set.mem_Icc.mp ht).2 i⟩⟩ := by
  have htcoord : ∀ i, t i ∈ Set.Icc (0:ℝ) 1 := fun i =>
    ⟨(Set.mem_Icc.mp ht).1 i, (Set.mem_Icc.mp ht).2 i⟩
  rw [rawTensorMaternCutoffPeriodization,
    BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight_restrict
      (rawTensorMaternCutoffOutput κ h hκ hh g)
      (rawTensorMaternCutoffOutput_vanishes_outside κ h hκ hh g) t ht]
  simp only [rawTensorMaternCutoffOutput, ContinuousMap.coe_mk]
  rw [tensorCubeSpatialCutoffReal_eq_one_on_cube t htcoord]
  simpa using rawTensorMaternFeatureOutput_eq_featureOperator κ h hκ hh g ⟨t, htcoord⟩

/-- Complex inverse-Fourier representative before taking its real part. Keeping
this complex source is useful because the exact periodized Fourier coefficient
formula applies directly to it. -/
def rawTensorMaternComplexFeatureOutput {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (t : Fin d → ℝ) : ℂ :=
  (complexFeatureScale κ h hκ hh : ℂ) *
    ∫ ξ, star (complexSheetPhase t ξ) * rawTensorFourierAmplitude κ h g ξ
      ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))

theorem rawTensorMaternFeatureOutput_eq_complex_re {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (t : Fin d → ℝ) :
    rawTensorMaternFeatureOutput κ h hκ hh g t =
      (rawTensorMaternComplexFeatureOutput κ h hκ hh g t).re := by
  simp [rawTensorMaternFeatureOutput, rawTensorMaternComplexFeatureOutput,
    Complex.mul_re]

theorem rawTensorMaternComplexFeatureOutput_continuous {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    Continuous (rawTensorMaternComplexFeatureOutput κ h hκ hh g) := by
  unfold rawTensorMaternComplexFeatureOutput
  exact continuous_const.mul
    (rawTensorFourierIntegral_continuous κ h hκ hh g)

/-- Complex-valued cutoff source whose real part is the actual real Matérn
feature cutoff source. -/
def rawTensorMaternComplexCutoffOutput {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) : C((Fin d → ℝ),ℂ) :=
  ⟨fun x => (tensorCubeSpatialCutoffReal x : ℂ) *
      rawTensorMaternComplexFeatureOutput κ h hκ hh g x,
    (Complex.continuous_ofReal.comp (tensorCubeSpatialCutoffReal_continuous)).mul
      (rawTensorMaternComplexFeatureOutput_continuous κ h hκ hh g)⟩

theorem rawTensorMaternComplexCutoffOutput_re {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (x : Fin d → ℝ) :
    (rawTensorMaternComplexCutoffOutput κ h hκ hh g x).re =
      rawTensorMaternCutoffOutput κ h hκ hh g x := by
  simp [rawTensorMaternComplexCutoffOutput, rawTensorMaternCutoffOutput,
    rawTensorMaternFeatureOutput_eq_complex_re, Complex.mul_re]

theorem rawTensorMaternComplexCutoffOutput_vanishes_outside {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    ∀ x, (∃ i, x i ≤ -2 ∨ 2 ≤ x i) →
      rawTensorMaternComplexCutoffOutput κ h hκ hh g x = 0 := by
  intro x hx
  obtain ⟨i,hi⟩ := hx
  have hcut : tensorCubeSpatialCutoffReal x = 0 := by
    unfold tensorCubeSpatialCutoffReal
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hi with hleft | hright
    · have habs : 2 ≤ |x i| := by rw [abs_of_nonpos (by linarith)]; linarith
      simp [cubeSpatialCutoff, BrownianSharp.SmoothResolution.cutoff_eq_zero habs]
    · have habs : 2 ≤ |x i| := by rw [abs_of_nonneg (by linarith)]; linarith
      simp [cubeSpatialCutoff, BrownianSharp.SmoothResolution.cutoff_eq_zero habs]
  have hz := rawTensorMaternCutoffOutput_vanishes_outside κ h hκ hh g x ⟨i,hi⟩
  apply Complex.ext
  · simpa [rawTensorMaternComplexCutoffOutput_re] using hz
  · simp [rawTensorMaternComplexCutoffOutput, hcut]

def rawTensorMaternComplexCutoffPeriodization {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) : C(UnitAddTorus (Fin d),ℂ) :=
  BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight
    (rawTensorMaternComplexCutoffOutput κ h hκ hh g)
    (rawTensorMaternComplexCutoffOutput_vanishes_outside κ h hκ hh g)

/-- The actual real torus extension is the pointwise real part of the complex
periodization. Equality is checked on the genuine quotient image of the
fundamental cube, which is surjective. -/
theorem rawTensorMaternCutoffPeriodization_eq_complex_re {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (z : UnitAddTorus (Fin d)) :
    rawTensorMaternCutoffPeriodization κ h hκ hh g z =
      (rawTensorMaternComplexCutoffPeriodization κ h hκ hh g z).re := by
  obtain ⟨x,hx⟩ := BrownianSharp.AlignmentPaperCubePeriodization.cubeToTorus_surjective d z
  rw [← hx]
  change BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight
      (rawTensorMaternCutoffOutput κ h hκ hh g)
      (rawTensorMaternCutoffOutput_vanishes_outside κ h hκ hh g)
      (BrownianSharp.AlignmentPaperCubePeriodization.cubeToTorus d x) =
    (BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight
      (rawTensorMaternComplexCutoffOutput κ h hκ hh g)
      (rawTensorMaternComplexCutoffOutput_vanishes_outside κ h hκ hh g)
      (BrownianSharp.AlignmentPaperCubePeriodization.cubeToTorus d x)).re
  rw [BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight_on_fundamentalCube
    (rawTensorMaternCutoffOutput κ h hκ hh g)
    (rawTensorMaternCutoffOutput_vanishes_outside κ h hκ hh g) x]
  rw [BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight_on_fundamentalCube
    (rawTensorMaternComplexCutoffOutput κ h hκ hh g)
    (rawTensorMaternComplexCutoffOutput_vanishes_outside κ h hκ hh g) x]
  exact (rawTensorMaternComplexCutoffOutput_re κ h hκ hh g
    (fun i => 8*x.val i)).symm

theorem mFourier_neg_periodEight_eq_complexPhase {d : ℕ}
    (k : Fin d → ℤ) (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-k)
      (BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus t) =
      complexSheetPhase (fun i => (k i : ℝ) / 8) t := by
  simp only [UnitAddTorus.mFourier, Pi.neg_apply, ContinuousMap.coe_mk,
    BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus,
    fourier_coe_apply, complexSheetPhase, complexPhase]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  push_cast
  ring_nf

/-- Rescaling integer frequencies from the period-eight extension to the
unit torus costs only the fixed Bessel-weight factor `64^(r*d)`. -/
theorem mixedWeight_integer_le_eight_rescale {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (k : Fin d → ℤ) :
    mixedWeight r (fun i => (k i : ℝ)) ≤
      64 ^ (r * d) * mixedWeight r (fun i => (k i : ℝ) / 8) := by
  unfold mixedWeight
  calc
    (∏ i, (1 + (k i : ℝ) ^ 2) ^ r) ≤
        ∏ i, (64 ^ r * (1 + ((k i : ℝ) / 8) ^ 2) ^ r) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            positivity
          · intro i hi
            calc
              (1 + (k i : ℝ) ^ 2) ^ r ≤
                  (64 * (1 + ((k i : ℝ) / 8) ^ 2)) ^ r :=
                    Real.rpow_le_rpow (by positivity) (by
                      nlinarith [sq_nonneg ((k i : ℝ) / 8)]) hr
              _ = 64 ^ r * (1 + ((k i : ℝ) / 8) ^ 2) ^ r := by
                    rw [Real.mul_rpow (by norm_num) (by positivity)]
    _ = (∏ _i : Fin d, (64 : ℝ) ^ r) *
        ∏ i, (1 + ((k i : ℝ) / 8) ^ 2) ^ r := by
          rw [Finset.prod_mul_distrib]
    _ = 64 ^ (r * d) *
        ∏ i, (1 + ((k i : ℝ) / 8) ^ 2) ^ r := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 1
          calc
            (64 ^ r) ^ d = (64 ^ r) ^ (d : ℝ) := (Real.rpow_natCast _ _).symm
            _ = 64 ^ (r * (d : ℝ)) := by
              rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 64)]

theorem rawTensorMaternComplexCutoffPeriodization_fourierCoeff {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (rawTensorMaternComplexCutoffPeriodization κ h hκ hh g) k =
      ((8:ℝ)^d)⁻¹ • ((complexFeatureScale κ h hκ hh : ℂ) *
        ∫ ξ, tensorCubeCutoffFourierKernel
          (fun i => (k i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => (volume : Measure ℝ)
  let A : (Fin d → ℝ) → ℂ := rawTensorFourierAmplitude κ h g
  let χ : (Fin d → ℝ) → ℂ := tensorCubeSpatialCutoff
  let q : (Fin d → ℝ) → (Fin d → ℝ) → ℂ :=
    fun t ξ => cutoffFeaturePhase (fun i => (k i : ℝ) / 8) t ξ
  have hA : Integrable A μ := by
    simpa [A, μ] using rawTensorFourierAmplitude_integrable κ h hκ hh g
  have hχ : Integrable χ μ := by
    simpa [χ, μ] using tensorCubeSpatialCutoff_integrable
  have hq : Measurable (Function.uncurry q) := by
    dsimp [q]
    exact cutoffFeaturePhase_measurable _
  have hqn : ∀ t ξ, ‖q t ξ‖ = 1 := by
    intro t ξ
    exact cutoffFeaturePhase_norm _ _ _
  have hswap := normOne_product_integral_swap μ μ χ A q hχ hA hq hqn
  have hcut (t : Fin d → ℝ) :
      (tensorCubeSpatialCutoffReal t : ℂ) = tensorCubeSpatialCutoff t := by
    simp [tensorCubeSpatialCutoff, tensorCubeSpatialCutoffReal]
  have hphase (t : Fin d → ℝ) :
      UnitAddTorus.mFourier (-k)
        (BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus t) =
      complexSheetPhase (fun i => (k i : ℝ) / 8) t :=
    mFourier_neg_periodEight_eq_complexPhase k t
  have hrepr :
      (∫ t : Fin d → ℝ,
        UnitAddTorus.mFourier (-k)
          (BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus t) *
          rawTensorMaternComplexCutoffOutput κ h hκ hh g t ∂μ) =
      (complexFeatureScale κ h hκ hh : ℂ) *
        ∫ ξ, tensorCubeCutoffFourierKernel
          (fun i => (k i : ℝ) / 8) ξ * A ξ ∂μ := by
    calc
      _ = (complexFeatureScale κ h hκ hh : ℂ) *
          ∫ t, ∫ ξ, χ t * q t ξ * A ξ ∂μ ∂μ := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [] with t
            simp only [rawTensorMaternComplexCutoffOutput, ContinuousMap.coe_mk,
              rawTensorMaternComplexFeatureOutput, hphase, hcut, μ]
            dsimp [χ, q, A]
            calc
              _ = (complexFeatureScale κ h hκ hh : ℂ) *
                  ∫ ξ, tensorCubeSpatialCutoff t *
                    complexSheetPhase (fun i => (k i : ℝ) / 8) t *
                    (star (complexSheetPhase t ξ) *
                      rawTensorFourierAmplitude κ h g ξ) ∂μ := by
                    have hi := (integral_const_mul (μ := μ)
                      (tensorCubeSpatialCutoff t *
                        complexSheetPhase (fun i => (k i : ℝ) / 8) t)
                      (fun ξ => star (complexSheetPhase t ξ) *
                        rawTensorFourierAmplitude κ h g ξ)).symm
                    calc
                      _ = (complexFeatureScale κ h hκ hh : ℂ) *
                          (tensorCubeSpatialCutoff t *
                            (complexSheetPhase (fun i => (k i : ℝ) / 8) t *
                              ∫ ξ, star (complexSheetPhase t ξ) *
                                rawTensorFourierAmplitude κ h g ξ ∂μ)) := by
                        simp only [μ, starRingEnd_apply]
                        ring
                      _ = _ := by
                        simpa only [mul_assoc] using congrArg
                          (fun z : ℂ => (complexFeatureScale κ h hκ hh : ℂ) * z) hi
              _ = (complexFeatureScale κ h hκ hh : ℂ) *
                  ∫ ξ, tensorCubeSpatialCutoff t *
                    cutoffFeaturePhase (fun i => (k i : ℝ) / 8) t ξ *
                    rawTensorFourierAmplitude κ h g ξ ∂μ := by
                    congr 1
                    apply integral_congr_ae
                    filter_upwards [] with ξ
                    simp only [cutoffFeaturePhase]
                    ring
      _ = (complexFeatureScale κ h hκ hh : ℂ) *
          ∫ ξ, ∫ t, χ t * q t ξ * A ξ ∂μ ∂μ := by rw [hswap]
      _ = (complexFeatureScale κ h hκ hh : ℂ) *
          ∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k i : ℝ) / 8) ξ * A ξ ∂μ := by
            congr 1
            calc
              _ = ∫ t, ∫ ξ, χ t * q t ξ * A ξ ∂μ ∂μ := hswap.symm
              _ = _ := by
                simpa [μ, χ, q, A] using tensorCubeCutoff_coefficient_fubini A
                  (fun i => (k i : ℝ) / 8) hA
  calc
    _ = ((8:ℝ)^d)⁻¹ •
        ∫ t : Fin d → ℝ,
          UnitAddTorus.mFourier (-k)
            (BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus t) *
            rawTensorMaternComplexCutoffOutput κ h hκ hh g t ∂μ := by
          exact BrownianSharp.AlignmentPaperCubePeriodization.periodizePeriodEight_fourierCoeff
            (rawTensorMaternComplexCutoffOutput κ h hκ hh g)
            (rawTensorMaternComplexCutoffOutput_vanishes_outside κ h hκ hh g) k
    _ = ((8:ℝ)^d)⁻¹ •
        ((complexFeatureScale κ h hκ hh : ℂ) *
          ∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k i : ℝ) / 8) ξ * A ξ ∂μ) := by
          rw [hrepr]

/-- The exact Fourier coefficients of the true complex Matérn cutoff source
have finite weighted energy, uniformly over the spectral source. This is the
period-eight coefficient theorem combined with the proved kernel Schur bound
and the explicit integer-frequency rescaling. -/
theorem rawTensorMaternComplexCutoffPeriodization_weighted_energy {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (N : ℕ) (hN : (h + 1/2) / 2 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ComplexProductL2 κ h)
      (S : Finset (Fin d → ℤ)),
      ∑ k : {k : Fin d → ℤ // k ∈ S}, spectralWeight (h + 1/2) k.1 *
        ‖UnitAddTorus.mFourierCoeff
          (rawTensorMaternComplexCutoffPeriodization κ h hκ hh g) k.1‖^2 ≤
        C * ‖g‖^2 := by
  obtain ⟨C₀,hC₀,hbase⟩ := rawTensorMatern_cutoffCoefficient_energy_le_normSq
    κ h hκ hh N hN
  let r : ℝ := h + 1/2
  let D : ℝ := ((8:ℝ)^d)⁻¹ * complexFeatureScale κ h hκ hh
  let K : ℝ := 64 ^ (r * d)
  let C : ℝ := C₀ * D ^ 2 * K
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (inv_pos.mpr (by positivity))
      (complexFeatureScale_pos κ h hκ hh)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro g S
  have hsource := hbase g S
  have hterm (k : Fin d → ℤ) :
      spectralWeight r k *
        ‖UnitAddTorus.mFourierCoeff
          (rawTensorMaternComplexCutoffPeriodization κ h hκ hh g) k‖^2 ≤
      (D^2*K) *
        (Real.sqrt (mixedWeight r (fun i => (k i : ℝ) / 8)) *
          ‖∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
            ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖)^2 := by
    have hcoef := rawTensorMaternComplexCutoffPeriodization_fourierCoeff
      κ h hκ hh g k
    have hnorm :
        ‖UnitAddTorus.mFourierCoeff
          (rawTensorMaternComplexCutoffPeriodization κ h hκ hh g) k‖^2 =
        D^2 * ‖∫ ξ, tensorCubeCutoffFourierKernel
          (fun i => (k i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖^2 := by
      rw [hcoef, Complex.real_smul, norm_mul, norm_mul, Complex.norm_real]
      have hInv : 0 < ((8:ℝ)^d)⁻¹ := inv_pos.mpr (by positivity)
      rw [Complex.norm_real, Real.norm_of_nonneg hInv.le,
        Real.norm_of_nonneg (complexFeatureScale_pos κ h hκ hh).le]
      dsimp [D]
      ring
    rw [hcoef]
    rw [hcoef] at hnorm
    rw [hnorm]
    have hweight := mixedWeight_integer_le_eight_rescale r hr k
    have hscaled := mul_le_mul_of_nonneg_right hweight
      (mul_nonneg (sq_nonneg D)
        (sq_nonneg (‖∫ ξ, tensorCubeCutoffFourierKernel
          (fun i => (k i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖)))
    have hsqrt : (Real.sqrt (mixedWeight r (fun i => (k i : ℝ) / 8)) *
        ‖∫ ξ, tensorCubeCutoffFourierKernel
          (fun i => (k i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖)^2 =
        mixedWeight r (fun i => (k i : ℝ) / 8) *
          ‖∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
            ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖^2 := by
      rw [mul_pow, Real.sq_sqrt (mixedWeight_pos r _).le]
    rw [hsqrt]
    simpa [spectralWeight, mixedWeight, r, D, K, mul_assoc, mul_left_comm,
      mul_comm] using hscaled
  calc
    _ ≤ ∑ k : {k : Fin d → ℤ // k ∈ S}, (D^2*K) *
        (Real.sqrt (mixedWeight r (fun i => (k.1 i : ℝ) / 8)) *
          ‖∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k.1 i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
            ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖)^2 := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k.1
    _ = D^2*K * ∑ k : {k : Fin d → ℤ // k ∈ S},
        (Real.sqrt (mixedWeight r (fun i => (k.1 i : ℝ) / 8)) *
          ‖∫ ξ, tensorCubeCutoffFourierKernel
            (fun i => (k.1 i : ℝ) / 8) ξ * rawTensorFourierAmplitude κ h g ξ
            ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))‖)^2 := by
          rw [Finset.mul_sum]
    _ ≤ D^2*K * (C₀ * ‖g‖^2) := by
          exact mul_le_mul_of_nonneg_left hsource
            (mul_nonneg (sq_nonneg D) hK)
    _ = C * ‖g‖^2 := by dsimp [C]; ring

theorem mFourierCoeff_complex_smul {d : ℕ} (a : ℝ)
    (f : C(UnitAddTorus (Fin d),ℂ)) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff ((a:ℂ) • f) k =
      (a:ℂ) * UnitAddTorus.mFourierCoeff f k := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_smul, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  change UnitAddTorus.mFourier (-k) x * ((a:ℂ) * f x) = _
  ring

/-- The entire unit spectral-feature image, after period-eight cutoff and
restriction, lies in a fixed scalar multiple of the literal periodic
smooth-cutoff Sobolev-2 unit ball. -/
theorem rawTensorMaternCutoffPeriodization_exists_sobolev_scalar {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (N : ℕ) (hN : (h + 1/2) / 2 ≤ N) :
    ∃ A : ℝ, 0 < A ∧ ∀ g : ComplexProductL2 κ h, ‖g‖ ≤ 1 →
      BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall
        BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff
        2 (h+1/2)
        (A⁻¹ • rawTensorMaternCutoffPeriodization κ h hκ hh g) := by
  obtain ⟨C,hC,henergy⟩ := rawTensorMaternComplexCutoffPeriodization_weighted_energy
    κ h hκ hh N hN
  let r : ℝ := h + 1/2
  let M : ℝ := (2 * (4:ℝ)^r)^d
  let Q : ℝ := M * (2*C)
  let A : ℝ := Q + 1
  let a : ℝ := A⁻¹
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have ha : 0 < a := by dsimp [a]; exact inv_pos.mpr hA
  refine ⟨A,hA,?_⟩
  intro g hg
  let f := rawTensorMaternComplexCutoffPeriodization κ h hκ hh g
  let rf := rawTensorMaternCutoffPeriodization κ h hκ hh g
  let fa : C(UnitAddTorus (Fin d),ℂ) := (a:ℂ) • f
  let rfa : BrownianSharp.Torus.RealPeriodic d := a • rf
  have hfiniteScaled : ∀ S : Finset (Fin d → ℤ),
      ∑ k ∈ S, spectralWeight r k *
        ‖UnitAddTorus.mFourierCoeff fa k‖^2 ≤
          a^2 * (C * ‖g‖^2) := by
    intro S
    have hbase := henergy g S
    have hsum :
        (∑ k ∈ S, spectralWeight r k *
          ‖UnitAddTorus.mFourierCoeff f k‖^2) =
        (∑ k : {k : Fin d → ℤ // k ∈ S}, spectralWeight r k.1 *
          ‖UnitAddTorus.mFourierCoeff f k.1‖^2) := by
      exact Finset.sum_subtype S (fun _ => Iff.rfl) _
    rw [← hsum] at hbase
    calc
      _ = a^2 * ∑ k ∈ S, spectralWeight r k *
          ‖UnitAddTorus.mFourierCoeff f k‖^2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            rw [mFourierCoeff_complex_smul a f k]
            have haNorm : ‖(a:ℂ)‖ = a := by
              rw [Complex.norm_real, Real.norm_of_nonneg ha.le]
            rw [norm_mul, haNorm]
            ring
      _ ≤ a^2 * (C * ‖g‖^2) := by
            exact mul_le_mul_of_nonneg_left hbase (sq_nonneg a)
  have hw : ∀ k : Fin d → ℤ, 0 ≤ spectralWeight r k := by
    intro k
    unfold spectralWeight
    apply Finset.prod_nonneg
    intro i hi
    exact Real.rpow_nonneg (by positivity) _
  have heven : ∀ k : Fin d → ℤ, spectralWeight r (-k)=spectralWeight r k := by
    intro k
    simp [spectralWeight]
  have hreal : ∀ z : UnitAddTorus (Fin d), rfa z = (fa z).re := by
    intro z
    have hbaseReal := rawTensorMaternCutoffPeriodization_eq_complex_re κ h hκ hh g z
    change (a * rf z) = ((a:ℂ) * f z).re
    dsimp [rf, f]
    rw [hbaseReal, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hts := BrownianSharp.AlignmentPaperPeriodicRealPartEnergy.realPart_weighted_fourier_tsum_le
    fa (spectralWeight r) hw heven (a^2 * (C*‖g‖^2)) hfiniteScaled
  have hcoeff (k : Fin d → ℤ) :
      BrownianSharp.Torus.realPeriodicFourierCoeff rfa k =
        UnitAddTorus.mFourierCoeff (fun z => ((fa z).re : ℂ)) k := by
    apply congrArg (fun u : UnitAddTorus (Fin d) → ℂ =>
      UnitAddTorus.mFourierCoeff u k)
    funext z
    change (rfa z : ℂ) = ((fa z).re : ℂ)
    rw [hreal]
  have hB : (∑' k : Fin d → ℤ, ENNReal.ofReal
      (spectralWeight r k *
        ‖BrownianSharp.Torus.realPeriodicFourierCoeff rfa k‖^2)) ≤
      ENNReal.ofReal (2 * (a^2 * (C*‖g‖^2))) := by
    calc
      _ = ∑' k : Fin d → ℤ, ENNReal.ofReal
          (spectralWeight r k *
            ‖UnitAddTorus.mFourierCoeff (fun z => ((fa z).re : ℂ)) k‖^2) := by
              apply tsum_congr
              intro k
              rw [← hcoeff k]
      _ ≤ ENNReal.ofReal (2 * (a^2 * (C*‖g‖^2))) := hts
  have hQle : Q / A^2 ≤ 1 := by
    apply (div_le_one₀ (sq_pos_of_pos hA)).2
    dsimp [A]
    nlinarith [hQ]
  have hnorm : ‖g‖^2 ≤ 1 := by
    nlinarith [norm_nonneg g, hg]
  have hsmallReal : M * (2 * (a^2 * (C*‖g‖^2))) ≤ 1 := by
    have ha2 : a^2 = (A⁻¹)^2 := by rfl
    rw [ha2]
    have hbaseBound : Q * (A⁻¹)^2 ≤ 1 := by
      simpa [div_eq_mul_inv, inv_pow] using hQle
    have hbaseNonneg : 0 ≤ Q * (A⁻¹)^2 := mul_nonneg hQ (sq_nonneg _)
    calc
      M * (2 * ((A⁻¹)^2 * (C*‖g‖^2))) =
          Q * (A⁻¹)^2 * ‖g‖^2 := by dsimp [Q]; ring
      _ ≤ Q * (A⁻¹)^2 * 1 := mul_le_mul_of_nonneg_left hnorm hbaseNonneg
      _ = Q * (A⁻¹)^2 := by ring
      _ ≤ 1 := hbaseBound
  have hscale : ENNReal.ofReal M *
      ENNReal.ofReal (2 * (a^2 * (C*‖g‖^2))) ≤ 1 := by
    rw [← ENNReal.ofReal_mul hM]
    exact ENNReal.ofReal_le_one.mpr hsmallReal
  exact BrownianSharp.AlignmentPaperPeriodicFourierReverse.mem_sobolev_two_unitBall_of_fourier_energy
    r hr rfa (ENNReal.ofReal (2 * (a^2 * (C*‖g‖^2)))) hB hscale

/-- Restriction from the period-eight torus to the original data cube. -/
def periodEightCubeMap {d : ℕ} :
    C(HaarQuarter.BrownianCubeAnchor d, UnitAddTorus (Fin d)) where
  toFun := fun t => BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus t.val
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' 1).comp
      (((continuous_apply i).comp continuous_subtype_val).div_const 8)

noncomputable def periodEightRestrictionCLM {d : ℕ} :
    C(UnitAddTorus (Fin d),ℝ) →L[ℝ] C(HaarQuarter.BrownianCubeAnchor d,ℝ) := by
  let L : C(UnitAddTorus (Fin d),ℝ) →ₗ[ℝ] C(HaarQuarter.BrownianCubeAnchor d,ℝ) := {
    toFun := fun f => f.comp (periodEightCubeMap (d:=d))
    map_add' := by intro f g; ext t; rfl
    map_smul' := by intro a f; ext t; rfl }
  exact L.mkContinuous 1 (by
    intro f
    rw [ContinuousMap.norm_le_of_nonempty]
    intro t
    change ‖f (periodEightCubeMap (d:=d) t)‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using ContinuousMap.norm_coe_le_norm f _)

@[simp] theorem periodEightRestrictionCLM_apply {d : ℕ}
    (f : C(UnitAddTorus (Fin d),ℝ)) (t : HaarQuarter.BrownianCubeAnchor d) :
    periodEightRestrictionCLM (d:=d) f t =
      f (BrownianSharp.AlignmentPaperCubePeriodization.cubeIntoPeriodEightTorus t.val) := rfl

/-- Restricting a periodized cutoff source recovers the actual normalized
Matérn feature output on the data cube. -/
theorem rawTensorMaternFeatureOutput_eq_periodEightRestriction {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    periodEightRestrictionCLM (d:=d) (rawTensorMaternCutoffPeriodization κ h hκ hh g) =
      AlignmentFractionalSheetRKHS.featureOperator (complexSheetFeature κ h hκ hh) g := by
  ext t
  have ht : t.val ∈ Set.Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) :=
    Set.mem_Icc.mpr ⟨fun i => (t.property i).1, fun i => (t.property i).2⟩
  exact rawTensorMaternCutoffPeriodization_restrict κ h hκ hh g t.val ht

/-- Restriction to the cube is contractive in the continuous-function norm. -/
theorem periodEightRestriction_norm_le {d : ℕ}
    (f : C(UnitAddTorus (Fin d),ℝ)) :
    ‖periodEightRestrictionCLM (d:=d) f‖ ≤ ‖f‖ := by
  have hR : ‖periodEightRestrictionCLM (d:=d)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    have hx : ‖periodEightRestrictionCLM (d:=d) x‖ ≤ ‖x‖ := by
      rw [ContinuousMap.norm_le_of_nonempty]
      intro t
      rw [periodEightRestrictionCLM_apply]
      exact ContinuousMap.norm_coe_le_norm x _
    simpa only [one_mul] using hx
  calc
    ‖periodEightRestrictionCLM (d:=d) f‖ ≤
        ‖periodEightRestrictionCLM (d:=d)‖ * ‖f‖ :=
          (periodEightRestrictionCLM (d:=d)).le_opNorm f
    _ ≤ ‖f‖ := by nlinarith [norm_nonneg f]

/-- The actual normalized Matérn feature image is contained in a fixed scalar
multiple of the restriction of the literal periodic Sobolev-2 unit ball. -/
theorem rawTensorMaternFeatureImage_subset_restricted_sobolev {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (N : ℕ) (hN : (h + 1/2) / 2 ≤ N) :
    ∃ A : ℝ, 0 < A ∧
      (AlignmentFractionalSheetRKHS.featureOperator (complexSheetFeature κ h hκ hh) ''
        Metric.closedBall (0 : ComplexProductL2 κ h) 1) ⊆
      periodEightRestrictionCLM (d:=d) ''
        BrownianSharp.AlignmentScaledSetWidth.scalarImage A
          {f : C(UnitAddTorus (Fin d),ℝ) |
            BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall
              BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff
              2 (h+1/2) f} := by
  obtain ⟨A,hA,hball⟩ := rawTensorMaternCutoffPeriodization_exists_sobolev_scalar
    κ h hκ hh N hN
  refine ⟨A,hA,?_⟩
  rintro y ⟨g,hg,rfl⟩
  have hgNorm : ‖g‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hg
  let p := rawTensorMaternCutoffPeriodization κ h hκ hh g
  refine ⟨p, ?_, ?_⟩
  · refine ⟨A⁻¹ • p, hball g hgNorm, ?_⟩
    simp [BrownianSharp.AlignmentScaledSetWidth.scalarImage, smul_smul, hA.ne']
  · simpa [p] using rawTensorMaternFeatureOutput_eq_periodEightRestriction κ h hκ hh g

/-- The normalized Matérn feature ball has the sharp periodic Sobolev width
upper order. This is the upper-width direction only; the matching lower rate
is supplied separately by the windowed source embedding. -/
theorem rawTensorMaternFeatureImage_width_upper {d : ℕ}
    (hd : 2 ≤ d) (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (AlignmentFractionalSheetRKHS.featureOperator (complexSheetFeature κ h hκ hh) ''
          Metric.closedBall (0 : ComplexProductL2 κ h) 1) k ≤
        ENNReal.ofReal (C * logarithmicIndexRate (h+1/2)
          ((h+1/2) * (d-1:ℕ) + 1/2) k) := by
  let r : ℝ := h + 1/2
  let J : Set C(UnitAddTorus (Fin d),ℝ) :=
    {f | BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall
      BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff 2 r f}
  have hr : 1/2 < r := by dsimp [r]; linarith
  obtain ⟨C0,hC0,n0,hwidth⟩ :=
    BrownianSharp.AlignmentLatestPeriodicWidths.periodic_sobolev_width_upper hd 2 r
      (by norm_num) hr
  obtain ⟨A,hA,hsubset⟩ := rawTensorMaternFeatureImage_subset_restricted_sobolev
    κ h hκ hh (Nat.ceil ((h+1/2)/2)) (by exact_mod_cast Nat.le_ceil ((h+1/2)/2))
  let K := AlignmentFractionalSheetRKHS.featureOperator
    (complexSheetFeature κ h hκ hh) '' Metric.closedBall (0 : ComplexProductL2 κ h) 1
  let R := periodEightRestrictionCLM (d:=d)
  have hcompact : IsCompact (closure J) := by
    apply BrownianSharp.AlignmentPaperPeriodicCompactness.smoothSobolev_unitBall_closure_isCompact hd
    exact hr
  have hwidthEq := BrownianSharp.AlignmentPaperContinuousSmoothing.torus_width_eq_LInfinity_width
    J hcompact
  have hJrate : ∀ k, n0 ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth J k ≤
        ENNReal.ofReal (C0 * logarithmicIndexRate r
          (r*(d-1:ℕ)+1/2) k) := by
    intro k hk
    have hset : BrownianSharp.Latest.periodicLInfinityImage
        {f : BrownianSharp.Torus.RealPeriodic d |
          BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall
            BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff 2 r f} =
        AlignmentAmbientWidth.continuousToLInfinity
          (volume : Measure (UnitAddTorus (Fin d))) '' J := by
      ext x
      simp [BrownianSharp.Latest.periodicLInfinityImage, J,
        AlignmentAmbientWidth.continuousToLInfinity,
        BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall_fixed]
    rw [hwidthEq, ← hset]
    have h := hwidth k hk
    simpa [r] using h
  refine ⟨A*C0, mul_pos hA hC0, max n0 2, ?_⟩
  intro k hk
  have hk0 : n0 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  have hrate : 0 ≤ logarithmicIndexRate r (r*(d-1:ℕ)+1/2) k := by
    unfold logarithmicIndexRate
    have hkR : (1:ℝ) < (k:ℝ) := by exact_mod_cast (show 1 < k by omega)
    have hlog : 0 < Real.log (k:ℝ) := Real.log_pos hkR
    positivity
  have hJ : HaarQuarter.TheoremD.Width.kolmogorovWidth J k ≤
      ENNReal.ofReal (C0 * logarithmicIndexRate r
        (r*(d-1:ℕ)+1/2) k) := hJrate k hk0
  have hinc : K ⊆ R ''
      BrownianSharp.AlignmentScaledSetWidth.scalarImage A J := by
    simpa [K, R, J, r] using hsubset
  have hup := BrownianSharp.AlignmentPaperWidthContraction.kolmogorovWidth_le_of_subset_contractive_scalar_image
    R periodEightRestriction_norm_le A
    (C0 * logarithmicIndexRate r (r*(d-1:ℕ)+1/2) k) hA
    (mul_nonneg hC0.le hrate) hinc k hJ
  simpa [K, r, mul_assoc] using hup

/-- Width upper bound for the actual raw positive Matérn spectral amplitudes.
The amplitude enters only through the exact tensor scaling factor. -/
theorem maternRawSpectralFeature_width_upper {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (AlignmentFractionalSheetRKHS.featureOperator
          (BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
          κ c h hκ hc hh) '' Metric.closedBall
            (0 : BrownianSharp.AlignmentMaternTensorFeature.SpectralProductL2 κ h) 1) k ≤
        ENNReal.ofReal (C * logarithmicIndexRate (h+1/2)
          ((h+1/2) * (d-1:ℕ) + 1/2) k) := by
  let P : ℝ := ∏ i, c i * BrownianSharp.AlignmentMaternContinuousFeature.spectralMass (κ i) h
  let a : ℝ := Real.sqrt P
  have hP : 0 < P := Finset.prod_pos fun i hi =>
    mul_pos (hc i) (BrownianSharp.AlignmentMaternContinuousFeature.spectralMass_pos
      (κ i) h (hκ i) hh)
  have ha : 0 < a := Real.sqrt_pos.2 hP
  obtain ⟨C0,hC0,k0,hupper⟩ := rawTensorMaternFeatureImage_width_upper hd κ h hκ hh
  let Kc := AlignmentFractionalSheetRKHS.featureOperator
    (BrownianSharp.AlignmentMaternComplexFeature.complexSheetFeature κ h hκ hh) ''
      Metric.closedBall (0 : ComplexProductL2 κ h) 1
  let Kr := AlignmentFractionalSheetRKHS.featureOperator
    (BrownianSharp.AlignmentMaternTensorFeature.maternSheetFeature κ h hκ hh) ''
      Metric.closedBall
        (0 : BrownianSharp.AlignmentMaternTensorFeature.SpectralProductL2 κ h) 1
  let Ka := AlignmentFractionalSheetRKHS.featureOperator
    (BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
      κ c h hκ hc hh) '' Metric.closedBall
        (0 : BrownianSharp.AlignmentMaternTensorFeature.SpectralProductL2 κ h) 1
  have hbase : ∀ k, k0 ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth Kr k ≤
        ENNReal.ofReal (C0 * logarithmicIndexRate (h+1/2)
          ((h+1/2)*(d-1:ℕ)+1/2) k) := by
    intro k hk
    have hbaseUpper := hupper k hk
    have heq : Kc = Kr :=
      BrownianSharp.AlignmentMaternComplexFeature.complexSheetFeature_ball_eq_real κ h hκ hh
    rw [← heq]
    exact hbaseUpper
  have hset : Ka = BrownianSharp.AlignmentScaledSetWidth.scalarImage a Kr := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨AlignmentFractionalSheetRKHS.featureOperator
        (BrownianSharp.AlignmentMaternTensorFeature.maternSheetFeature κ h hκ hh) z,
        ⟨z,hz,rfl⟩,?_⟩
      ext t
      simp [Ka, Kr, BrownianSharp.AlignmentFractionalSheetRKHS.featureOperator_apply,
        BrownianSharp.AlignmentMaternTensorFeature.maternSheetFeature,
        BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude,
        a, P, real_inner_smul_left]
    · rintro ⟨x,⟨z,hz,rfl⟩,rfl⟩
      refine ⟨z,hz,?_⟩
      ext t
      simp [Ka, Kr, BrownianSharp.AlignmentFractionalSheetRKHS.featureOperator_apply,
        BrownianSharp.AlignmentMaternTensorFeature.maternSheetFeature,
        BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude,
        a, P, real_inner_smul_left]
  have hrate_nonneg {k : ℕ} (hk : 2 ≤ k) :
      0 ≤ logarithmicIndexRate (h+1/2)
        ((h+1/2)*(d-1:ℕ)+1/2) k := by
    unfold logarithmicIndexRate
    have hkR : (1:ℝ) < (k:ℝ) := by exact_mod_cast (show 1 < k by omega)
    positivity
  refine ⟨a*C0,mul_pos ha hC0,max k0 2,?_⟩
  intro k hk
  have hk0 : k0 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  have hbasek := hbase k hk0
  have hE : 0 ≤ C0 * logarithmicIndexRate (h+1/2)
      ((h+1/2)*(d-1:ℕ)+1/2) k := mul_nonneg hC0.le (hrate_nonneg hk2)
  have hscaled := BrownianSharp.AlignmentScaledSetWidth.kolmogorovWidth_scalarImage_le_of_bound
    Kr k a (C0 * logarithmicIndexRate (h+1/2)
      ((h+1/2)*(d-1:ℕ)+1/2) k) ha hE (by simpa [hset] using hbasek)
  calc
    HaarQuarter.TheoremD.Width.kolmogorovWidth Ka k =
        HaarQuarter.TheoremD.Width.kolmogorovWidth
          (BrownianSharp.AlignmentScaledSetWidth.scalarImage a Kr) k := by rw [hset]
    _ ≤ ENNReal.ofReal
        (a * (C0 * logarithmicIndexRate (h+1/2)
          ((h+1/2)*(d-1:ℕ)+1/2) k)) := hscaled
    _ = ENNReal.ofReal
        ((a*C0) * logarithmicIndexRate (h+1/2)
          ((h+1/2)*(d-1:ℕ)+1/2) k) := by congr 1; ring

/-- Carl's width-to-entropy transfer for the actual raw Matérn feature ball. -/
theorem maternRawSpectralFeature_entropy_upper {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k
        (AlignmentCompactFeatureBall.featureBall
          (BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
            κ c h hκ hc hh)) ≤
        ENNReal.ofReal (C * logarithmicIndexRate (h+1/2)
          ((h+1/2)*(d-1:ℕ)+1/2) k) := by
  let F := BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
    κ c h hκ hc hh
  let K := AlignmentFractionalSheetRKHS.featureOperator F ''
    Metric.closedBall (0 : BrownianSharp.AlignmentMaternTensorFeature.SpectralProductL2 κ h) 1
  let T := AlignmentFractionalSheetRKHS.featureOperator F
  obtain ⟨Cw,hCw,k0,hwidth⟩ := maternRawSpectralFeature_width_upper hd κ c h hκ hc hh
  let m0 := max k0 2
  have hm0 : 2 ≤ m0 := le_max_right _ _
  have hwidth' : ∀ k : ℕ, m0 ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth K k ≤
        ENNReal.ofReal (Cw * logarithmicIndexRate (h+1/2)
          ((h+1/2)*(d-1:ℕ)+1/2) k) := by
    intro k hk
    apply hwidth k
    exact (le_max_left _ _).trans hk
  let R := ‖T‖
  have hR : 0 ≤ R := norm_nonneg T
  have hbound : ∀ f ∈ K, ‖f‖ ≤ R := by
    rintro f ⟨g,hg,rfl⟩
    have hgNorm : ‖g‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hg
    dsimp [R,T]
    calc
      ‖AlignmentFractionalSheetRKHS.featureOperator F g‖ ≤
          ‖AlignmentFractionalSheetRKHS.featureOperator F‖ * ‖g‖ :=
        (AlignmentFractionalSheetRKHS.featureOperator F).le_opNorm g
      _ ≤ ‖AlignmentFractionalSheetRKHS.featureOperator F‖ :=
        calc
          _ ≤ ‖AlignmentFractionalSheetRKHS.featureOperator F‖ * 1 :=
            mul_le_mul_of_nonneg_left hgNorm
              (norm_nonneg (AlignmentFractionalSheetRKHS.featureOperator F))
          _ = _ := by ring
  have hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth K 0 ≤ ENNReal.ofReal R :=
    BrownianSharp.AlignmentAuditPeriodicBoundedness.kolmogorovWidth_zero_le_of_norm_bound
      K R hbound
  have hs : 0 < h+1/2 := by linarith
  have ha : 0 ≤ (h+1/2)*(d-1:ℕ)+1/2 := by positivity
  obtain ⟨Cu,hCu,ku,hku,hupper⟩ :=
    BrownianSharp.AlignmentEndpointDyadicEntropy.entropy_upper_all_indices_of_width_upper
      K hs ha hR hCw m0 hm0 hzero hwidth'
  have hball : AlignmentCompactFeatureBall.featureBall F = K :=
    BrownianSharp.AlignmentPaperGaussianFeatureBridge.featureBall_eq_featureOperator_image F
  refine ⟨Cu,hCu,ku,hku,?_⟩
  · intro k hk
    rw [hball]
    exact hupper k hk

/-- Uniform two-sided entropy estimate with the paper's quantifier order:
constants are selected from `(d,κ,c,h)` before the Gaussian realization. -/
theorem maternRawSpectral_intrinsicCM_entropy_two_sided {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ cE CE : ℝ, 0 < cE ∧ 0 < CE ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (X : HaarQuarter.BrownianCubeAnchor d → Ω → ℝ)
        (hX : ∀ x, MemLp (X x) 2 P)
        (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
        (hcov : ∀ x y,
          cov[X x, X y; P] =
            ∏ i, c i * BrownianSharp.AlignmentMaternSpectralFeature.stationaryCovariance
              (κ i) h (x.val i) (y.val i)),
        ∀ k : ℕ, k₀ ≤ k →
          ENNReal.ofReal (cE * logarithmicIndexRate (h+1/2)
            ((h+1/2)*(d-1:ℕ)+1/2) k) ≤
              HaarQuarter.TheoremD.entropyNumber k (intrinsicGaussianCMUnitBall X hX) ∧
          HaarQuarter.TheoremD.entropyNumber k (intrinsicGaussianCMUnitBall X hX) ≤
            ENNReal.ofReal (CE * logarithmicIndexRate (h+1/2)
              ((h+1/2)*(d-1:ℕ)+1/2) k) := by
  obtain ⟨cE,hcE,kE,hkE,hlo⟩ :=
    BrownianSharp.AlignmentPaperMatern.maternSheetRawSpectralFeature_entropy_lower
      hd κ c h hκ hc hh
  obtain ⟨CE,hCE,kU,hkU,hupFeature⟩ :=
    maternRawSpectralFeature_entropy_upper hd κ c h hκ hc hh
  let k₀ := max kE kU
  refine ⟨cE,CE,hcE,hCE,k₀,le_trans hkE (le_max_left _ _),?_⟩
  intro Ω hΩ P hP X hX hmean hcov k hk
  let F := BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
    κ c h hκ hc hh
  have hball := BrownianSharp.AlignmentPaperGaussianFeatureBridge.maternRawSpectral_intrinsicCM_ball_eq_featureBall
    κ c h hκ hc hh X hX hmean hcov
  have himage := BrownianSharp.AlignmentPaperGaussianFeatureBridge.featureBall_eq_featureOperator_image F
  have hkE' : kE ≤ k := (le_max_left _ _).trans hk
  have hkU' : kU ≤ k := (le_max_right _ _).trans hk
  constructor
  · rw [hball, himage]
    exact hlo k hkE'
  · rw [hball]
    exact hupFeature k hkU'

/-- Uniform sharp Kolmogorov-width equivalence for the intrinsic CM balls of
all Gaussian realizations with fixed raw Matérn parameters. -/
theorem maternRawSpectral_intrinsicCM_width_two_sided {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ cW CW : ℝ, 0 < cW ∧ 0 < CW ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (X : HaarQuarter.BrownianCubeAnchor d → Ω → ℝ)
        (hX : ∀ x, MemLp (X x) 2 P)
        (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
        (hcov : ∀ x y,
          cov[X x, X y; P] =
            ∏ i, c i * BrownianSharp.AlignmentMaternSpectralFeature.stationaryCovariance
              (κ i) h (x.val i) (y.val i)),
        ∀ k : ℕ, k₀ ≤ k →
          ENNReal.ofReal (cW * logarithmicIndexRate (h+1/2)
            ((h+1/2)*(d-1:ℕ)+1/2) k) ≤
              HaarQuarter.TheoremD.Width.kolmogorovWidth
                (intrinsicGaussianCMUnitBall X hX) k ∧
          HaarQuarter.TheoremD.Width.kolmogorovWidth
                (intrinsicGaussianCMUnitBall X hX) k ≤
              ENNReal.ofReal (CW * logarithmicIndexRate (h+1/2)
                ((h+1/2)*(d-1:ℕ)+1/2) k) := by
  let F := BrownianSharp.AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
    κ c h hκ hc hh
  let K := AlignmentFractionalSheetRKHS.featureOperator F ''
    Metric.closedBall (0 : BrownianSharp.AlignmentMaternTensorFeature.SpectralProductL2 κ h) 1
  let T := AlignmentFractionalSheetRKHS.featureOperator F
  let r := h+1/2
  let α := r*(d-1:ℕ)+1/2
  obtain ⟨cE,hcE,kE,hkE,hEntropy⟩ :=
    BrownianSharp.AlignmentPaperMatern.maternSheetRawSpectralFeature_entropy_lower
      hd κ c h hκ hc hh
  have hEntropyK : ∃ cE' : ℝ, 0<cE' ∧ ∃ n₀ : ℕ, ∀ n, n₀≤n →
      ENNReal.ofReal (cE' * logarithmicIndexRate r α n) ≤
        HaarQuarter.TheoremD.entropyNumber n K := by
    refine ⟨cE,hcE,kE,?_⟩
    intro n hn
    simpa [K,r,α] using hEntropy n hn
  obtain ⟨Cw,hCw,kW,hwidth⟩ := maternRawSpectralFeature_width_upper hd κ c h hκ hc hh
  have hUpperK : ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n, n₀≤n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth K n ≤
        ENNReal.ofReal (C * logarithmicIndexRate r α n) := by
    refine ⟨Cw,hCw,kW,?_⟩
    intro n hn
    simpa [K,r,α] using hwidth n hn
  let R := ‖T‖
  have hR : 0≤R := norm_nonneg T
  have hbound : ∀ f ∈ K, ‖f‖ ≤ R := by
    rintro f ⟨g,hg,rfl⟩
    have hg' : ‖g‖≤1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hg
    dsimp [R,T]
    calc
      ‖AlignmentFractionalSheetRKHS.featureOperator F g‖ ≤
          ‖AlignmentFractionalSheetRKHS.featureOperator F‖ * ‖g‖ :=
        (AlignmentFractionalSheetRKHS.featureOperator F).le_opNorm g
      _ ≤ ‖AlignmentFractionalSheetRKHS.featureOperator F‖ * 1 :=
        mul_le_mul_of_nonneg_left hg'
          (norm_nonneg (AlignmentFractionalSheetRKHS.featureOperator F))
      _ = _ := by ring
  have hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth K 0 ≤ ENNReal.ofReal R :=
    BrownianSharp.AlignmentAuditPeriodicBoundedness.kolmogorovWidth_zero_le_of_norm_bound
      K R hbound
  have hr : 0<r := by dsimp [r]; linarith
  have ha : 0≤α := by dsimp [α,r]; positivity
  have hwidthRate := BrownianSharp.AlignmentWidthRates.twoSidedWidthRate_of_entropy_lower_and_width_upper
    K r α R hr ha hR hzero hEntropyK hUpperK
  obtain ⟨cW,CW,hcW,hCW,k0,hk0,hKrate⟩ := hwidthRate
  have hballF : AlignmentCompactFeatureBall.featureBall F = K :=
    BrownianSharp.AlignmentPaperGaussianFeatureBridge.featureBall_eq_featureOperator_image F
  refine ⟨cW,CW,hcW,hCW,k0,hk0,?_⟩
  intro Ω hΩ P hP X hX hmean hcov k hk
  have hball := BrownianSharp.AlignmentPaperGaussianFeatureBridge.maternRawSpectral_intrinsicCM_ball_eq_featureBall
    κ c h hκ hc hh X hX hmean hcov
  rw [hball, hballF]
  exact hKrate k hk

end BrownianSharp.AlignmentPaperMaternUpper
