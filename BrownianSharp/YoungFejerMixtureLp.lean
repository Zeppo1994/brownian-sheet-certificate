import BrownianSharp.YoungConvolutionLp
import BrownianSharp.ScalarKernelL1
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-! Finite signed mixtures of positive Fejer kernels act on `Lᵖ` with norm
bounded by the actual coefficient variation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
open BrownianSharp.ScalarKernelL1
open AddCircle HaarQuarter.TheoremD.FejerFourier

namespace BrownianSharp

/-- The real-valued Fejer kernel, obtained from the actual Fejer polynomial. -/
def realFejerKernel (N : ℕ) : C(UnitAddCircle, ℝ) :=
  ⟨fun x => ‖fejerFourierPolynomial N x‖, (fejer_continuous N).norm⟩

theorem realFejerKernel_nonneg (N : ℕ) (x : UnitAddCircle) :
    0 ≤ realFejerKernel N x := by
  change 0 ≤ ‖fejerFourierPolynomial N x‖
  exact norm_nonneg _

theorem realFejerKernel_integral (N : ℕ) (hN : 0 < N) :
    (∫ x : UnitAddCircle, realFejerKernel N x ∂AddCircle.haarAddCircle) = 1 := by
  simpa [realFejerKernel, fejerKernel] using fejer_norm_integral N hN

/-- A finite real signed Fejer mixture has its convolution `Lᵖ` moment bounded
by the coefficient variation to the `p`th power times the input moment. -/
theorem realFejer_mixture_convolution_rpow_le
    (S : Finset ℕ) (w : ℕ → ℝ) (hpos : ∀ N ∈ S, 0 < N)
    (u : C(UnitAddCircle, ℝ)) (p : ℝ) (hp : 1 ≤ p) :
    (∫ x : UnitAddCircle,
      |∫ y, (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y)
          ∂AddCircle.haarAddCircle| ^ p ∂AddCircle.haarAddCircle) ≤
      (∑ N ∈ S, |w N|) ^ p *
        ∫ x : UnitAddCircle, |u x| ^ p ∂AddCircle.haarAddCircle := by
  classical
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let A : ℝ := ∑ N ∈ S, |w N|
  let c (N : ℕ) (x : UnitAddCircle) : ℝ :=
    ∫ y, realFejerKernel N y * u (x-y) ∂μ
  let q (x : UnitAddCircle) : ℝ := ∑ N ∈ S, w N * c N x
  have hA : 0 ≤ A := by positivity
  have hFpos (N : ℕ) (hN : N ∈ S) (x : UnitAddCircle) :
      0 ≤ realFejerKernel N x := realFejerKernel_nonneg N x
  have hFmass (N : ℕ) (hN : N ∈ S) :
      (∫ x, realFejerKernel N x ∂μ) = 1 := realFejerKernel_integral N (hpos N hN)
  have hcMeas (N : ℕ) : Measurable (c N) := by
    have hs : StronglyMeasurable (fun x : UnitAddCircle =>
        ∫ y, realFejerKernel N y * u (x-y) ∂μ) :=
      (((realFejerKernel N).continuous.comp continuous_snd).mul
        (u.continuous.comp (continuous_fst.sub continuous_snd))).stronglyMeasurable
          |>.integral_prod_right
    exact hs.measurable
  have hsubx (x : UnitAddCircle) : Continuous (fun y : UnitAddCircle => x-y) :=
    continuous_const.sub continuous_id
  have hcBound (N : ℕ) (hN : N ∈ S) (x : UnitAddCircle) : |c N x| ≤ ‖u‖ := by
    have hki : Integrable (fun y : UnitAddCircle =>
        realFejerKernel N y * u (x-y)) μ := by
      have hc : Continuous (fun y : UnitAddCircle =>
          realFejerKernel N y * u (x-y)) :=
        (realFejerKernel N).continuous.mul (u.continuous.comp (hsubx x))
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmi : Integrable (fun y : UnitAddCircle =>
        realFejerKernel N y * |u (x-y)|) μ := by
      have hc : Continuous (fun y : UnitAddCircle =>
          realFejerKernel N y * |u (x-y)|) :=
        (realFejerKernel N).continuous.mul
          (continuous_abs.comp (u.continuous.comp (hsubx x)))
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hupper : Integrable (fun y : UnitAddCircle =>
        realFejerKernel N y * ‖u‖) μ :=
      ((realFejerKernel N).continuous.mul_const _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      |c N x| ≤ ∫ y, |realFejerKernel N y * u (x-y)| ∂μ := abs_integral_le_integral_abs
      _ = ∫ y, realFejerKernel N y * |u (x-y)| ∂μ := by
        congr 1; funext y; rw [abs_mul, abs_of_nonneg (hFpos N hN y)]
      _ ≤ ∫ y, realFejerKernel N y * ‖u‖ ∂μ := by
        apply integral_mono hmi hupper
        intro y
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using (u.norm_le (norm_nonneg _)).mp le_rfl (x-y))
          (hFpos N hN y)
      _ = ‖u‖ := by rw [integral_mul_const, hFmass N hN, one_mul]
  have hcPowIntegrable (N : ℕ) (hN : N ∈ S) :
      Integrable (fun x => |c N x| ^ p) μ := by
    apply Integrable.of_bound
      ((Real.continuous_rpow_const (le_trans (by norm_num) hp)).measurable.comp
        ((continuous_abs.measurable.comp (hcMeas N)))).aestronglyMeasurable (‖u‖ ^ p)
    filter_upwards [] with x
    change |(|c N x| ^ p)| ≤ ‖u‖ ^ p
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hcBound N hN x)
      (le_trans (by norm_num) hp)
  have hsingle (N : ℕ) (hN : N ∈ S) :
      (∫ x, |c N x| ^ p ∂μ) ≤ ∫ x, |u x| ^ p ∂μ := by
    simpa [c, μ] using addCircle_positive_convolution_rpow_le
      (realFejerKernel N) u (hFpos N hN) (hFmass N hN) p hp
  have hconvEq (x : UnitAddCircle) :
      (∫ y, (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y) ∂μ) = q x := by
    calc
      _ = ∫ y, ∑ N ∈ S, (w N * realFejerKernel N y) * u (x-y) ∂μ := by
        congr 1
        funext y
        rw [Finset.sum_mul]
      _ = ∑ N ∈ S, ∫ y, (w N * realFejerKernel N y) * u (x-y) ∂μ := by
        rw [integral_finset_sum]
        intro N hN
        have hc : Continuous (fun y : UnitAddCircle =>
            (w N * realFejerKernel N y) * u (x-y)) := by fun_prop
        exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      _ = q x := by
        dsimp [q, c]
        apply Finset.sum_congr rfl
        intro N hN
        rw [show (fun y : UnitAddCircle =>
          (w N * realFejerKernel N y) * u (x-y)) =
          fun y => w N * (realFejerKernel N y * u (x-y)) by
            funext y; ring]
        rw [integral_const_mul]
  by_cases hAzero : A = 0
  · have hwzero (N : ℕ) (hN : N ∈ S) : w N = 0 := by
      have hle : |w N| ≤ A := by
        dsimp [A]
        exact Finset.single_le_sum (fun M hM => abs_nonneg (w M)) hN
      exact abs_eq_zero.mp (le_antisymm (by simpa [hAzero] using hle) (abs_nonneg _))
    have hqzero : ∀ x, q x = 0 := by
      intro x
      dsimp [q]
      apply Finset.sum_eq_zero
      intro N hN
      rw [hwzero N hN]
      simp
    have hkernelzero : (fun y : UnitAddCircle =>
        ∑ N ∈ S, w N * realFejerKernel N y) = 0 := by
      funext y
      apply Finset.sum_eq_zero
      intro N hN
      rw [hwzero N hN]
      simp
    have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
    have hzeroFun : (fun x : UnitAddCircle => |∫ y,
        (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y) ∂μ| ^ p) = 0 := by
      funext x
      have hintzero : (fun y : UnitAddCircle =>
          (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y)) = 0 := by
        funext y
        rw [congrFun hkernelzero y]
        simp
      rw [show (∫ y, (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y) ∂μ) = 0 by
        rw [show (fun y => (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y) :
          UnitAddCircle → ℝ) = 0 from hintzero]
        simp]
      simp [Real.zero_rpow hp0]
    rw [hzeroFun]
    simp [A, hAzero, Real.zero_rpow hp0]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    let v (N : ℕ) : ℝ := |w N| / A
    have hvnonneg (N : ℕ) : 0 ≤ v N := div_nonneg (abs_nonneg _) hApos.le
    have hvsum : (∑ N ∈ S, v N) = 1 := by
      simp [v, A, div_eq_mul_inv, ← Finset.sum_mul, hApos.ne', inv_mul_cancel₀]
    have hpoint (x : UnitAddCircle) :
        |q x| ^ p ≤ A ^ p * ∑ N ∈ S, v N * |c N x| ^ p := by
      have htriangle : |q x| ≤ ∑ N ∈ S, |w N| * |c N x| := by
        dsimp [q]
        calc
          |∑ N ∈ S, w N * c N x| ≤ ∑ N ∈ S, |w N * c N x| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ N ∈ S, |w N| * |c N x| := by
            apply Finset.sum_congr rfl
            intro N hN
            rw [abs_mul]
      have hJensen := (convexOn_rpow hp).map_sum_le
        (t := S) (w := v) (p := fun N => |c N x|)
        (fun N hN => hvnonneg N) hvsum
        (fun N hN => Set.mem_Ici.mpr (abs_nonneg _))
      have hnonneg : 0 ≤ ∑ N ∈ S, v N * |c N x| := by
        apply Finset.sum_nonneg
        intro N hN
        exact mul_nonneg (hvnonneg N) (abs_nonneg _)
      have hJensen' :
          (∑ N ∈ S, v N * |c N x|) ^ p ≤
            ∑ N ∈ S, v N * |c N x| ^ p := by
        simpa [smul_eq_mul] using hJensen
      have hscale : (∑ N ∈ S, |w N| * |c N x|) =
          A * (∑ N ∈ S, v N * |c N x|) := by
        calc
          _ = ∑ N ∈ S, A * (v N * |c N x|) := by
            apply Finset.sum_congr rfl
            intro N hN
            dsimp [v]
            field_simp [hApos.ne']
          _ = _ := by rw [Finset.mul_sum]
      calc
        _ ≤ (∑ N ∈ S, |w N| * |c N x|) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) htriangle (le_trans (by norm_num) hp)
        _ = (A * (∑ N ∈ S, v N * |c N x|)) ^ p := by rw [hscale]
        _ = A ^ p * (∑ N ∈ S, v N * |c N x|) ^ p :=
          Real.mul_rpow hApos.le hnonneg
        _ ≤ A ^ p * ∑ N ∈ S, v N * |c N x| ^ p := by
          exact mul_le_mul_of_nonneg_left hJensen' (Real.rpow_nonneg hApos.le _)
    have hqMeas : Measurable q := by
      apply Finset.measurable_sum
      intro N hN
      exact measurable_const.mul (hcMeas N)
    have hqInt : Integrable (fun x => |q x| ^ p) μ := by
      apply Integrable.of_bound
        ((Real.continuous_rpow_const (le_trans (by norm_num) hp)).measurable.comp
          (continuous_abs.measurable.comp hqMeas)).aestronglyMeasurable
        ((∑ N ∈ S, |w N| * ‖u‖) ^ p)
      filter_upwards [] with x
      have hqbound : |q x| ≤ ∑ N ∈ S, |w N| * ‖u‖ := by
        calc
          |q x| ≤ ∑ N ∈ S, |w N| * |c N x| := by
            dsimp [q]
            calc
              |∑ N ∈ S, w N * c N x| ≤ ∑ N ∈ S, |w N * c N x| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = ∑ N ∈ S, |w N| * |c N x| := by
                apply Finset.sum_congr rfl
                intro N hN
                rw [abs_mul]
          _ ≤ ∑ N ∈ S, |w N| * ‖u‖ := by
            apply Finset.sum_le_sum
            intro N hN
            exact mul_le_mul_of_nonneg_left (hcBound N hN x) (abs_nonneg _)
      change |(|q x| ^ p)| ≤ _
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) hqbound (le_trans (by norm_num) hp)
    calc
      (∫ x, |∫ y, (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y) ∂μ| ^ p ∂μ)
          = ∫ x, |q x| ^ p ∂μ := by
            congr 1
            funext x
            rw [hconvEq x]
      _ ≤
          ∫ x, A ^ p * ∑ N ∈ S, v N * |c N x| ^ p ∂μ := by
            apply integral_mono hqInt
            · have hsumInt : Integrable (fun x : UnitAddCircle =>
                  ∑ N ∈ S, v N * |c N x| ^ p) μ := by
                apply integrable_finset_sum
                intro N hN
                exact (hcPowIntegrable N hN).const_mul (v N)
              exact hsumInt.const_mul (A ^ p)
            · exact fun x => hpoint x
      _ = A ^ p * ∑ N ∈ S, v N * (∫ x, |c N x| ^ p ∂μ) := by
            rw [integral_const_mul, integral_finset_sum]
            · congr 1
              apply Finset.sum_congr rfl
              intro N hN
              rw [integral_const_mul]
            · intro N hN
              exact (hcPowIntegrable N hN).const_mul _
      _ ≤ A ^ p * ∑ N ∈ S, v N * (∫ x, |u x| ^ p ∂μ) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hApos.le _)
            apply Finset.sum_le_sum
            intro N hN
            exact mul_le_mul_of_nonneg_left (hsingle N hN) (hvnonneg N)
      _ = A ^ p * ∫ x, |u x| ^ p ∂μ := by rw [← Finset.sum_mul, hvsum, one_mul]
      _ = (∑ N ∈ S, |w N|) ^ p * ∫ x, |u x| ^ p ∂μ := by rfl

end BrownianSharp
