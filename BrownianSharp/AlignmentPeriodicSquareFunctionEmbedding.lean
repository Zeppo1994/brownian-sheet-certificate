import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace BrownianSharp.AlignmentPeriodicSquareFunctionEmbedding

/-- Finite Minkowski inequality for a square function: at exponent p≥2 the
Lp norm of the sum of squared block magnitudes is controlled by the ℓ² sum
of block Lp norms. -/
theorem finite_square_sum_rpow_le
    {α ι F : Type*} [MeasurableSpace α] [MeasurableSpace F]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [BorelSpace F]
    {μ : Measure α} {p : ℝ} (hp : 2 ≤ p)
    (s : Finset ι) (g : ι → α → F) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hg : ∀ i ∈ s, AEStronglyMeasurable (g i) μ) :
    (∫⁻ x, ENNReal.ofReal
      (∑ i ∈ s, (w i * ‖g i x‖) ^ 2) ^ (p / 2) ∂μ) ≤
      (∑ i ∈ s, (ENNReal.ofReal (w i) *
        eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2) ^ (p / 2) := by
  classical
  let q : ℝ := p / 2
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let u : ι → α → ℝ := fun i x => w i * ‖g i x‖
  let v : ι → α → ℝ := fun i x => u i x * u i x
  have hu_meas : ∀ i ∈ s, AEStronglyMeasurable (u i) μ := by
    intro i hi
    exact (hg i hi).norm.const_mul (w i)
  have hv_meas : ∀ i ∈ s, AEStronglyMeasurable (v i) μ := by
    intro i hi
    convert (hu_meas i hi).mul (hu_meas i hi) using 1 <;> funext x <;> simp [v]
  have hsum_nonneg (x : α) : 0 ≤ ∑ i ∈ s, v i x := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_self_nonneg _
  have htriangle :
      eLpNorm' (∑ i ∈ s, v i) q μ ≤
        ∑ i ∈ s, eLpNorm' (v i) q μ := by
    exact (eLpNorm'_sum_le (fun i hi => hv_meas i hi) hq)
  have hterm (i : ι) (hi : i ∈ s) :
      eLpNorm' (v i) q μ =
        (ENNReal.ofReal (w i) * eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2 := by
    have hnormsq : ∀ x, v i x = ‖u i x‖ ^ 2 := by
      intro x
      have hu_nonneg : 0 ≤ u i x := by
        dsimp [u]
        exact mul_nonneg (hw i) (norm_nonneg _)
      calc
        v i x = u i x * u i x := rfl
        _ = (u i x) ^ 2 := by ring
        _ = ‖u i x‖ ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg hu_nonneg]
    rw [show v i = fun x => ‖u i x‖ ^ 2 by funext x; exact hnormsq x]
    rw [show (fun x => ‖u i x‖ ^ 2) = (fun x => ‖u i x‖ ^ (2 : ℝ)) by
      funext x; exact (Real.rpow_natCast _ _).symm]
    rw [eLpNorm'_norm_rpow (u i) q (2 : ℝ) (by norm_num)]
    have hqp : q * 2 = p := by dsimp [q]; ring
    rw [hqp]
    have hscale : eLpNorm' (u i) p μ =
        ENNReal.ofReal (w i) * eLpNorm (g i) (ENNReal.ofReal p) μ := by
      have hsmul : u i = (w i) • (fun x => ‖g i x‖) := by
        funext x
        simp [u, smul_eq_mul]
      rw [hsmul, eLpNorm'_const_smul]
      · have hnorm : eLpNorm' (fun x => ‖g i x‖) p μ =
            eLpNorm (g i) (ENNReal.ofReal p) μ := by
          rw [eLpNorm'_norm]
          simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
            (eLpNorm_eq_eLpNorm' (by positivity : ENNReal.ofReal p ≠ 0)
              ENNReal.ofReal_ne_top (hg i hi)).symm
        rw [hnorm]
        rw [Real.enorm_of_nonneg (hw i)]
      · exact lt_of_lt_of_le zero_lt_one (by linarith [hp])
    rw [hscale]
    simp
  have hsum_integral :
      (∫⁻ x, ENNReal.ofReal (∑ i ∈ s, v i x) ^ q ∂μ) =
        (eLpNorm' (∑ i ∈ s, v i) q μ) ^ q := by
    let S : α → ℝ := ∑ i ∈ s, v i
    have hS (x : α) : S x = ∑ i ∈ s, v i x := by simp [S]
    have hreal (x : α) : ENNReal.ofReal (∑ i ∈ s, v i x) = ‖S x‖ₑ := by
      rw [← hS x]
      exact (Real.enorm_of_nonneg (by rw [hS]; exact hsum_nonneg x)).symm
    calc
      (∫⁻ x, ENNReal.ofReal (∑ i ∈ s, v i x) ^ q ∂μ) =
          ∫⁻ x, ‖S x‖ₑ ^ q ∂μ := by
            apply lintegral_congr_ae
            filter_upwards [] with x
            rw [hreal x]
      _ = (eLpNorm' S q μ) ^ q := lintegral_rpow_enorm_eq_rpow_eLpNorm' hqpos
      _ = (eLpNorm' (∑ i ∈ s, v i) q μ) ^ q := by rfl
  calc
    (∫⁻ x, ENNReal.ofReal (∑ i ∈ s, (w i * ‖g i x‖) ^ 2) ^ (p / 2) ∂μ)
        = (∫⁻ x, ENNReal.ofReal (∑ i ∈ s, v i x) ^ q ∂μ) := by
            apply lintegral_congr_ae
            filter_upwards [] with x
            rw [show q = p / 2 by rfl]
            apply congrArg (fun z : ℝ≥0∞ => z ^ (p / 2))
            apply congrArg ENNReal.ofReal
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [v, u]
            ring
    _ = (eLpNorm' (∑ i ∈ s, v i) q μ) ^ q := hsum_integral
    _ ≤ (∑ i ∈ s, eLpNorm' (v i) q μ) ^ q := by
          exact ENNReal.rpow_le_rpow (by simpa [Finset.sum_apply] using htriangle) (by positivity)
    _ = (∑ i ∈ s,
          (ENNReal.ofReal (w i) * eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2) ^ (p / 2) := by
          have hs : (∑ i ∈ s, eLpNorm' (v i) q μ) =
              ∑ i ∈ s, (ENNReal.ofReal (w i) * eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i hi
          rw [hs]

/-- Countable Minkowski inequality for the actual ENNReal-valued square
function. -/
theorem lintegral_tsum_square_function_le
    {α ι F : Type*} [MeasurableSpace α] [MeasurableSpace F] [Countable ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [BorelSpace F]
    {μ : Measure α} {p : ℝ} (hp : 2 ≤ p)
    (g : ι → α → F) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hg : ∀ i, StronglyMeasurable (g i)) :
    (∫⁻ x, (∑' i, ENNReal.ofReal ((w i) ^ 2 * ‖g i x‖ ^ 2)) ^ (p / 2) ∂μ) ≤
      (∑' i, (ENNReal.ofReal (w i) *
        eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2) ^ (p / 2) := by
  classical
  let Fsum : Finset ι → α → ℝ≥0∞ := fun s x =>
    ∑ i ∈ s, ENNReal.ofReal ((w i) ^ 2 * ‖g i x‖ ^ 2)
  have hmeas : ∀ s : Finset ι, Measurable (fun x => Fsum s x ^ (p / 2)) := by
    intro s
    apply ENNReal.continuous_rpow_const.measurable.comp
    unfold Fsum
    fun_prop
  have hdirected : Directed (· ≤ ·) (fun s : Finset ι => fun x => Fsum s x ^ (p / 2)) := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x
      apply ENNReal.rpow_le_rpow ?_ (by linarith [hp])
      unfold Fsum
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro i hi hnot
      positivity
    · intro x
      apply ENNReal.rpow_le_rpow ?_ (by linarith [hp])
      unfold Fsum
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      intro i hi hnot
      positivity
  have hiSup :
      (∫⁻ x, ⨆ s : Finset ι, Fsum s x ^ (p / 2) ∂μ) =
        ⨆ s : Finset ι, ∫⁻ x, Fsum s x ^ (p / 2) ∂μ :=
    lintegral_iSup_directed_of_measurable hmeas hdirected
  have hterm_sum : ∀ x,
      (∑' i, ENNReal.ofReal ((w i) ^ 2 * ‖g i x‖ ^ 2)) = ⨆ s : Finset ι, Fsum s x := by
    intro x
    simp [Fsum, ENNReal.tsum_eq_iSup_sum]
  have hpartial : ∀ s : Finset ι,
      (∫⁻ x, Fsum s x ^ (p / 2) ∂μ) ≤
        (∑' i, (ENNReal.ofReal (w i) * eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2) ^ (p / 2) := by
    intro s
    have hsum (x : α) : Fsum s x = ENNReal.ofReal (∑ i ∈ s, (w i * ‖g i x‖) ^ 2) := by
      unfold Fsum
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (w i) ^ 2 * ‖g i x‖ ^ 2 = (w i * ‖g i x‖) ^ 2 by ring]
      · intro i hi
        positivity
    calc
      (∫⁻ x, Fsum s x ^ (p / 2) ∂μ) =
          ∫⁻ x, ENNReal.ofReal (∑ i ∈ s, (w i * ‖g i x‖) ^ 2) ^ (p / 2) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards [] with x
            rw [hsum x]
      _ ≤ (∑ i ∈ s, (ENNReal.ofReal (w i) *
            eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2) ^ (p / 2) :=
          finite_square_sum_rpow_le hp s g w hw (fun i hi => (hg i).aestronglyMeasurable)
      _ ≤ (∑' i, (ENNReal.ofReal (w i) * eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2) ^ (p / 2) := by
          apply ENNReal.rpow_le_rpow ?_ (by linarith [hp])
          apply ENNReal.sum_le_tsum
  have hpow_iSup : ∀ x,
      (⨆ s : Finset ι, Fsum s x) ^ (p / 2) =
        ⨆ s : Finset ι, Fsum s x ^ (p / 2) := by
    intro x
    let f : ℝ≥0∞ → ℝ≥0∞ := fun z => z ^ (p / 2)
    have hmono : Monotone f := by
      intro a b hab
      exact ENNReal.rpow_le_rpow hab (by linarith [hp])
    have hbot : f 0 = 0 := by
      dsimp [f]
      rw [ENNReal.zero_rpow_of_pos (by linarith [hp] : 0 < p / 2)]
    exact Monotone.map_iSup_of_continuousAt
      ENNReal.continuous_rpow_const.continuousAt hmono hbot
  calc
    (∫⁻ x, (∑' i, ENNReal.ofReal ((w i) ^ 2 * ‖g i x‖ ^ 2)) ^ (p / 2) ∂μ) =
        ∫⁻ x, ⨆ s : Finset ι, Fsum s x ^ (p / 2) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [] with x
          rw [hterm_sum x, hpow_iSup x]
    _ = ⨆ s : Finset ι, ∫⁻ x, Fsum s x ^ (p / 2) ∂μ := hiSup
    _ ≤ (∑' i, (ENNReal.ofReal (w i) * eLpNorm (g i) (ENNReal.ofReal p) μ) ^ 2) ^ (p / 2) :=
          iSup_le hpartial

end BrownianSharp.AlignmentPeriodicSquareFunctionEmbedding
