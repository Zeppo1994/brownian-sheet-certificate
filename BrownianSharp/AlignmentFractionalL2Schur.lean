import BrownianSharp.AlignmentFractionalDensity
import BrownianSharp.AlignmentFractionalSemigroup
import BrownianSharp.AlignmentFractionalL2OperatorSemigroup
import BrownianSharp.AlignmentFractionalPolynomialProjectionRate
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Initial Schur-kernel calculations for the genuine fractional Volterra
operator on the unit interval. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentFractionalL2Schur

/-- The weighted Cauchy--Schwarz estimate used in the Schur test. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (K G : α → ℝ≥0∞) (hK : AEMeasurable K μ) (hG : AEMeasurable G μ) :
    (∫⁻ x, K x * G x ∂μ)^2 ≤
      (∫⁻ x, K x ∂μ) * (∫⁻ x, K x * (G x)^2 ∂μ) := by
  have hKG : AEMeasurable (fun x => K x * (G x)^2) μ :=
    hK.mul (hG.pow_const 2)
  have hcs := ENNReal.lintegral_mul_norm_pow_le hK hKG
      (p := (1/2:ℝ)) (q := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hleft : (∫⁻ x, K x * G x ∂μ) =
      ∫⁻ x, (K x)^(1/2:ℝ) * (K x * (G x)^2)^(1/2:ℝ) ∂μ := by
    congr 1
    funext x
    rw [ENNReal.mul_rpow_of_nonneg (K x) ((G x)^2) (by norm_num)]
    have hroot : (K x ^ (1/2:ℝ))^2 = K x := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      simp

    have hsquare : (G x ^ 2)^(1/2:ℝ) = G x := by
      rw [← ENNReal.rpow_natCast (G x) 2, ← ENNReal.rpow_mul]
      norm_num
    calc
      K x * G x = (K x ^ (1/2:ℝ))^2 * G x := by
        exact congrArg (fun z : ℝ≥0∞ => z * G x) hroot.symm
      _ = K x ^ (1/2:ℝ) * (K x ^ (1/2:ℝ) * G x) := by
        simp only [pow_two]
        ac_rfl
      _ = K x ^ (1/2:ℝ) * (K x ^ (1/2:ℝ) * (G x ^ 2)^(1/2:ℝ)) := by
        rw [hsquare]
  have hcs' : (∫⁻ x, K x * G x ∂μ) ≤
      (∫⁻ x, K x ∂μ)^(1/2:ℝ) *
        (∫⁻ x, K x * (G x)^2 ∂μ)^(1/2:ℝ) := by
    rw [hleft]
    exact hcs
  calc
    (∫⁻ x, K x * G x ∂μ)^2 ≤
        ((∫⁻ x, K x ∂μ)^(1/2:ℝ) *
          (∫⁻ x, K x * (G x)^2 ∂μ)^(1/2:ℝ))^2 := by
      exact pow_le_pow_left' hcs' 2
    _ = (∫⁻ x, K x ∂μ) * (∫⁻ x, K x * (G x)^2 ∂μ) := by
      rw [← ENNReal.rpow_natCast
        ((∫⁻ x, K x ∂μ)^(1/2:ℝ) *
          (∫⁻ x, K x * (G x)^2 ∂μ)^(1/2:ℝ)) 2]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      simp

/-- Schur's weighted L² estimate in extended nonnegative form.  The hypotheses
are stated at the level of row and column masses, so the result applies to
singular Volterra kernels without requiring a square-integrable kernel. -/
theorem schur_lintegral_sq_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (K : α → β → ℝ≥0∞) (G : β → ℝ≥0∞) (A B : ℝ≥0∞)
    (hKGprod : AEMeasurable (fun z => K z.1 z.2 * G z.2 ^ 2) (μ.prod ν))
    (hKrow : ∀ x, AEMeasurable (K x) ν)
    (hKcol : ∀ y, AEMeasurable (fun x => K x y) μ)
    (hG : AEMeasurable G ν)
    (hrow : ∀ x, (∫⁻ y, K x y ∂ν) ≤ A)
    (hcol : ∀ y, (∫⁻ x, K x y ∂μ) ≤ B) :
    (∫⁻ x, (∫⁻ y, K x y * G y ∂ν)^2 ∂μ) ≤
      A * B * (∫⁻ y, (G y)^2 ∂ν) := by
  have hKGprod' : AEMeasurable
      (Function.uncurry (fun x y => K x y * G y ^ 2)) (μ.prod ν) := by
    convert hKGprod using 1 <;> ext z <;> rfl
  have hswap := lintegral_lintegral_swap hKGprod'
  have hJ : AEMeasurable (fun x => ∫⁻ y, K x y * (G y)^2 ∂ν) μ :=
    hKGprod'.lintegral_prod_right
  have hG2 : AEMeasurable (fun y => (G y)^2) ν := hG.pow_const 2
  calc
    (∫⁻ x, (∫⁻ y, K x y * G y ∂ν)^2 ∂μ) ≤
        ∫⁻ x, (∫⁻ y, K x y ∂ν) *
          (∫⁻ y, K x y * (G y)^2 ∂ν) ∂μ := by
      apply lintegral_mono
      intro x
      exact lintegral_mul_sq_le ν (K x) G (hKrow x) hG
    _ ≤ ∫⁻ x, A * (∫⁻ y, K x y * (G y)^2 ∂ν) ∂μ := by
      apply lintegral_mono
      intro x
      exact mul_le_mul_of_nonneg_right (hrow x) (by positivity)
    _ = A * (∫⁻ x, ∫⁻ y, K x y * (G y)^2 ∂ν ∂μ) := by
      rw [lintegral_const_mul'' _ hJ]
    _ = A * (∫⁻ y, ∫⁻ x, K x y * (G y)^2 ∂μ ∂ν) := by
      rw [hswap]
    _ ≤ A * ∫⁻ y, B * (G y)^2 ∂ν := by
      apply mul_le_mul_of_nonneg_left
      · apply lintegral_mono
        intro y
        calc
          ∫⁻ x, K x y * (G y)^2 ∂μ =
              (∫⁻ x, K x y ∂μ) * (G y)^2 := by
                rw [lintegral_mul_const'' _ (hKcol y)]
          _ ≤ B * (G y)^2 := by
            exact mul_le_mul_of_nonneg_right (hcol y) (by positivity)
      · positivity
    _ = A * B * (∫⁻ y, (G y)^2 ∂ν) := by
      rw [lintegral_const_mul'' _ hG2]
      ac_rfl

open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalSemigroup
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalPolynomialProjectionRate
open BrownianSharp.AlignmentFractionalPolynomialSpaces

/-- Squared error of the actual source projection of a causal kernel row. -/
noncomputable def causalKernelPolynomialResidualSq (α : ℝ) (hα : 1/2 < α)
    (q n : ℕ) (t : ℝ) : ℝ :=
  if ht : t ∈ UnitInterval then
    let ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa [UnitInterval] using ht
    ‖causalKernelUnitVector α t hα ht'.1 ht'.2 -
      polynomialProjection q n (causalKernelUnitVector α t hα
        ht'.1 ht'.2)‖^2
  else 0

/-- Integrating the pointwise polynomial source-projection estimate gives the
actual squared Hilbert--Schmidt kernel residual on the target unit interval. -/
theorem exists_integrated_causalKernel_polynomialResidual {α : ℝ}
    (hα : 1/2 < α) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < q ∧ 0 < C ∧
      ∀ n : ℕ, 1 ≤ n →
        (∫⁻ t, ENNReal.ofReal (causalKernelPolynomialResidualSq α hα q n t)
          ∂(volume.restrict UnitInterval)) ≤
            ENNReal.ofReal (C * (1/(2:ℝ)^n)^(2*α-1)) := by
  obtain ⟨q,C,hq,hC,hres⟩ :=
    exists_degree_causalKernel_polynomialProjection_dyadic_rate hα
  refine ⟨q,C,hq,hC,?_⟩
  intro n hn
  let μ : Measure ℝ := volume.restrict UnitInterval
  let R : ℝ := C * (1/(2:ℝ)^n)^(2*α-1)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hmass : μ Set.univ = 1 := by
    simp [μ, UnitInterval, Real.volume_Icc]
  have hpt : ∀ᵐ t ∂μ, ENNReal.ofReal
      (causalKernelPolynomialResidualSq α hα q n t) ≤ ENNReal.ofReal R := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hmem : t ∈ UnitInterval := by simpa [UnitInterval] using ht
    rw [causalKernelPolynomialResidualSq, dif_pos hmem]
    have h := hres n hn t ht.1 ht.2
    exact ENNReal.ofReal_le_ofReal (by simpa [R] using h)
  calc
    (∫⁻ t, ENNReal.ofReal (causalKernelPolynomialResidualSq α hα q n t) ∂μ) ≤
        ∫⁻ _ : ℝ, ENNReal.ofReal R ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal R := by simp [hmass]

/-- For every positive order, the causal kernel is integrable on the unit
source interval; this uses only the L¹ power threshold β>0. -/
theorem causalKernel_intervalIntegrable_unit {β t : ℝ} (hβ : 0 < β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntervalIntegrable (fun u : ℝ => causalKernel β t u) volume 0 1 := by
  have hbase : IntervalIntegrable (fun u : ℝ => kernel β (t-u)) volume 0 t := by
    have hker : IntervalIntegrable (kernel β) volume 0 t := by
      unfold kernel
      exact (intervalIntegral.intervalIntegrable_rpow'
        (by linarith : -1 < β-1)).const_mul _
    have hshift := hker.comp_sub_left t
    simpa using hshift.symm
  have hleft : IntervalIntegrable (fun u : ℝ => causalKernel β t u) volume 0 t := by
    have heq : Set.EqOn (fun u : ℝ => causalKernel β t u)
        (fun u => kernel β (t-u)) (Set.uIoo 0 t) := by
      intro u hu
      have hu0 : 0 < u := by
        simpa [Set.uIoo, min_eq_left ht0] using hu.1
      have hut : u < t := by
        have hmax : u < max (0:ℝ) t := by
          simpa [Set.uIoo, min_eq_left ht0] using hu.2
        rcases lt_max_iff.mp hmax with h | h
        · linarith
        · exact h
      simp [causalKernel, hut]
    exact (intervalIntegrable_congr_uIoo heq).mpr hbase
  have hright : IntervalIntegrable (fun u : ℝ => causalKernel β t u) volume t 1 := by
    have heq : Set.EqOn (fun u : ℝ => causalKernel β t u)
        (fun _ => (0:ℝ)) (Set.uIoo t 1) := by
      intro u hu
      have huLow : t < u := by
        have hmin : min t (1:ℝ) < u := by simpa [Set.uIoo] using hu.1
        rcases min_lt_iff.mp hmin with h | h
        · exact h
        · linarith
      simp [causalKernel, le_of_lt huLow]
    have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume t 1 :=
      continuous_const.intervalIntegrable t 1
    exact (intervalIntegrable_congr_uIoo heq).mpr hz
  exact hleft.trans hright

/-- The same integrability assertion with the causal variables reversed; it
is used for column masses. -/
theorem causalKernel_column_intervalIntegrable_unit {β u : ℝ} (hβ : 0 < β)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IntervalIntegrable (fun t : ℝ => causalKernel β t u) volume 0 1 := by
  have hbase : IntervalIntegrable (fun t : ℝ => kernel β (t-u)) volume u 1 := by
    have hker : IntervalIntegrable (kernel β) volume 0 (1-u) := by
      unfold kernel
      exact (intervalIntegral.intervalIntegrable_rpow'
        (by linarith : -1 < β-1)).const_mul _
    have hshift := hker.comp_add_right (-u)
    simpa [sub_eq_add_neg] using hshift
  have hleft : IntervalIntegrable (fun t : ℝ => causalKernel β t u) volume 0 u := by
    have heq : Set.EqOn (fun t : ℝ => causalKernel β t u)
        (fun _ => (0:ℝ)) (Set.uIoo 0 u) := by
      intro t ht
      have htu : t < u := by
        simpa [Set.uIoo, min_eq_left hu0, max_eq_right hu0] using ht.2
      simp [causalKernel, le_of_lt htu]
    have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 u :=
      continuous_const.intervalIntegrable 0 u
    exact (intervalIntegrable_congr_uIoo heq).mpr hz
  have hright : IntervalIntegrable (fun t : ℝ => causalKernel β t u) volume u 1 := by
    have heq : Set.EqOn (fun t : ℝ => causalKernel β t u)
        (fun t => kernel β (t-u)) (Set.uIoo u 1) := by
      intro t ht
      have htu : u < t := by
        have hmin : min u (1:ℝ) < t := by simpa [Set.uIoo] using ht.1
        rcases min_lt_iff.mp hmin with h | h
        · exact h
        · linarith
      simp [causalKernel, htu]
    exact (intervalIntegrable_congr_uIoo heq).mpr hbase
  exact hleft.trans hright

/-- The positive causal fractional kernel on the unit square. -/
def schurKernel (β t u : ℝ) : ℝ := causalKernel β t u

/-- ENNReal version used by Tonelli's theorem. -/
def schurKernelENN (β t u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (schurKernel β t u)

theorem schurKernel_nonneg {β t u : ℝ} (hβ : 0 < β) :
    0 ≤ schurKernel β t u := by
  unfold schurKernel causalKernel
  split_ifs with h
  · unfold kernel
    have hp : 0 < t-u := sub_pos.mpr h
    positivity
  · exact le_rfl

theorem schurKernel_measurable (β : ℝ) :
    Measurable (Function.uncurry (fun t u => schurKernelENN β t u)) := by
  have hcond : MeasurableSet {z : ℝ × ℝ | z.2 < z.1} :=
    measurableSet_lt measurable_snd measurable_fst
  unfold schurKernelENN schurKernel causalKernel kernel
  exact ENNReal.measurable_ofReal.comp
    (Measurable.ite hcond (by fun_prop) measurable_const)

/-- Integral of the scalar Gamma-normalized power kernel over an interval. -/
theorem kernel_interval_integral {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L) :
    (∫ x in (0:ℝ)..L, kernel β x) = L^β / Real.Gamma (β+1) := by
  by_cases hLpos : 0 < L
  · have hpow := rlIntegral_rpow (a := β) (γ := 1) hβ (by norm_num) hLpos
    have href : (∫ x in (0:ℝ)..L, kernel β (L-x)) =
        ∫ x in (0:ℝ)..L, kernel β x := by
      simpa using (intervalIntegral.integral_comp_sub_left (f := kernel β) L)
    have hΓ : Real.Gamma (β+1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith : 0 < β+1)).ne'
    have hh : rlIntegral β (fun _ : ℝ => 1) L =
        (Real.Gamma (β+1))⁻¹ * L^β := by
      simpa [rlIntegral, kernel, Real.Gamma_one, add_comm, add_left_comm,
        add_assoc] using hpow
    calc
      (∫ x in (0:ℝ)..L, kernel β x) =
          (∫ x in (0:ℝ)..L, kernel β (L-x)) := href.symm
      _ = rlIntegral β (fun _ : ℝ => 1) L := by
        simp [rlIntegral, mul_comm]
      _ = (Real.Gamma (β+1))⁻¹ * L^β := hh
      _ = L^β / Real.Gamma (β+1) := by
        rw [div_eq_mul_inv]
        ring
  · have hLe : L = 0 := le_antisymm (le_of_not_gt hLpos) hL
    subst L
    simp [kernel, Real.zero_rpow hβ.ne']

/-- Exact row mass of the causal kernel. This is the Schur row bound before
using `t ≤ 1`. -/
theorem schurKernel_row_integral {β t : ℝ} (hβ : 0 < β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u, schurKernel β t u ∂(volume.restrict UnitInterval)) =
      t ^ β / Real.Gamma (β+1) := by
  calc
    (∫ u, causalKernel β t u ∂(volume.restrict UnitInterval)) =
        ∫ u, causalKernel β t u * (1:ℝ) ∂(volume.restrict UnitInterval) := by simp
    _ = rlIntegral β (fun _ : ℝ => 1) t :=
      causal_integral_eq_interval ht0 ht1 (fun _ : ℝ => 1)
    _ = t ^ β / Real.Gamma (β+1) := by
      by_cases htp : 0 < t
      · have h := rlIntegral_rpow (a := β) (γ := 1) hβ (by norm_num) htp
        have hΓ : Real.Gamma (β+1) ≠ 0 :=
          (Real.Gamma_pos_of_pos (by linarith : 0 < β+1)).ne'
        have hh : rlIntegral β (fun _ : ℝ => 1) t =
            (Real.Gamma (β+1))⁻¹ * t^β := by
          simpa [rlIntegral, kernel, Real.Gamma_one, add_comm, add_left_comm,
            add_assoc] using h
        rw [hh, div_eq_mul_inv]
        ring
      · have ht : t = 0 := le_antisymm (le_of_not_gt htp) ht0
        subst t
        have hΓ : Real.Gamma (β+1) ≠ 0 :=
          (Real.Gamma_pos_of_pos (by linarith : 0 < β+1)).ne'
        simp [rlIntegral, kernel, Real.zero_rpow hβ.ne', hΓ]

/-- Exact column mass, by translating the interval `[u,1]` to `[0,1-u]`. -/
theorem schurKernel_column_integral {β u : ℝ} (hβ : 0 < β)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ t, schurKernel β t u ∂(volume.restrict UnitInterval)) =
      (1-u) ^ β / Real.Gamma (β+1) := by
  let x : ℝ → ℝ := fun t => schurKernel β t u
  have hEq : x =ᵐ[volume.restrict UnitInterval]
      (Set.Icc u 1).indicator (fun t => kernel β (t-u)) := by
    have hne : ∀ᵐ t ∂(volume.restrict UnitInterval), t ≠ u :=
      ae_mono Measure.restrict_le_self (volume.ae_ne u)
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with t ht htu_ne
    by_cases htu : u < t
    · have hmem : t ∈ Set.Icc u 1 := ⟨le_of_lt htu, ht.2⟩
      rw [Set.indicator_of_mem hmem]
      simp [x, schurKernel, causalKernel, htu]
    · have htule : t ≤ u := le_of_not_gt htu
      have hlt : t < u := lt_of_le_of_ne htule htu_ne
      have hnot : t ∉ Set.Icc u 1 := by simp [Set.mem_Icc, not_le_of_gt hlt]
      rw [Set.indicator_apply_eq_zero.mpr (by intro hm; exact (hnot hm).elim)]
      simp [x, schurKernel, causalKernel, htu]
  rw [show (∫ t, schurKernel β t u ∂(volume.restrict UnitInterval)) =
      ∫ t, (Set.Icc u 1).indicator (fun t => kernel β (t-u)) t
        ∂(volume.restrict UnitInterval) from integral_congr_ae hEq]
  have hsub : Set.Icc u 1 ⊆ UnitInterval := by
    intro t ht
    exact ⟨le_trans hu0 ht.1, ht.2⟩
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict_of_subset hsub]
  have hInt : (∫ t in (u:ℝ)..1, kernel β (t-u)) =
      (1-u)^β / Real.Gamma (β+1) := by
    have h : (∫ t in (u:ℝ)..1, kernel β (t-u)) =
        ∫ x in (0:ℝ)..(1-u), kernel β x := by
      simpa [sub_eq_add_neg] using
        (intervalIntegral.integral_comp_add_right (f := kernel β) (-u))
    rw [h]
    exact kernel_interval_integral hβ (sub_nonneg.mpr hu1)
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : u ≤ (1:ℝ))]
  exact hInt

/-- Row mass bound for the actual Gamma-normalized causal kernel. -/
theorem schurKernelENN_row_le {β t : ℝ} (hβ : 0 < β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ u, schurKernelENN β t u ∂(volume.restrict UnitInterval)) ≤
      ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  have hInterval := causalKernel_intervalIntegrable_unit hβ ht0 ht1
  have hIntegrable : Integrable (schurKernel β t) μ := by
    have h' := (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0:ℝ) ≤ 1)).mp hInterval
    change Integrable (fun u => causalKernel β t u) μ
    simpa [μ, UnitInterval] using h'.integrable
  have hnonneg : 0 ≤ᵐ[μ] schurKernel β t :=
    Filter.Eventually.of_forall (fun u => schurKernel_nonneg hβ)
  have hmass : (∫⁻ u, schurKernelENN β t u ∂μ) =
      ENNReal.ofReal (t^β / Real.Gamma (β+1)) := by
    change (∫⁻ u, ENNReal.ofReal (schurKernel β t u) ∂μ) = _
    rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hnonneg]
    rw [schurKernel_row_integral hβ ht0 ht1]
  rw [hmass]
  apply ENNReal.ofReal_le_ofReal
  have hpow : t^β ≤ 1 := Real.rpow_le_one ht0 ht1 hβ.le
  have hden : 0 < Real.Gamma (β+1) := Real.Gamma_pos_of_pos (by linarith)
  simpa [div_eq_mul_inv] using div_le_div_of_nonneg_right hpow hden.le

/-- Column mass bound for the actual Gamma-normalized causal kernel. -/
theorem schurKernelENN_column_le {β u : ℝ} (hβ : 0 < β)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫⁻ t, schurKernelENN β t u ∂(volume.restrict UnitInterval)) ≤
      ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  have hInterval := causalKernel_column_intervalIntegrable_unit hβ hu0 hu1
  have hIntegrable : Integrable (fun t => schurKernel β t u) μ := by
    have h' := (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0:ℝ) ≤ 1)).mp hInterval
    change Integrable (fun t => causalKernel β t u) μ
    simpa [μ, UnitInterval] using h'.integrable
  have hnonneg : 0 ≤ᵐ[μ] (fun t => schurKernel β t u) :=
    Filter.Eventually.of_forall (fun t => schurKernel_nonneg hβ)
  have hmass : (∫⁻ t, schurKernelENN β t u ∂μ) =
      ENNReal.ofReal ((1-u)^β / Real.Gamma (β+1)) := by
    change (∫⁻ t, ENNReal.ofReal (schurKernel β t u) ∂μ) = _
    rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hnonneg]
    rw [schurKernel_column_integral hβ hu0 hu1]
  rw [hmass]
  apply ENNReal.ofReal_le_ofReal
  have hpow : (1-u)^β ≤ 1 :=
    Real.rpow_le_one (by linarith : 0 ≤ 1-u) (by linarith : 1-u ≤ 1) hβ.le
  have hden : 0 < Real.Gamma (β+1) := Real.Gamma_pos_of_pos (by linarith)
  simpa [div_eq_mul_inv] using div_le_div_of_nonneg_right hpow hden.le

/-- Kernel restricted to the unit square, extended by zero so that the Schur
row and column hypotheses hold on the ambient real line. -/
def unitSchurKernelENN (β t u : ℝ) : ℝ≥0∞ :=
  if t ∈ UnitInterval ∧ u ∈ UnitInterval then schurKernelENN β t u else 0

theorem unitSchurKernelENN_measurable (β : ℝ) :
    Measurable (Function.uncurry (fun t u => unitSchurKernelENN β t u)) := by
  have hs : MeasurableSet {z : ℝ × ℝ | z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval} := by
    exact (measurableSet_Icc.preimage measurable_fst).inter
      (measurableSet_Icc.preimage measurable_snd)
  have hk := schurKernel_measurable β
  unfold unitSchurKernelENN
  exact Measurable.ite hs hk measurable_const

/-- Actual causal Gamma-kernel Schur estimate on the unit interval. The bound
is independent of the source profile and does not assume the kernel is in L². -/
theorem causalKernel_lintegral_sq_bound {β : ℝ} (hβ : 0 < β)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ t, (∫⁻ u, unitSchurKernelENN β t u * G u
      ∂(volume.restrict UnitInterval))^2 ∂(volume.restrict UnitInterval)) ≤
      (ENNReal.ofReal ((Real.Gamma (β+1))⁻¹))^2 *
        (∫⁻ u, G u^2 ∂(volume.restrict UnitInterval)) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  let K : ℝ → ℝ → ℝ≥0∞ := unitSchurKernelENN β
  have hKM : Measurable (Function.uncurry K) := by
    simpa [K] using unitSchurKernelENN_measurable β
  have hKG : AEMeasurable
      (fun z : ℝ × ℝ => K z.1 z.2 * G z.2^2) (μ.prod μ) := by
    exact (hKM.mul ((hG.comp measurable_snd).pow_const 2)).aemeasurable
  have hrow : ∀ t, (∫⁻ u, K t u ∂μ) ≤ ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) := by
    intro t
    by_cases ht : t ∈ UnitInterval
    · have heq : (fun u => K t u) =ᵐ[μ] (fun u => schurKernelENN β t u) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        simp [K, unitSchurKernelENN, ht, hu]
      rw [lintegral_congr_ae heq]
      exact schurKernelENN_row_le hβ (by simpa [UnitInterval, Set.mem_Icc] using ht.1)
        (by simpa [UnitInterval, Set.mem_Icc] using ht.2)
    · have hz : (fun u => K t u) = fun _ => (0:ℝ≥0∞) := by
        funext u
        simp [K, unitSchurKernelENN, ht]
      rw [hz]
      simp
  have hcol : ∀ u, (∫⁻ t, K t u ∂μ) ≤ ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) := by
    intro u
    by_cases hu : u ∈ UnitInterval
    · have heq : (fun t => K t u) =ᵐ[μ] (fun t => schurKernelENN β t u) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        simp [K, unitSchurKernelENN, ht, hu]
      rw [lintegral_congr_ae heq]
      exact schurKernelENN_column_le hβ (by simpa [UnitInterval, Set.mem_Icc] using hu.1)
        (by simpa [UnitInterval, Set.mem_Icc] using hu.2)
    · have hz : (fun t => K t u) = fun _ => (0:ℝ≥0∞) := by
        funext t
        simp [K, unitSchurKernelENN, hu]
      rw [hz]
      simp
  have hrowMeas : ∀ t, AEMeasurable (K t) μ := by
    intro t
    exact (hKM.comp measurable_prodMk_left).aemeasurable
  have hcolMeas : ∀ u, AEMeasurable (fun t => K t u) μ := by
    intro u
    exact (hKM.comp measurable_prodMk_right).aemeasurable
  simpa [K, μ, pow_two, mul_assoc] using
    schur_lintegral_sq_bound K G (ENNReal.ofReal ((Real.Gamma (β+1))⁻¹))
      (ENNReal.ofReal ((Real.Gamma (β+1))⁻¹)) hKG hrowMeas hcolMeas hG.aemeasurable
      hrow hcol

/-- The actual Schur estimate for the absolute value of any measurable real
profile, in the form used to extend RL integration from a dense class. -/
theorem causalKernel_absProfile_lintegral_sq_bound {β : ℝ} (hβ : 0 < β)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫⁻ t, (∫⁻ u, unitSchurKernelENN β t u * ENNReal.ofReal (|f u|)
      ∂(volume.restrict UnitInterval))^2 ∂(volume.restrict UnitInterval)) ≤
      (ENNReal.ofReal ((Real.Gamma (β+1))⁻¹))^2 *
        (∫⁻ u, (ENNReal.ofReal (|f u|))^2 ∂(volume.restrict UnitInterval)) := by
  have hnorm : Measurable (fun u => ENNReal.ofReal (|f u|)) := by
    convert ENNReal.measurable_ofReal.comp hf.norm using 1
    ext u
    simp [Real.norm_eq_abs]
  exact causalKernel_lintegral_sq_bound hβ (fun u => ENNReal.ofReal (|f u|))
    hnorm

/-- Nonnegative kernel action as an extended-valued measurable amplitude. -/
def causalKernelAmplitude (β : ℝ) (G : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, unitSchurKernelENN β t u * G u ∂(volume.restrict UnitInterval)

/-- Quantitative squared-energy estimate for the real-valued target amplitude. -/
theorem causalKernelAmplitude_energy_le {β : ℝ} (hβ : 0 < β)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G)
    (hEnergy : (∫⁻ u, G u^2 ∂(volume.restrict UnitInterval)) < ⊤) :
    (∫⁻ t, ENNReal.ofReal ((causalKernelAmplitude β G t).toReal^2)
      ∂(volume.restrict UnitInterval)) ≤
      (ENNReal.ofReal ((Real.Gamma (β+1))⁻¹))^2 *
        (∫⁻ u, G u^2 ∂(volume.restrict UnitInterval)) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  let H : ℝ → ℝ≥0∞ := causalKernelAmplitude β G
  have hH : Measurable H := by
    have hKM : Measurable (Function.uncurry (fun t u =>
        unitSchurKernelENN β t u * G u)) :=
      (unitSchurKernelENN_measurable β).mul (hG.comp measurable_snd)
    change Measurable (fun t => ∫⁻ u, unitSchurKernelENN β t u * G u ∂μ)
    exact hKM.lintegral_prod_right
  have hbound : (∫⁻ t, H t^2 ∂μ) ≤
      (ENNReal.ofReal ((Real.Gamma (β+1))⁻¹))^2 *
        (∫⁻ u, G u^2 ∂μ) := by
    simpa [H, μ, causalKernelAmplitude] using causalKernel_lintegral_sq_bound hβ G hG
  have hfinite : (∫⁻ t, H t^2 ∂μ) < ⊤ := by
    apply lt_of_le_of_lt hbound
    exact ENNReal.mul_lt_top
      (ENNReal.pow_lt_top (by simp : ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) < ⊤))
      hEnergy
  have hHtop : ∀ᵐ t ∂μ, H t < ⊤ := by
    have hsquare : ∀ᵐ t ∂μ, H t^2 < ⊤ :=
      ae_lt_top' (hH.pow_const 2).aemeasurable hfinite.ne
    filter_upwards [hsquare] with t ht
    exact (ENNReal.pow_lt_top_iff.mp ht).resolve_right (by norm_num)
  have heq : (fun t => ENNReal.ofReal ((H t).toReal^2)) =ᵐ[μ]
      (fun t => H t^2) := by
    filter_upwards [hHtop] with t ht
    rw [ENNReal.ofReal_pow (by positivity)]
    rw [ENNReal.ofReal_toReal (ne_top_of_lt ht)]
  rw [lintegral_congr_ae heq]
  exact hbound

/-- If the source amplitude has finite L² energy, the actual causal kernel
amplitude is an L² function. This packages Schur's estimate as membership in
the genuine target L² space. -/
theorem causalKernelAmplitude_memLp {β : ℝ} (hβ : 0 < β)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G)
    (hEnergy : (∫⁻ u, G u^2 ∂(volume.restrict UnitInterval)) < ⊤) :
    MemLp (fun t => (causalKernelAmplitude β G t).toReal) 2
      (volume.restrict UnitInterval) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  let H : ℝ → ℝ≥0∞ := causalKernelAmplitude β G
  have hKM : Measurable (Function.uncurry (fun t u =>
      unitSchurKernelENN β t u * G u)) := by
    exact (unitSchurKernelENN_measurable β).mul
      (hG.comp measurable_snd)
  have hH : Measurable H := by
    exact hKM.lintegral_prod_right
  have hbound : (∫⁻ t, H t^2 ∂μ) ≤
      (ENNReal.ofReal ((Real.Gamma (β+1))⁻¹))^2 *
        (∫⁻ u, G u^2 ∂μ) := by
    simpa [H, μ, causalKernelAmplitude] using causalKernel_lintegral_sq_bound hβ G hG
  have hfinite : (∫⁻ t, H t^2 ∂μ) < ⊤ := by
    apply lt_of_le_of_lt hbound
    exact ENNReal.mul_lt_top
      (ENNReal.pow_lt_top (by simp : ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) < ⊤))
      hEnergy
  have hHtop : ∀ᵐ t ∂μ, H t < ⊤ := by
    have hsqtop : ∀ᵐ t ∂μ, H t^2 < ⊤ :=
      ae_lt_top' (hH.pow_const 2).aemeasurable hfinite.ne
    filter_upwards [hsqtop] with t ht
    exact (ENNReal.pow_lt_top_iff.mp ht).resolve_right (by norm_num)
  have htoRealMeas : Measurable (fun t => (H t).toReal) :=
    ENNReal.measurable_toReal.comp hH
  have hsqMeas : AEMeasurable (fun t => (H t).toReal^2) μ :=
    (htoRealMeas.pow_const 2).aemeasurable
  have hsqAE : (fun t => ENNReal.ofReal ((H t).toReal^2)) =ᵐ[μ]
      (fun t => H t^2) := by
    filter_upwards [hHtop] with t ht
    rw [ENNReal.ofReal_pow (by positivity)]
    rw [ENNReal.ofReal_toReal (ne_top_of_lt ht)]
  have hsqIntegral : (∫⁻ t, ENNReal.ofReal ((H t).toReal^2) ∂μ) < ⊤ := by
    rw [lintegral_congr_ae hsqAE]
    exact hfinite
  have hnonneg : 0 ≤ᵐ[μ] (fun t => (H t).toReal^2) :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hfi : HasFiniteIntegral (fun t => (H t).toReal^2) μ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).2 hsqIntegral
  have hint : Integrable (fun t => (H t).toReal^2) μ :=
    ⟨hsqMeas.aestronglyMeasurable, hfi⟩
  rw [memLp_two_iff_integrable_sq htoRealMeas.aestronglyMeasurable]
  exact hint

/-- An L² input on the unit interval is L¹ there, with the unit mass as the
constant in Cauchy--Schwarz. -/
theorem unitInterval_abs_lintegral_finite {f : ℝ → ℝ} (hf : Measurable f)
    (henergy : (∫⁻ u, (ENNReal.ofReal (|f u|))^2
      ∂(volume.restrict UnitInterval)) < ⊤) :
    (∫⁻ u, ENNReal.ofReal (|f u|) ∂(volume.restrict UnitInterval)) < ⊤ := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  have hG : Measurable (fun u : ℝ => ENNReal.ofReal (|f u|)) := by
    exact ENNReal.measurable_ofReal.comp hf.norm
  have hcs := lintegral_mul_sq_le μ (fun _ : ℝ => (1:ℝ≥0∞))
    (fun u => ENNReal.ofReal (|f u|)) (by fun_prop) hG.aemeasurable
  have hmass : (∫⁻ _ : ℝ, (1:ℝ≥0∞) ∂μ) = 1 := by
    rw [lintegral_const]
    simp [μ, UnitInterval, Real.volume_Icc]
  have hbound : (∫⁻ u, ENNReal.ofReal (|f u|) ∂μ)^2 ≤
      ∫⁻ u, (ENNReal.ofReal (|f u|))^2 ∂μ := by
    simpa [hmass, μ] using hcs
  by_contra htop
  have hinf : (∫⁻ u, ENNReal.ofReal (|f u|) ∂μ) = ⊤ := by
    exact top_unique (le_of_not_gt htop)
  rw [hinf] at hbound
  simp at hbound
  have htople : ⊤ ≤ ∫⁻ u, (ENNReal.ofReal (|f u|))^2 ∂μ := by
    simpa using hbound
  exact (not_le_of_gt henergy) htople

/-- The absolute kernel-input product is integrable on the unit square. This
is the Fubini bridge needed to define the signed Volterra action almost
everywhere for an arbitrary L² profile. -/
theorem causalKernel_abs_product_integrable {β : ℝ} (hβ : 0 < β)
    (f : ℝ → ℝ) (hf : Measurable f)
    (henergy : (∫⁻ u, (ENNReal.ofReal (|f u|))^2
      ∂(volume.restrict UnitInterval)) < ⊤) :
    Integrable (fun z : ℝ × ℝ =>
      if z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval then
        schurKernel β z.1 z.2 * |f z.2| else 0)
      ((volume.restrict UnitInterval).prod (volume.restrict UnitInterval)) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  let K : ℝ → ℝ → ℝ≥0∞ := unitSchurKernelENN β
  let G : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (|f u|)
  have hG : Measurable G := by
    exact ENNReal.measurable_ofReal.comp hf.norm
  have hG1 := unitInterval_abs_lintegral_finite hf henergy
  have hKM : Measurable (Function.uncurry K) := by
    simpa [K] using unitSchurKernelENN_measurable β
  have hPG : Measurable (fun z : ℝ × ℝ => K z.1 z.2 * G z.2) :=
    hKM.mul (hG.comp measurable_snd)
  have hcolumn : ∀ u, (∫⁻ t, K t u ∂μ) ≤
      ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) := by
    intro u
    by_cases hu : u ∈ UnitInterval
    · have heq : (fun t => K t u) =ᵐ[μ] (fun t => schurKernelENN β t u) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        simp [K, unitSchurKernelENN, hu, ht]
      rw [lintegral_congr_ae heq]
      exact schurKernelENN_column_le hβ (by simpa [UnitInterval, Set.mem_Icc] using hu.1)
        (by simpa [UnitInterval, Set.mem_Icc] using hu.2)
    · have hz : (fun t => K t u) = fun _ => (0:ℝ≥0∞) := by
        funext t
        simp [K, unitSchurKernelENN, hu]
      rw [hz]
      simp
  have hcolMeas : ∀ u, AEMeasurable (fun t => K t u) μ := by
    intro u
    exact (hKM.comp measurable_prodMk_right).aemeasurable
  have hPGuncurry : AEMeasurable (Function.uncurry (fun t u => K t u * G u))
      (μ.prod μ) := by
    convert hPG.aemeasurable using 1 <;> ext z <;> rfl
  have hswap := lintegral_lintegral_swap hPGuncurry
  have hmass : (∫⁻ t, ∫⁻ u, K t u * G u ∂μ ∂μ) ≤
      ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) * (∫⁻ u, G u ∂μ) := by
    rw [hswap]
    calc
      (∫⁻ u, ∫⁻ t, K t u * G u ∂μ ∂μ) ≤
          ∫⁻ u, ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) * G u ∂μ := by
        apply lintegral_mono
        intro u
        change (∫⁻ t, K t u * G u ∂μ) ≤ _
        rw [lintegral_mul_const'' _ (hcolMeas u)]
        exact mul_le_mul_of_nonneg_right (hcolumn u) (by positivity)
      _ = ENNReal.ofReal ((Real.Gamma (β+1))⁻¹) * (∫⁻ u, G u ∂μ) := by
        rw [lintegral_const_mul'' _ hG.aemeasurable]
  have hfinite : (∫⁻ z, K z.1 z.2 * G z.2 ∂(μ.prod μ)) < ⊤ := by
    have hprod : (∫⁻ z, K z.1 z.2 * G z.2 ∂(μ.prod μ)) =
        ∫⁻ t, ∫⁻ u, K t u * G u ∂μ ∂μ := by
      calc
        _ = ∫⁻ z, Function.uncurry (fun t u => K t u * G u) z ∂(μ.prod μ) := by rfl
        _ = ∫⁻ t, ∫⁻ u, K t u * G u ∂μ ∂μ := lintegral_prod _ hPGuncurry
    rw [hprod]
    apply lt_of_le_of_lt hmass
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG1
  let F : ℝ × ℝ → ℝ := fun z =>
    if z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval then
      schurKernel β z.1 z.2 * |f z.2| else 0
  have hFmeas : Measurable F := by
    have hs : MeasurableSet {z : ℝ × ℝ | z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval} := by
      exact (measurableSet_Icc.preimage measurable_fst).inter
        (measurableSet_Icc.preimage measurable_snd)
    have hkernel : Measurable (Function.uncurry (fun t u => schurKernel β t u)) := by
      have hm := ENNReal.measurable_toReal.comp (schurKernel_measurable β)
      have heq : (fun z : ℝ × ℝ => (schurKernelENN β z.1 z.2).toReal) =
          Function.uncurry (fun t u => schurKernel β t u) := by
        funext z
        rw [schurKernelENN, ENNReal.toReal_ofReal (schurKernel_nonneg hβ)]
        rfl
      rw [← heq]
      exact hm
    exact Measurable.ite hs (hkernel.mul (hf.norm.comp measurable_snd))
      measurable_const
  have hnormeq : (fun z : ℝ × ℝ => ENNReal.ofReal ‖F z‖) =
      (fun z => K z.1 z.2 * G z.2) := by
    funext z
    by_cases hz : z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval
    · have ht : z.1 ∈ UnitInterval := hz.1
      have hu : z.2 ∈ UnitInterval := hz.2
      have hz' : ((0:ℝ) ≤ z.1 ∧ z.1 ≤ 1) ∧ (0:ℝ) ≤ z.2 ∧ z.2 ≤ 1 := by
        simpa [UnitInterval] using hz
      simp only [F, if_pos hz, K, G, unitSchurKernelENN, if_pos hz']
      have hk : 0 ≤ schurKernel β z.1 z.2 := schurKernel_nonneg hβ
      have hmul : 0 ≤ schurKernel β z.1 z.2 * |f z.2| :=
        mul_nonneg hk (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hmul, schurKernelENN,
        ENNReal.ofReal_mul hk]
    · have hz' : ¬(z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval) := hz
      simp only [UnitInterval, Set.mem_Icc] at hz'
      simp [F, K, G, unitSchurKernelENN, UnitInterval, hz']
  have hnormfinite : (∫⁻ z, ENNReal.ofReal ‖F z‖ ∂(μ.prod μ)) < ⊤ := by
    rw [show (fun z : ℝ × ℝ => ENNReal.ofReal ‖F z‖) =
      (fun z => K z.1 z.2 * G z.2) from hnormeq]
    exact hfinite
  have hfi : HasFiniteIntegral (fun z => ‖F z‖) (μ.prod μ) :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => norm_nonneg (F z))).2
      hnormfinite
  have hnormint : Integrable (fun z => ‖F z‖) (μ.prod μ) :=
    ⟨hFmeas.norm.aestronglyMeasurable, hfi⟩
  exact (integrable_norm_iff hFmeas.aestronglyMeasurable).mp hnormint

/-- Real-valued kernel on the unit square, extended by zero to the ambient
product space. -/
def unitSchurKernelReal (β t u : ℝ) : ℝ :=
  if t ∈ UnitInterval ∧ u ∈ UnitInterval then schurKernel β t u else 0

theorem unitSchurKernelReal_measurable {β : ℝ} (hβ : 0 < β) :
    Measurable (Function.uncurry (fun t u => unitSchurKernelReal β t u)) := by
  have hs : MeasurableSet {z : ℝ × ℝ | z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval} := by
    exact (measurableSet_Icc.preimage measurable_fst).inter
      (measurableSet_Icc.preimage measurable_snd)
  have hk : Measurable (Function.uncurry (fun t u => schurKernel β t u)) := by
    have hm := ENNReal.measurable_toReal.comp (schurKernel_measurable β)
    have heq : (fun z : ℝ × ℝ => (schurKernelENN β z.1 z.2).toReal) =
        Function.uncurry (fun t u => schurKernel β t u) := by
      funext z
      have hn : 0 ≤ schurKernel β z.1 z.2 := schurKernel_nonneg hβ
      rw [schurKernelENN, ENNReal.toReal_ofReal hn]
      rfl
    rw [← heq]
    exact hm
  unfold unitSchurKernelReal
  exact Measurable.ite hs hk measurable_const

/-- Signed kernel action on a measurable representative. The product
integrability theorem ensures this is the Bochner integral for almost every
target point. -/
noncomputable def causalKernelSignedAction (β : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u, unitSchurKernelReal β t u * f u ∂(volume.restrict UnitInterval)

/-- Product-space integrability of the signed kernel-input function. -/
theorem causalKernel_signed_product_integrable {β : ℝ} (hβ : 0 < β)
    (f : ℝ → ℝ) (hf : Measurable f)
    (henergy : (∫⁻ u, (ENNReal.ofReal (|f u|))^2
      ∂(volume.restrict UnitInterval)) < ⊤) :
    Integrable (fun z : ℝ × ℝ => unitSchurKernelReal β z.1 z.2 * f z.2)
      ((volume.restrict UnitInterval).prod (volume.restrict UnitInterval)) := by
  have habs := causalKernel_abs_product_integrable hβ f hf henergy
  have hsm : AEStronglyMeasurable
      (fun z : ℝ × ℝ => unitSchurKernelReal β z.1 z.2 * f z.2)
      ((volume.restrict UnitInterval).prod (volume.restrict UnitInterval)) := by
    exact (unitSchurKernelReal_measurable hβ).mul (hf.comp measurable_snd) |>.aestronglyMeasurable
  have hnorm : (fun z : ℝ × ℝ =>
      ‖unitSchurKernelReal β z.1 z.2 * f z.2‖) =
      (fun z => if z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval then
        schurKernel β z.1 z.2 * |f z.2| else 0) := by
    funext z
    by_cases hz : z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval
    · have hk : 0 ≤ schurKernel β z.1 z.2 := schurKernel_nonneg hβ
      simp [unitSchurKernelReal, hz, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg hk]
    · have hz' : ¬(((0:ℝ) ≤ z.1 ∧ z.1 ≤ 1) ∧ ((0:ℝ) ≤ z.2 ∧ z.2 ≤ 1)) := by
        simpa [UnitInterval] using hz
      simp [unitSchurKernelReal, UnitInterval, hz']
  have habs' : Integrable (fun z : ℝ × ℝ =>
      if z.1 ∈ UnitInterval ∧ z.2 ∈ UnitInterval then
        schurKernel β z.1 z.2 * |f z.2| else 0)
      ((volume.restrict UnitInterval).prod (volume.restrict UnitInterval)) := by
    exact habs
  have hnormint : Integrable
      (fun z : ℝ × ℝ => ‖unitSchurKernelReal β z.1 z.2 * f z.2‖)
      ((volume.restrict UnitInterval).prod (volume.restrict UnitInterval)) := by
    rw [hnorm]
    exact habs'
  exact (integrable_norm_iff hsm).1 hnormint

/-- The signed Volterra action is an L² target function for every measurable
L² input. This is a representative-level boundedness result; linearity on Lp
classes is a separate a.e.-invariance packaging step. -/
theorem causalKernelSignedAction_memLp {β : ℝ} (hβ : 0 < β)
    (f : ℝ → ℝ) (hf : Measurable f)
    (henergy : (∫⁻ u, (ENNReal.ofReal (|f u|))^2
      ∂(volume.restrict UnitInterval)) < ⊤) :
    MemLp (causalKernelSignedAction β f) 2 (volume.restrict UnitInterval) ∧
      (∫⁻ t, ENNReal.ofReal ((causalKernelSignedAction β f t)^2)
        ∂(volume.restrict UnitInterval)) ≤
        ENNReal.ofReal ((Real.Gamma (β+1))⁻¹)^2 *
          (∫⁻ u, (ENNReal.ofReal (|f u|))^2 ∂(volume.restrict UnitInterval)) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  let F : ℝ × ℝ → ℝ := fun z => unitSchurKernelReal β z.1 z.2 * f z.2
  have hFmeas : Measurable F := by
    exact (unitSchurKernelReal_measurable hβ).mul (hf.comp measurable_snd)
  have hF : Integrable F (μ.prod μ) := by
    simpa [F, μ] using causalKernel_signed_product_integrable hβ f hf henergy
  have hmeas : Measurable (causalKernelSignedAction β f) := by
    change Measurable (fun t => ∫ u, F (t,u) ∂μ)
    exact (hFmeas.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hsections : ∀ᵐ t ∂μ, Integrable (fun u => F (t,u)) μ := hF.prod_right_ae
  let G : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (|f u|)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp hf.norm
  have hGenergy : (∫⁻ u, G u^2 ∂μ) < ⊤ := by
    simpa [G, μ] using henergy
  have hAmpMem := causalKernelAmplitude_memLp hβ G hG hGenergy
  have hAmpMeas : Measurable (causalKernelAmplitude β G) := by
    have hm := (unitSchurKernelENN_measurable β).mul (hG.comp measurable_snd)
    exact hm.lintegral_prod_right
  have hAmpSq : (∫⁻ t, (causalKernelAmplitude β G t)^2 ∂μ) ≤
      ENNReal.ofReal ((Real.Gamma (β+1))⁻¹)^2 * (∫⁻ u, G u^2 ∂μ) := by
    simpa [μ, causalKernelAmplitude, pow_two, mul_assoc] using
      causalKernel_lintegral_sq_bound hβ G hG
  have hAmpSqTop : (∫⁻ t, (causalKernelAmplitude β G t)^2 ∂μ) < ⊤ := by
    apply lt_of_le_of_lt hAmpSq
    exact ENNReal.mul_lt_top
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hGenergy
  have hAmpTop : ∀ᵐ t ∂μ, causalKernelAmplitude β G t < ⊤ := by
    have hsqtop : ∀ᵐ t ∂μ, (causalKernelAmplitude β G t)^2 < ⊤ :=
      ae_lt_top' (hAmpMeas.pow_const 2).aemeasurable hAmpSqTop.ne
    filter_upwards [hsqtop] with t ht
    exact (ENNReal.pow_lt_top_iff.mp ht).resolve_right (by norm_num)
  have hpoint : ∀ᵐ t ∂μ,
      ENNReal.ofReal (|causalKernelSignedAction β f t|) ≤ causalKernelAmplitude β G t := by
    filter_upwards [hsections, hAmpTop, ae_restrict_mem measurableSet_Icc] with t ht htop htu
    have hsectionNorm : (∫⁻ u, ENNReal.ofReal
        ‖F (t,u)‖ ∂μ) = causalKernelAmplitude β G t := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have hu' : (0:ℝ) ≤ u ∧ u ≤ 1 := by simpa [UnitInterval] using hu
      have ht' : (0:ℝ) ≤ t ∧ t ≤ 1 := by simpa [UnitInterval] using htu
      have hk : 0 ≤ schurKernel β t u := schurKernel_nonneg hβ
      calc
        ENNReal.ofReal ‖F (t,u)‖ = ENNReal.ofReal
            |schurKernel β t u * f u| := by
          simp [F, unitSchurKernelReal, UnitInterval, ht', hu', Real.norm_eq_abs]
        _ = ENNReal.ofReal (schurKernel β t u * |f u|) := by
          rw [abs_mul, abs_of_nonneg hk]
        _ = ENNReal.ofReal (schurKernel β t u) * ENNReal.ofReal |f u| :=
          ENNReal.ofReal_mul hk
        _ = unitSchurKernelENN β t u * G u := by
          simp [unitSchurKernelENN, schurKernelENN, G, UnitInterval, ht', hu']
    have hnormle := enorm_integral_le_lintegral_enorm (μ := μ) (fun u => F (t,u))
    have hnormcast : ‖∫ u, F (t,u) ∂μ‖ₑ =
        ENNReal.ofReal (|causalKernelSignedAction β f t|) := by
      have hI : (∫ u, F (t,u) ∂μ) = causalKernelSignedAction β f t := rfl
      rw [hI]
      exact Real.enorm_eq_ofReal_abs _
    have hnormeq : (fun u => ‖F (t,u)‖ₑ) =
        (fun u => ENNReal.ofReal ‖F (t,u)‖) := by
      funext u
      simpa [Real.enorm_abs] using
        (Real.enorm_eq_ofReal (abs_nonneg (F (t,u))))
    rw [hnormcast, hnormeq, hsectionNorm] at hnormle
    exact hnormle
  have hAmpBound : (∫⁻ t, ENNReal.ofReal
      ((causalKernelSignedAction β f t)^2) ∂μ) ≤
      ENNReal.ofReal ((Real.Gamma (β+1))⁻¹)^2 * (∫⁻ u, G u^2 ∂μ) := by
    have hb := causalKernelAmplitude_energy_le hβ G hG hGenergy
    have hAEbound : ∀ᵐ t ∂μ, ENNReal.ofReal
        ((causalKernelSignedAction β f t)^2) ≤ ENNReal.ofReal
        ((causalKernelAmplitude β G t).toReal^2) := by
      filter_upwards [hpoint, hAmpTop] with t hp ht
      have hto : |causalKernelSignedAction β f t| ≤
          (causalKernelAmplitude β G t).toReal := by
        exact (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt ht)).mp hp
      have hsq : (causalKernelSignedAction β f t)^2 ≤
          (causalKernelAmplitude β G t).toReal^2 := by
        calc
          (causalKernelSignedAction β f t)^2 =
              |causalKernelSignedAction β f t| * |causalKernelSignedAction β f t| := by
                rw [← sq_abs]
                ring
          _ ≤ (causalKernelAmplitude β G t).toReal *
              |causalKernelSignedAction β f t| :=
                mul_le_mul_of_nonneg_right hto (abs_nonneg _)
          _ ≤ (causalKernelAmplitude β G t).toReal *
              (causalKernelAmplitude β G t).toReal :=
                mul_le_mul_of_nonneg_left hto (ENNReal.toReal_nonneg)
          _ = (causalKernelAmplitude β G t).toReal^2 := by ring
      exact ENNReal.ofReal_le_ofReal hsq
    have hmono := lintegral_mono_ae hAEbound
    calc
      (∫⁻ t, ENNReal.ofReal ((causalKernelSignedAction β f t)^2) ∂μ) ≤
          ∫⁻ t, ENNReal.ofReal ((causalKernelAmplitude β G t).toReal^2) ∂μ := hmono
      _ ≤ ENNReal.ofReal ((Real.Gamma (β+1))⁻¹)^2 * (∫⁻ u, G u^2 ∂μ) := hb
  have hAmpFinite : (∫⁻ t, ENNReal.ofReal
      ((causalKernelSignedAction β f t)^2) ∂μ) < ⊤ := by
    apply lt_of_le_of_lt hAmpBound
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hGenergy
  have hsqmeas : AEStronglyMeasurable (fun t =>
      (causalKernelSignedAction β f t)^2) μ :=
    (hmeas.pow_const 2).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[μ] (fun t => (causalKernelSignedAction β f t)^2) :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hfi : HasFiniteIntegral (fun t => (causalKernelSignedAction β f t)^2) μ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).2 hAmpFinite
  have hint : Integrable (fun t => (causalKernelSignedAction β f t)^2) μ :=
    ⟨hsqmeas, hfi⟩
  refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hint, ?_⟩
  simpa [G, μ] using hAmpBound

open BrownianSharp.AlignmentFractionalL2

/-- Choose a measurable representative of a unit-interval L² class. -/
noncomputable def unitL2MeasurableRep (g : UnitL2) : ℝ → ℝ :=
  (Lp.memLp g).aestronglyMeasurable.aemeasurable.mk (g : ℝ → ℝ)

theorem unitL2MeasurableRep_ae (g : UnitL2) :
    unitL2MeasurableRep g =ᵐ[volume.restrict UnitInterval] (g : ℝ → ℝ) :=
  (Lp.memLp g).aestronglyMeasurable.aemeasurable.ae_eq_mk.symm

theorem unitL2MeasurableRep_measurable (g : UnitL2) :
    Measurable (unitL2MeasurableRep g) :=
  (Lp.memLp g).aestronglyMeasurable.aemeasurable.measurable_mk

theorem unitL2MeasurableRep_memLp (g : UnitL2) :
    MemLp (unitL2MeasurableRep g) 2 (volume.restrict UnitInterval) := by
  exact (memLp_congr_ae (unitL2MeasurableRep_ae g)).2 (Lp.memLp g)

theorem unitL2MeasurableRep_energy_lt_top (g : UnitL2) :
    (∫⁻ u, (ENNReal.ofReal (|unitL2MeasurableRep g u|))^2
      ∂(volume.restrict UnitInterval)) < ⊤ := by
  have hrep := unitL2MeasurableRep_memLp g
  have hint : Integrable (fun u : ℝ => (unitL2MeasurableRep g u)^2)
      (volume.restrict UnitInterval) :=
    (memLp_two_iff_integrable_sq hrep.aestronglyMeasurable).1 hrep
  have hnonneg : 0 ≤ᵐ[volume.restrict UnitInterval]
      (fun u : ℝ => (unitL2MeasurableRep g u)^2) :=
    Filter.Eventually.of_forall fun u => sq_nonneg _
  have hfinite := (hasFiniteIntegral_iff_ofReal hnonneg).1 hint.hasFiniteIntegral
  calc
    (∫⁻ u, (ENNReal.ofReal (|unitL2MeasurableRep g u|))^2 ∂(volume.restrict UnitInterval))
        = ∫⁻ u, ENNReal.ofReal ((unitL2MeasurableRep g u)^2) ∂(volume.restrict UnitInterval) := by
          apply lintegral_congr_ae
          filter_upwards [] with u
          rw [← ENNReal.ofReal_pow (abs_nonneg _)]
          simp [abs_sq]
    _ < ⊤ := hfinite

theorem unitL2MeasurableRep_add_ae (f g : UnitL2) :
    unitL2MeasurableRep (f+g) =ᵐ[volume.restrict UnitInterval]
      unitL2MeasurableRep f + unitL2MeasurableRep g := by
  have h := Lp.coeFn_add f g
  filter_upwards [unitL2MeasurableRep_ae (f+g),
    unitL2MeasurableRep_ae f, unitL2MeasurableRep_ae g, h] with u hsum hf hg hfg
  change unitL2MeasurableRep (f+g) u =
    unitL2MeasurableRep f u + unitL2MeasurableRep g u
  rw [hsum, hf, hg, hfg]
  simp

theorem unitL2MeasurableRep_smul_ae (c : ℝ) (f : UnitL2) :
    unitL2MeasurableRep (c • f) =ᵐ[volume.restrict UnitInterval]
      c • unitL2MeasurableRep f := by
  have h := Lp.coeFn_smul c f
  filter_upwards [unitL2MeasurableRep_ae (c • f),
    unitL2MeasurableRep_ae f, h] with u hcf hf h
  change unitL2MeasurableRep (c • f) u = c * unitL2MeasurableRep f u
  rw [hcf, hf, h]
  simp

/-- For almost every target point, the signed Volterra action is additive in
its measurable input representatives. -/
theorem causalKernelSignedAction_add_ae {β : ℝ} (hβ : 0 < β)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfe : (∫⁻ u, (ENNReal.ofReal (|f u|))^2 ∂(volume.restrict UnitInterval)) < ⊤)
    (hge : (∫⁻ u, (ENNReal.ofReal (|g u|))^2 ∂(volume.restrict UnitInterval)) < ⊤) :
    causalKernelSignedAction β (f+g) =ᵐ[volume.restrict UnitInterval]
      causalKernelSignedAction β f + causalKernelSignedAction β g := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  have hfp := causalKernel_signed_product_integrable hβ f hf hfe
  have hgp := causalKernel_signed_product_integrable hβ g hg hge
  have hfsec : ∀ᵐ t ∂μ, Integrable (fun u =>
      unitSchurKernelReal β t u * f u) μ := by
    exact hfp.prod_right_ae
  have hgsec : ∀ᵐ t ∂μ, Integrable (fun u =>
      unitSchurKernelReal β t u * g u) μ := by
    exact hgp.prod_right_ae
  filter_upwards [hfsec, hgsec] with t hft hgt
  calc
    ∫ u, unitSchurKernelReal β t u * (f u + g u) ∂μ =
        ∫ u, (unitSchurKernelReal β t u * f u +
          unitSchurKernelReal β t u * g u) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with u
            ring
    _ = (∫ u, unitSchurKernelReal β t u * f u ∂μ) +
        (∫ u, unitSchurKernelReal β t u * g u ∂μ) := integral_add hft hgt

theorem causalKernelSignedAction_smul_ae {β : ℝ} (hβ : 0 < β)
    (c : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hfe : (∫⁻ u, (ENNReal.ofReal (|f u|))^2 ∂(volume.restrict UnitInterval)) < ⊤) :
    causalKernelSignedAction β (c • f) =ᵐ[volume.restrict UnitInterval]
      c • causalKernelSignedAction β f := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  have hfp := causalKernel_signed_product_integrable hβ f hf hfe
  have hfsec : ∀ᵐ t ∂μ, Integrable (fun u =>
      unitSchurKernelReal β t u * f u) μ := hfp.prod_right_ae
  filter_upwards [hfsec] with t hft
  change ∫ u, unitSchurKernelReal β t u * (c • f u) ∂μ =
    c * (∫ u, unitSchurKernelReal β t u * f u ∂μ)
  calc
    ∫ u, unitSchurKernelReal β t u * (c • f u) ∂μ =
        ∫ u, c • (unitSchurKernelReal β t u * f u) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with u
          simp only [smul_eq_mul]
          ring
    _ = c * (∫ u, unitSchurKernelReal β t u * f u ∂μ) := by
          rw [integral_smul]
          simp [smul_eq_mul]

theorem causalKernelSignedAction_congr_ae {β : ℝ} (hβ : 0 < β)
    (f g : ℝ → ℝ) (hfg : f =ᵐ[volume.restrict UnitInterval] g) :
    causalKernelSignedAction β f = causalKernelSignedAction β g := by
  funext t
  unfold causalKernelSignedAction
  apply integral_congr_ae
  filter_upwards [hfg] with u hu
  rw [hu]

/-- The causal signed integral action, represented as an L² equivalence class. -/
noncomputable def causalKernelL2Action (β : ℝ) (hβ : 0 < β) (g : UnitL2) : UnitL2 := by
  let f := unitL2MeasurableRep g
  exact (causalKernelSignedAction_memLp hβ f (unitL2MeasurableRep_measurable g)
    (unitL2MeasurableRep_energy_lt_top g)).1.toLp
    (causalKernelSignedAction β f)

/-- For orders above one half, the Schur representative-level action is the
same L² operator as the continuous-profile RL map. This identifies the
almost-everywhere integral construction with the canonical bounded operator. -/
theorem causalKernelL2Action_eq_fractionalRLOnL2 {β : ℝ} (hβ : 1/2 < β)
    (g : UnitL2) :
    causalKernelL2Action β (by linarith) g =
      AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 β hβ g := by
  let hOut := (causalKernelSignedAction_memLp (by linarith : 0 < β)
    (unitL2MeasurableRep g) (unitL2MeasurableRep_measurable g)
    (unitL2MeasurableRep_energy_lt_top g)).1
  have hact : causalKernelSignedAction β (unitL2MeasurableRep g) =ᵐ[
      volume.restrict UnitInterval]
      fun t => fractionalRL β hβ g (clipUnit t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hk : ∀ᵐ u ∂(volume.restrict UnitInterval),
        unitSchurKernelReal β t u = causalKernel β t u := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have hu0 : 0 ≤ u := hu.1
      have hu1 : u ≤ 1 := hu.2
      simp [unitSchurKernelReal, UnitInterval, schurKernel, ht0, ht1, hu0, hu1]
    have hi : (∫ u, unitSchurKernelReal β t u * unitL2MeasurableRep g u ∂
        (volume.restrict UnitInterval)) =
        ∫ u, causalKernel β t u * g u ∂(volume.restrict UnitInterval) := by
      apply integral_congr_ae
      filter_upwards [hk, unitL2MeasurableRep_ae g] with u hk hu
      rw [hk, hu]
    change (∫ u, unitSchurKernelReal β t u * unitL2MeasurableRep g u ∂
      (volume.restrict UnitInterval)) = _
    rw [hi]
    have hclip : clipUnit t = ⟨t, ⟨ht0, ht1⟩⟩ := by
      apply Subtype.ext
      simp [clipUnit, ht0, ht1]
    rw [hclip, fractionalRL_apply β hβ g t ht0 ht1]
  unfold causalKernelL2Action
  change hOut.toLp (causalKernelSignedAction β (unitL2MeasurableRep g)) =
    AlignmentFractionalDensity.profileToL2 (fractionalRL β hβ g)
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp hOut,
    AlignmentFractionalDensity.profileToL2_coe (fractionalRL β hβ g), hact,
    ae_restrict_mem measurableSet_Icc] with t hout hprofile hval ht
  exact hout.trans (hval.trans (hprofile.symm))

/-- The actual fractional Volterra map as a linear map on L² classes. -/
noncomputable def causalKernelL2Linear (β : ℝ) (hβ : 0 < β) :
    UnitL2 →ₗ[ℝ] UnitL2 where
  toFun := causalKernelL2Action β hβ
  map_add' := by
    intro f g
    let hf := unitL2MeasurableRep_memLp f
    let hg := unitL2MeasurableRep_memLp g
    let houtf := (causalKernelSignedAction_memLp hβ (unitL2MeasurableRep f)
      (unitL2MeasurableRep_measurable f) (unitL2MeasurableRep_energy_lt_top f)).1
    let houtg := (causalKernelSignedAction_memLp hβ (unitL2MeasurableRep g)
      (unitL2MeasurableRep_measurable g) (unitL2MeasurableRep_energy_lt_top g)).1
    let houts := (causalKernelSignedAction_memLp hβ (unitL2MeasurableRep (f+g))
      (unitL2MeasurableRep_measurable (f+g))
      (unitL2MeasurableRep_energy_lt_top (f+g))).1
    have hact : causalKernelSignedAction β (unitL2MeasurableRep (f+g)) =ᵐ[
        volume.restrict UnitInterval]
        causalKernelSignedAction β (unitL2MeasurableRep f) +
          causalKernelSignedAction β (unitL2MeasurableRep g) := by
      calc
        causalKernelSignedAction β (unitL2MeasurableRep (f+g)) =
            causalKernelSignedAction β
              (unitL2MeasurableRep f + unitL2MeasurableRep g) := by
                apply causalKernelSignedAction_congr_ae hβ
                exact unitL2MeasurableRep_add_ae f g
        _ =ᵐ[volume.restrict UnitInterval]
            causalKernelSignedAction β (unitL2MeasurableRep f) +
              causalKernelSignedAction β (unitL2MeasurableRep g) :=
                causalKernelSignedAction_add_ae hβ _ _
                  (unitL2MeasurableRep_measurable f)
                  (unitL2MeasurableRep_measurable g)
                  (unitL2MeasurableRep_energy_lt_top f)
                  (unitL2MeasurableRep_energy_lt_top g)
    change houts.toLp (causalKernelSignedAction β (unitL2MeasurableRep (f+g))) =
      houtf.toLp (causalKernelSignedAction β (unitL2MeasurableRep f)) +
        houtg.toLp (causalKernelSignedAction β (unitL2MeasurableRep g))
    rw [← MemLp.toLp_add houtf houtg]
    apply MemLp.toLp_congr
    exact hact
  map_smul' := by
    intro c f
    let houtf := (causalKernelSignedAction_memLp hβ (unitL2MeasurableRep f)
      (unitL2MeasurableRep_measurable f) (unitL2MeasurableRep_energy_lt_top f)).1
    let houts := (causalKernelSignedAction_memLp hβ (unitL2MeasurableRep (c • f))
      (unitL2MeasurableRep_measurable (c • f))
      (unitL2MeasurableRep_energy_lt_top (c • f))).1
    have hact : causalKernelSignedAction β (unitL2MeasurableRep (c • f)) =ᵐ[
        volume.restrict UnitInterval]
        c • causalKernelSignedAction β (unitL2MeasurableRep f) := by
      calc
        causalKernelSignedAction β (unitL2MeasurableRep (c • f)) =
            causalKernelSignedAction β (c • unitL2MeasurableRep f) := by
                apply causalKernelSignedAction_congr_ae hβ
                exact unitL2MeasurableRep_smul_ae c f
        _ =ᵐ[volume.restrict UnitInterval]
            c • causalKernelSignedAction β (unitL2MeasurableRep f) :=
              causalKernelSignedAction_smul_ae hβ c _
                (unitL2MeasurableRep_measurable f)
                (unitL2MeasurableRep_energy_lt_top f)
    change houts.toLp (causalKernelSignedAction β (unitL2MeasurableRep (c • f))) =
      c • houtf.toLp (causalKernelSignedAction β (unitL2MeasurableRep f))
    rw [← MemLp.toLp_const_smul c houtf]
    apply MemLp.toLp_congr
    exact hact

end BrownianSharp.AlignmentFractionalL2Schur
