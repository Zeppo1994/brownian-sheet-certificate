import BrownianSharp.AlignmentMaternSpectralFeature
import BrownianSharp.AlignmentMaternScalarFeature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
Finite spectral-window calculations for the one-dimensional Matérn feature.
The feature phase convention is `(cos (2π ξ t), sin (2π ξ t))`, so windows
are centered at integer frequencies.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped InnerProductSpace

namespace BrownianSharp.AlignmentMaternSpectralWindow

def window (k : ℤ) (a : ℝ) : Set ℝ := Set.Icc ((k : ℝ) - a / 2) ((k : ℝ) + a / 2)

theorem window_disjoint_of_integer_centers (k l : ℤ) (a : ℝ)
    (ha : a < 1) (hne : k ≠ l) : Disjoint (window k a) (window l a) := by
  rw [Set.disjoint_left]
  intro ξ hk hl
  have hsepZ : 1 ≤ |k - l| := Int.one_le_abs (sub_ne_zero.mpr hne)
  have hsep : 1 ≤ |(k : ℝ) - (l : ℝ)| := by
    exact_mod_cast hsepZ
  have hdist : |(k : ℝ) - (l : ℝ)| ≤ a := by
    have hkabs : |ξ - (k : ℝ)| ≤ a / 2 := by
      rw [abs_le]
      constructor <;> linarith [hk.1, hk.2]
    have hlabs : |ξ - (l : ℝ)| ≤ a / 2 := by
      rw [abs_le]
      constructor <;> linarith [hl.1, hl.2]
    calc
      |(k : ℝ) - (l : ℝ)| = |((k : ℝ) - ξ) + (ξ - (l : ℝ))| := by congr 1; ring
      _ ≤ |(k : ℝ) - ξ| + |ξ - (l : ℝ)| := abs_add_le _ _
      _ = |ξ - (k : ℝ)| + |ξ - (l : ℝ)| := by rw [abs_sub_comm]
      _ ≤ a := by linarith [hkabs, hlabs]
  linarith

def windowMultiplier (a t : ℝ) : ℝ :=
  if t = 0 then a else Real.sin (Real.pi * a * t) / (Real.pi * t)

theorem abs_frequency_le_window (k : ℤ) (a ξ : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hξ : ξ ∈ window k a) :
    |ξ| ≤ |(k : ℝ)| + 1 := by
  have hd : |ξ - (k : ℝ)| ≤ a / 2 := by
    rw [abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  calc
    |ξ| = |(ξ - (k : ℝ)) + (k : ℝ)| := by congr 1; ring
    _ ≤ |ξ - (k : ℝ)| + |(k : ℝ)| := abs_add_le _ _
    _ ≤ a / 2 + |(k : ℝ)| := by linarith [hd]
    _ ≤ |(k : ℝ)| + 1 := by linarith

theorem density_inv_le_window_bound (κ h : ℝ) (k : ℤ) (a ξ : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hξ : ξ ∈ window k a) :
    (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ ≤
      Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
  let s := h + 1 / 2
  let K := κ ^ 2 + (|(k : ℝ)| + 1) ^ 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hbase : 0 < κ ^ 2 + ξ ^ 2 := by positivity
  have hfreq := abs_frequency_le_window k a ξ ha0 ha1 hξ
  have hsq : |ξ| ^ 2 ≤ (|(k : ℝ)| + 1) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg ξ) (by positivity)).2 hfreq
  have hbasele : κ ^ 2 + ξ ^ 2 ≤ K := by
    dsimp [K]
    simpa [sq_abs] using add_le_add_left hsq (κ ^ 2)
  have hinv : (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ =
      Real.rpow (κ ^ 2 + ξ ^ 2) s := by
    rw [AlignmentMaternSpectralFeature.density]
    change ((κ ^ 2 + ξ ^ 2).rpow (-(h + 1 / 2)))⁻¹ = _
    have hr : (κ ^ 2 + ξ ^ 2).rpow (-(h + 1 / 2)) =
        ((κ ^ 2 + ξ ^ 2).rpow (h + 1 / 2))⁻¹ :=
      Real.rpow_neg (by positivity) (h + 1 / 2)
    rw [hr, inv_inv]
  rw [hinv]
  exact Real.rpow_le_rpow (by positivity) hbasele (by linarith)

/-- Uniform polynomial tail of the Matérn density on a short window.  This
is the measure-side estimate needed to turn the pointwise source envelope
into the sharp Sobolev-frequency L² cost. -/
theorem density_le_frequency_tail_on_window (κ h : ℝ) (k : ℤ) (a ξ : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hξ : ξ ∈ window k a) :
    AlignmentMaternSpectralFeature.density κ h ξ ≤
      Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)) := by
  let s := h + 1 / 2
  let m := min 1 (κ ^ 2)
  have hs : 0 < s := by dsimp [s]; linarith
  have hm0 : 0 < m := by
    dsimp [m]
    exact lt_min (by norm_num) (sq_pos_of_pos hκ)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmk : m ≤ κ ^ 2 := min_le_right _ _
  have hd : |ξ - (k : ℝ)| ≤ a / 2 := by
    rw [abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  have hfreq : |(k : ℝ)| ≤ |ξ| + 1 / 2 := by
    calc
      |(k : ℝ)| = |((k : ℝ) - ξ) + ξ| := by congr 1; ring
      _ ≤ |(k : ℝ) - ξ| + |ξ| := abs_add_le _ _
      _ = |ξ - (k : ℝ)| + |ξ| := by rw [abs_sub_comm]
      _ ≤ a / 2 + |ξ| := by linarith [hd]
      _ ≤ |ξ| + 1 / 2 := by linarith
  have hksq : (k : ℝ) ^ 2 ≤ 2 * ξ ^ 2 + 1 / 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (k : ℝ)) (by positivity)).2 hfreq
    nlinarith [sq_abs ξ, sq_abs (k : ℝ), sq_nonneg (|ξ| - 1 / 2)]
  have hmkxi : m * ξ ^ 2 ≤ ξ ^ 2 := by
    calc
      m * ξ ^ 2 ≤ 1 * ξ ^ 2 := mul_le_mul_of_nonneg_right hm1 (sq_nonneg ξ)
      _ = ξ ^ 2 := by ring
  have hlow : m / 2 * (1 + (k : ℝ) ^ 2) ≤ κ ^ 2 + ξ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hksq hm0.le, hmkxi, hmk]
  have hbase : 0 < κ ^ 2 + ξ ^ 2 := by positivity
  have hsmall : 0 < m / 2 * (1 + (k : ℝ) ^ 2) := by positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hsmall hlow (by linarith : -s ≤ 0)
  have hfactor : Real.rpow (m / 2 * (1 + (k : ℝ) ^ 2)) (-s) =
      Real.rpow (m / 2) (-s) * Real.rpow (1 + (k : ℝ) ^ 2) (-s) :=
    Real.mul_rpow (le_of_lt (by positivity)) (by positivity)
  rw [AlignmentMaternSpectralFeature.density]
  change Real.rpow (κ ^ 2 + ξ ^ 2) (-s) ≤ _
  calc
    Real.rpow (κ ^ 2 + ξ ^ 2) (-s) ≤
        Real.rpow (m / 2 * (1 + (k : ℝ) ^ 2)) (-s) := hpow
    _ = Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)) := by
          simpa [s, m] using hfactor

theorem spectralMeasure_window_le (κ h : ℝ) (k : ℤ) (a : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    AlignmentMaternSpectralFeature.spectralMeasure κ h (window k a) ≤
      ENNReal.ofReal (a *
        (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) := by
  let D := Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
      Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDξ (ξ : ℝ) (hξ : ξ ∈ window k a) :
      ENNReal.ofReal (AlignmentMaternSpectralFeature.density κ h ξ) ≤ ENNReal.ofReal D := by
    apply ENNReal.ofReal_le_ofReal
    simpa [D] using density_le_frequency_tail_on_window κ h k a ξ hκ hh ha0 ha1 hξ
  have hs : MeasurableSet (window k a) := measurableSet_Icc
  rw [show AlignmentMaternSpectralFeature.spectralMeasure κ h =
      volume.withDensity (fun ξ => ENNReal.ofReal
        (AlignmentMaternSpectralFeature.density κ h ξ)) by rfl]
  rw [withDensity_apply _ hs]
  calc
    ∫⁻ ξ in window k a, ENNReal.ofReal (AlignmentMaternSpectralFeature.density κ h ξ)
        ∂volume = ∫⁻ ξ, (window k a).indicator
          (fun ξ => ENNReal.ofReal (AlignmentMaternSpectralFeature.density κ h ξ)) ξ ∂volume := by
          rw [lintegral_indicator hs]
    _ ≤ ∫⁻ ξ, (window k a).indicator (fun _ : ℝ => ENNReal.ofReal D) ξ ∂volume := by
          apply lintegral_mono
          intro ξ
          by_cases hx : ξ ∈ window k a
          · simpa [hx] using hDξ ξ hx
          · simp [hx]
    _ = ENNReal.ofReal D * volume (window k a) := by
          rw [lintegral_indicator_const hs]
    _ = ENNReal.ofReal (D * a) := by
          rw [window, Real.volume_Icc]
          rw [← ENNReal.ofReal_mul hD]
          congr 1
          ring
    _ = ENNReal.ofReal (a * D) := by rw [mul_comm]
    _ = _ := by rfl

theorem integral_cos_window (k : ℤ) (a t : ℝ) (ht : t ≠ 0) :
    (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      Real.cos (2 * Real.pi * ξ * t)) =
      windowMultiplier a t * Real.cos (2 * Real.pi * (k : ℝ) * t) := by
  have hc : 2 * Real.pi * t ≠ 0 := mul_ne_zero (by positivity) ht
  have hcomp := intervalIntegral.integral_comp_mul_left (f := Real.cos)
    (a := (k : ℝ) - a / 2) (b := (k : ℝ) + a / 2)
    (c := 2 * Real.pi * t) hc
  have hrewrite :
      (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
        Real.cos (2 * Real.pi * ξ * t)) =
        (2 * Real.pi * t)⁻¹ *
          (∫ x in (2 * Real.pi * t) * ((k : ℝ) - a / 2)..
            (2 * Real.pi * t) * ((k : ℝ) + a / 2), Real.cos x) := by
    have hf : (fun ξ : ℝ => Real.cos (2 * Real.pi * ξ * t)) =
        fun ξ => Real.cos ((2 * Real.pi * t) * ξ) := by
      funext ξ
      congr 1
      ring
    rw [hf]
    simpa only [smul_eq_mul] using hcomp
  rw [hrewrite, integral_cos]
  unfold windowMultiplier
  rw [if_neg ht]
  have hs1 :
      Real.sin (2 * Real.pi * t * ((k : ℝ) + a / 2)) =
        Real.sin (2 * Real.pi * (k : ℝ) * t + Real.pi * a * t) := by ring_nf
  have hs2 :
      Real.sin (2 * Real.pi * t * ((k : ℝ) - a / 2)) =
        Real.sin (2 * Real.pi * (k : ℝ) * t - Real.pi * a * t) := by ring_nf
  rw [hs1, hs2, Real.sin_add, Real.sin_sub]
  have hmul : (2 * Real.pi * t)⁻¹ *
      (2 * Real.cos (2 * Real.pi * (k : ℝ) * t) * Real.sin (Real.pi * a * t)) =
      (Real.sin (Real.pi * a * t) / (Real.pi * t)) *
        Real.cos (2 * Real.pi * (k : ℝ) * t) := by
    field_simp
  convert hmul using 1 <;> ring_nf

theorem integral_sin_window (k : ℤ) (a t : ℝ) (ht : t ≠ 0) :
    (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      Real.sin (2 * Real.pi * ξ * t)) =
      windowMultiplier a t * Real.sin (2 * Real.pi * (k : ℝ) * t) := by
  have hc : 2 * Real.pi * t ≠ 0 := mul_ne_zero (by positivity) ht
  have hcomp := intervalIntegral.integral_comp_mul_left (f := Real.sin)
    (a := (k : ℝ) - a / 2) (b := (k : ℝ) + a / 2)
    (c := 2 * Real.pi * t) hc
  have hrewrite :
      (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
        Real.sin (2 * Real.pi * ξ * t)) =
        (2 * Real.pi * t)⁻¹ *
          (∫ x in (2 * Real.pi * t) * ((k : ℝ) - a / 2)..
            (2 * Real.pi * t) * ((k : ℝ) + a / 2), Real.sin x) := by
    have hf : (fun ξ : ℝ => Real.sin (2 * Real.pi * ξ * t)) =
        fun ξ => Real.sin ((2 * Real.pi * t) * ξ) := by
      funext ξ
      congr 1
      ring
    rw [hf]
    simpa only [smul_eq_mul] using hcomp
  rw [hrewrite, integral_sin]
  unfold windowMultiplier
  rw [if_neg ht]
  have hc1 :
      Real.cos (2 * Real.pi * t * ((k : ℝ) - a / 2)) =
        Real.cos (2 * Real.pi * (k : ℝ) * t - Real.pi * a * t) := by ring_nf
  have hc2 :
      Real.cos (2 * Real.pi * t * ((k : ℝ) + a / 2)) =
        Real.cos (2 * Real.pi * (k : ℝ) * t + Real.pi * a * t) := by ring_nf
  rw [hc1, hc2, Real.cos_sub, Real.cos_add]
  have hmul : (2 * Real.pi * t)⁻¹ *
      (2 * Real.sin (2 * Real.pi * (k : ℝ) * t) * Real.sin (Real.pi * a * t)) =
      (Real.sin (Real.pi * a * t) / (Real.pi * t)) *
        Real.sin (2 * Real.pi * (k : ℝ) * t) := by
    field_simp
  convert hmul using 1 <;> ring_nf

theorem windowMultiplier_pos_on_unit (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < windowMultiplier a t := by
  unfold windowMultiplier
  by_cases ht : t = 0
  · simp [ht, ha0]
  · rw [if_neg ht]
    have harg0 : 0 ≤ Real.pi * a * t := by positivity
    have harg1 : Real.pi * a * t ≤ Real.pi / 2 := by
      calc
        Real.pi * a * t ≤ Real.pi * (1 / 2) * t := by gcongr
        _ ≤ Real.pi * (1 / 2) * 1 := by gcongr
        _ = Real.pi / 2 := by ring
    have hs := Real.mul_le_sin harg0 harg1
    have hsin : 0 < Real.sin (Real.pi * a * t) := by
      have : 0 < (2 / Real.pi) * (Real.pi * a * t) := by positivity
      exact lt_of_lt_of_le this hs
    exact div_pos hsin (mul_pos Real.pi_pos (lt_of_le_of_ne ht0 (Ne.symm ht)))

theorem windowMultiplier_lower_on_unit (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a * (2 / Real.pi) ≤ windowMultiplier a t := by
  unfold windowMultiplier
  by_cases ht : t = 0
  · rw [if_pos ht]
    have htwo : (2 : ℝ) / Real.pi ≤ 1 := (div_le_one₀ Real.pi_pos).2 Real.two_le_pi
    calc
      a * (2 / Real.pi) ≤ a * 1 := mul_le_mul_of_nonneg_left htwo ha0.le
      _ = a := mul_one _
  · rw [if_neg ht]
    have harg0 : 0 ≤ Real.pi * a * t := by positivity
    have harg1 : Real.pi * a * t ≤ Real.pi / 2 := by
      calc
        Real.pi * a * t ≤ Real.pi * (1 / 2) * t := by gcongr
        _ ≤ Real.pi * (1 / 2) * 1 := by gcongr
        _ = Real.pi / 2 := by ring
    have hs := Real.mul_le_sin harg0 harg1
    have hden : 0 < Real.pi * t := mul_pos Real.pi_pos (lt_of_le_of_ne ht0 (Ne.symm ht))
    rw [le_div_iff₀ hden]
    calc
      a * (2 / Real.pi) * (Real.pi * t) = (2 / Real.pi) * (Real.pi * a * t) := by ring
      _ ≤ Real.sin (Real.pi * a * t) := hs

end BrownianSharp.AlignmentMaternSpectralWindow
