import BrownianSharp.AlignmentMaternSpectralWindow
import BrownianSharp.AlignmentMaternComplexFeature
import BrownianSharp.AlignmentPeriodicSpectralEnergy
import BrownianSharp.AlignmentPeriodicAbsoluteFourier
import BrownianSharp.AlignmentPeriodicCubeRestriction
import BrownianSharp.AlignmentMaternWindowWeight
import BrownianSharp.AlignmentFeatureSourceClosure
import BrownianSharp.AlignmentPeriodicWindowEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Complex spectral-window sources for the stationary Matérn feature.  Unlike the
real cosine/sine construction, each integer mode is supported on one window;
this makes tensor products and full-lattice frequency sums transparent.
-/

noncomputable section
open MeasureTheory
open Filter
open HaarQuarter
open scoped Topology
open scoped InnerProductSpace

namespace BrownianSharp.AlignmentMaternComplexWindow

open AlignmentMaternSpectralWindow
open BrownianSharp.Torus
open BrownianSharp.AlignmentFractionalSheetRKHS
open BrownianSharp.AlignmentMaternComplexFeature
open BrownianSharp.AlignmentPeriodicCubeRestriction
open BrownianSharp.AlignmentPeriodicAbsoluteFourier
open BrownianSharp.AlignmentMaternWindowWeight
open BrownianSharp.AlignmentFeatureSourceClosure
open BrownianSharp.AlignmentPeriodicWindowEntropy
open BrownianSharp.AtomicBlockKernelL2

def complexMaternPhase (t ξ : ℝ) : ℂ :=
  Complex.exp (((-(2 * Real.pi * ξ * t) : ℝ) : ℂ) * Complex.I)

theorem complexMaternPhase_norm (t ξ : ℝ) : ‖complexMaternPhase t ξ‖ = 1 := by
  simp [complexMaternPhase, Complex.norm_exp]

theorem complexMaternPhaseMemLp (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    MemLp (complexMaternPhase t) 2
      (AlignmentMaternSpectralFeature.spectralMeasure κ h) := by
  let μ := AlignmentMaternSpectralFeature.spectralMeasure κ h
  letI : IsFiniteMeasure μ := AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  have hc : Continuous (complexMaternPhase t) := by
    unfold complexMaternPhase
    fun_prop
  apply MemLp.of_bound hc.measurable.aestronglyMeasurable 1
  filter_upwards with ξ
  rw [complexMaternPhase_norm]

noncomputable def complexMaternPhaseL2 (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Lp ℂ 2 (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
  (complexMaternPhaseMemLp κ h t hκ hh).toLp (complexMaternPhase t)

def complexWindowSourceField (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ) (ξ : ℝ) : ℂ := by
  classical
  exact if ξ ∈ window k a then
    c / (AlignmentMaternSpectralFeature.density κ h ξ : ℂ)
  else 0

theorem complexWindowSourceField_measurable (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (hκ : 0 < κ) : Measurable (complexWindowSourceField κ h k a c) := by
  classical
  unfold complexWindowSourceField
  have hd : Continuous (AlignmentMaternSpectralFeature.density κ h) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    unfold AlignmentMaternSpectralFeature.density
    have hb : ContinuousAt (fun x : ℝ => κ ^ 2 + x ^ 2) ξ := by fun_prop
    exact hb.rpow_const (Or.inl (ne_of_gt (by positivity)))
  have hc : Continuous (fun ξ : ℝ => c / (AlignmentMaternSpectralFeature.density κ h ξ : ℂ)) := by
    apply continuous_const.div₀
      ((Complex.continuous_ofReal.comp hd))
    intro ξ
    exact Complex.ofReal_ne_zero.mpr (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ).ne'
  exact Measurable.ite measurableSet_Icc hc.measurable measurable_const

theorem complexWindowSourceField_norm_bound (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ξ : ℝ) :
    ‖complexWindowSourceField κ h k a c ξ‖ ≤
      ‖c‖ * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
  by_cases hξ : ξ ∈ window k a
  · simp only [complexWindowSourceField, if_pos hξ, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ)]
    have hinv := density_inv_le_window_bound κ h k a ξ hκ hh ha0 ha1 hξ
    calc
      ‖c‖ / AlignmentMaternSpectralFeature.density κ h ξ =
          ‖c‖ * (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ := by ring
      _ ≤ ‖c‖ * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
  · simp [complexWindowSourceField, hξ]
    positivity

noncomputable def complexWindowSourceMemLp (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    MemLp (complexWindowSourceField κ h k a c) 2
      (AlignmentMaternSpectralFeature.spectralMeasure κ h) := by
  let μ := AlignmentMaternSpectralFeature.spectralMeasure κ h
  letI : IsFiniteMeasure μ := AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  apply MemLp.of_bound
    (complexWindowSourceField_measurable κ h k a c hκ).aestronglyMeasurable _
  filter_upwards with ξ
  exact complexWindowSourceField_norm_bound κ h k a c hκ hh ha0 ha1 ξ

noncomputable def complexWindowSource (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Lp ℂ 2 (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
  (complexWindowSourceMemLp κ h k a c hκ hh ha0 ha1).toLp
    (complexWindowSourceField κ h k a c)

theorem complexWindowSource_eLpNorm_le (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (M : ℝ) (hκ : 0 < κ) (hh : 0 < h) (hM : 0 ≤ M)
    (hbound : ∀ ξ, ‖complexWindowSourceField κ h k a c ξ‖ ≤ M) :
    eLpNorm (complexWindowSourceField κ h k a c) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) ≤
      ENNReal.ofReal M *
        (AlignmentMaternSpectralFeature.spectralMeasure κ h (window k a)) ^ (1 / 2 : ℝ) := by
  classical
  have hset : MeasurableSet (window k a) := measurableSet_Icc
  have hdom (ξ : ℝ) :
      ‖complexWindowSourceField κ h k a c ξ‖ₑ ≤
        ‖(window k a).indicator (fun _ : ℝ => M) ξ‖ₑ := by
    by_cases hξ : ξ ∈ window k a
    · simpa only [Set.indicator_of_mem hξ, enorm_le_iff_norm_le,
        Real.norm_of_nonneg hM] using hbound ξ
    · rw [complexWindowSourceField, if_neg hξ]
      simp [Set.indicator_apply, hξ]
  calc
    eLpNorm (complexWindowSourceField κ h k a c) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) ≤
      eLpNorm ((window k a).indicator (fun _ : ℝ => M)) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
      eLpNorm_mono_enorm
        (complexWindowSourceField_measurable κ h k a c hκ).aestronglyMeasurable hdom
    _ = ENNReal.ofReal M *
        (AlignmentMaternSpectralFeature.spectralMeasure κ h (window k a)) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_indicator_const hset.nullMeasurableSet (by norm_num) (by norm_num)]
      rw [show (2 : ENNReal).toReal = 2 by norm_num]
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hM]

theorem complexWindowSource_norm_frequency_bound (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖complexWindowSource κ h k a c hκ hh ha0 ha1‖ ≤
      ‖c‖ * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) *
        Real.rpow (a *
          (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) : ℝ) (1 / 2 : ℝ) := by
  let M := ‖c‖ * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)
  let V := a * (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
    Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hbound (ξ : ℝ) : ‖complexWindowSourceField κ h k a c ξ‖ ≤ M := by
    simpa [M] using complexWindowSourceField_norm_bound κ h k a c hκ hh ha0 ha1 ξ
  have hmem := complexWindowSourceMemLp κ h k a c hκ hh ha0 ha1
  have hnorm : ‖complexWindowSource κ h k a c hκ hh ha0 ha1‖ =
      ENNReal.toReal (eLpNorm (complexWindowSourceField κ h k a c) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h)) := by
    rw [complexWindowSource, Lp.norm_toLp _ hmem]
  have hboundEnn := complexWindowSource_eLpNorm_le κ h k a c M hκ hh hM hbound
  have hmass := spectralMeasure_window_le κ h k a hκ hh ha0 ha1
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (x := ENNReal.ofReal V) (y := (1 / 2 : ℝ))
        (by norm_num) ENNReal.ofReal_ne_top))
    (hboundEnn.trans (mul_le_mul_of_nonneg_left
      (ENNReal.rpow_le_rpow hmass (by norm_num)) (by positivity)))
  rw [← hnorm] at hreal
  have hconvert : ENNReal.toReal (ENNReal.ofReal M * (ENNReal.ofReal V) ^ (1 / 2 : ℝ)) =
      M * Real.rpow V (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hV]
    rfl
  rw [hconvert] at hreal
  simpa [M, V] using hreal

theorem integral_complexExp_window (k : ℤ) (a t : ℝ) (ht : t ≠ 0) :
    (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      Complex.exp (((2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I)) =
      (windowMultiplier a t : ℂ) *
        Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  let x : ℝ → ℝ := fun ξ => 2 * Real.pi * ξ * t
  have hphase (ξ : ℝ) :
      Complex.exp (((x ξ : ℝ) : ℂ) * Complex.I) =
        (Real.cos (x ξ) : ℂ) + (Real.sin (x ξ) : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I (x ξ)
  have hfun : (fun ξ : ℝ => Complex.exp (((2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I)) =
      fun ξ => (Real.cos (x ξ) : ℂ) + (Real.sin (x ξ) : ℂ) * Complex.I := by
    funext ξ
    simpa [x] using hphase ξ
  rw [hfun, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hcos := integral_cos_window k a t ht
  have hsin := integral_sin_window k a t ht
  have hsinC :
      (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
        (Real.sin (x ξ) : ℂ) * Complex.I) =
        Complex.I * (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
          (Real.sin (x ξ) : ℂ)) := by
    rw [show (fun ξ : ℝ => (Real.sin (x ξ) : ℂ) * Complex.I) =
        fun ξ => Complex.I * (Real.sin (x ξ) : ℂ) by funext ξ; ring,
      intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_ofReal, hsinC, intervalIntegral.integral_ofReal]
  have hcos' :
      (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2), Real.cos (x ξ)) =
        windowMultiplier a t * Real.cos (2 * Real.pi * (k : ℝ) * t) := by
    simpa [x] using hcos
  have hsin' :
      (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2), Real.sin (x ξ)) =
        windowMultiplier a t * Real.sin (2 * Real.pi * (k : ℝ) * t) := by
    simpa [x] using hsin
  rw [hcos', hsin']
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.ofReal_mul, Complex.ofReal_add]
  ring

theorem integral_complexExp_window_all (k : ℤ) (a t : ℝ) :
    (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      Complex.exp (((2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I)) =
      (windowMultiplier a t : ℂ) *
        Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  by_cases ht : t = 0
  · simp [windowMultiplier, ht, intervalIntegral.integral_const]
  · exact integral_complexExp_window k a t ht

theorem complexWindowSource_coeFn (κ h : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ((complexWindowSource κ h k a c hκ hh ha0 ha1 : ℝ → ℂ) =ᵐ[
      AlignmentMaternSpectralFeature.spectralMeasure κ h]
      complexWindowSourceField κ h k a c) := by
  exact (complexWindowSourceMemLp κ h k a c hκ hh ha0 ha1).coeFn_toLp

theorem complexWindowFeature_inner_eq_mode (κ h t : ℝ) (k : ℤ) (a : ℝ) (c : ℂ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    inner ℂ (complexMaternPhaseL2 κ h t hκ hh)
      (complexWindowSource κ h k a c hκ hh ha0 ha1) =
      (windowMultiplier a t : ℂ) * c *
        Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  classical
  let μ := AlignmentMaternSpectralFeature.spectralMeasure κ h
  letI : IsFiniteMeasure μ := AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  let f : ℝ → ℂ := fun ξ =>
    inner ℂ (complexMaternPhase t ξ) (complexWindowSourceField κ h k a c ξ)
  have hphase := (complexMaternPhaseMemLp κ h t hκ hh).coeFn_toLp
  have hsrc := complexWindowSource_coeFn κ h k a c hκ hh ha0 ha1
  have hinner : inner ℂ (complexMaternPhaseL2 κ h t hκ hh)
      (complexWindowSource κ h k a c hκ hh ha0 ha1) = ∫ ξ, f ξ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hphase, hsrc] with ξ hp hs
    change complexMaternPhaseL2 κ h t hκ hh ξ = _ at hp
    change complexWindowSource κ h k a c hκ hh ha0 ha1 ξ = _ at hs
    rw [hp, hs]
  rw [hinner]
  have hd : Continuous (AlignmentMaternSpectralFeature.density κ h) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    unfold AlignmentMaternSpectralFeature.density
    have hb : ContinuousAt (fun x : ℝ => κ ^ 2 + x ^ 2) ξ := by fun_prop
    exact hb.rpow_const (Or.inl (ne_of_gt (by positivity)))
  have hmeas : Measurable (fun ξ : ℝ => ENNReal.ofReal
      (AlignmentMaternSpectralFeature.density κ h ξ)) := by
    exact hd.measurable.ennreal_ofReal
  have hfinite : ∀ᵐ ξ ∂volume, ENNReal.ofReal
      (AlignmentMaternSpectralFeature.density κ h ξ) < ⊤ := by
    filter_upwards with ξ
    exact ENNReal.ofReal_lt_top
  rw [show μ = volume.withDensity (fun ξ => ENNReal.ofReal
      (AlignmentMaternSpectralFeature.density κ h ξ)) by rfl,
    integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  have hcancel : ∀ ξ, (ENNReal.ofReal (AlignmentMaternSpectralFeature.density κ h ξ)).toReal • f ξ =
      (if ξ ∈ window k a then c *
        Complex.exp (((2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I) else 0) := by
    intro ξ
    by_cases hξ : ξ ∈ window k a
    · simp [f, complexWindowSourceField, complexMaternPhase, hξ,
        ENNReal.toReal_ofReal (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ).le]
      field_simp [ne_of_gt (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ)]
      rw [← Complex.exp_conj]
      congr 2
      simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
      simp only [map_ofNat]
      push_cast
      ring
    · simp [f, complexWindowSourceField, hξ,
        ENNReal.toReal_ofReal (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ).le]
  simp_rw [hcancel]
  have hwindow :
      (∫ ξ, (if ξ ∈ window k a then c *
        Complex.exp (((2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I) else 0) ∂volume) =
      c * (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
        Complex.exp (((2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I)) := by
    classical
    let g : ℝ → ℂ := fun ξ => c * Complex.exp (((2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I)
    have hcompact : IsCompact (window k a) := isCompact_Icc
    have hcont : Continuous g := by dsimp [g]; fun_prop
    have hi : Integrable ((window k a).indicator g) volume :=
      (hcont.continuousOn.integrableOn_compact hcompact).integrable_indicator hcompact.measurableSet
    have heq : (fun ξ : ℝ => if ξ ∈ window k a then g ξ else 0) =
        (window k a).indicator g := by funext ξ; simp [Set.indicator]
    rw [heq, integral_indicator hcompact.measurableSet]
    simp only [window]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [ha0] :
        (k : ℝ) - a / 2 ≤ (k : ℝ) + a / 2), intervalIntegral.integral_const_mul]
  rw [hwindow, integral_complexExp_window_all]
  ring

theorem complexWindowSource_inner_zero_of_ne (κ h : ℝ) (k l : ℤ) (a : ℝ)
    (c d : ℂ) (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (haLt : a < 1) (hkl : k ≠ l) :
    inner ℂ (complexWindowSource κ h k a c hκ hh ha0 ha1)
      (complexWindowSource κ h l a d hκ hh ha0 ha1) = 0 := by
  let μ := AlignmentMaternSpectralFeature.spectralMeasure κ h
  letI : IsFiniteMeasure μ := AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  classical
  have hdis := window_disjoint_of_integer_centers k l a haLt hkl
  have hcoe₁ := complexWindowSource_coeFn κ h k a c hκ hh ha0 ha1
  have hcoe₂ := complexWindowSource_coeFn κ h l a d hκ hh ha0 ha1
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hcoe₁, hcoe₂] with ξ hξ₁ hξ₂
  rw [hξ₁, hξ₂]
  by_cases hk : ξ ∈ window k a
  · by_cases hl : ξ ∈ window l a
    · exact False.elim ((Set.disjoint_left.mp hdis) hk hl)
    · simp [complexWindowSourceField, hl]
  · simp [complexWindowSourceField, hk]

/-! ### Product windows on the tensor spectral feature -/

open AlignmentMaternComplexFeature

def complexProductWindowSourceField {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (k : Fin d → ℤ) (a : ℝ) (ξ : Fin d → ℝ) : ℂ :=
  ∏ i, complexWindowSourceField (κ i) h (k i) a 1 (ξ i)

theorem complexProductWindowSourceField_measurable {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (k : Fin d → ℤ) (a : ℝ) (hκ : ∀ i, 0 < κ i) :
    Measurable (complexProductWindowSourceField κ h k a) := by
  unfold complexProductWindowSourceField
  apply Finset.univ.measurable_prod
  intro i hi
  exact (complexWindowSourceField_measurable (κ i) h (k i) a 1 (hκ i)).comp
    (measurable_pi_apply i)

theorem complexProductWindowSourceField_norm_bound {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (k : Fin d → ℤ) (a : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ξ : Fin d → ℝ) :
    ‖complexProductWindowSourceField κ h k a ξ‖ ≤
      ∏ i, Real.rpow (κ i ^ 2 + (|(k i : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
  unfold complexProductWindowSourceField
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    simpa using complexWindowSourceField_norm_bound (κ i) h (k i) a 1 (hκ i) hh
      ha0 ha1 (ξ i)

def complexProductWindowSourceMemLp {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (k : Fin d → ℤ) (a : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    MemLp (complexProductWindowSourceField κ h k a) 2
      (Measure.pi (fun i => AlignmentMaternSpectralFeature.spectralMeasure (κ i) h)) := by
  let μ := fun i => AlignmentMaternSpectralFeature.spectralMeasure (κ i) h
  letI (i : Fin d) : IsFiniteMeasure (μ i) :=
    AlignmentMaternSpectralFeature.spectralMeasure_isFinite (κ i) h (hκ i) hh
  apply MemLp.of_bound
    (complexProductWindowSourceField_measurable κ h k a hκ).aestronglyMeasurable _
  filter_upwards with ξ
  exact complexProductWindowSourceField_norm_bound κ h k a hκ hh ha0 ha1 ξ

def complexProductWindowSource {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (k : Fin d → ℤ) (a : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : ComplexProductL2 κ h :=
  (complexProductWindowSourceMemLp κ h k a hκ hh ha0 ha1).toLp
    (complexProductWindowSourceField κ h k a)

theorem complexProductWindowSource_norm {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (k : Fin d → ℤ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖complexProductWindowSource κ h k a hκ hh ha0 ha1‖ =
      ∏ i, ‖complexWindowSource (κ i) h (k i) a 1 (hκ i) hh ha0 ha1‖ := by
  classical
  let μ := fun i => AlignmentMaternSpectralFeature.spectralMeasure (κ i) h
  letI (i : Fin d) : IsFiniteMeasure (μ i) :=
    AlignmentMaternSpectralFeature.spectralMeasure_isFinite (κ i) h (hκ i) hh
  have hnormsq :
      ‖complexProductWindowSource κ h k a hκ hh ha0 ha1‖ ^ 2 =
        ∏ i, ‖complexWindowSource (κ i) h (k i) a 1 (hκ i) hh ha0 ha1‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have hae := (complexProductWindowSourceMemLp κ h k a hκ hh ha0 ha1).coeFn_toLp
    calc
      _ = ∫ ξ, ∏ i, ‖complexWindowSourceField (κ i) h (k i) a 1 (ξ i)‖ ^ 2
          ∂Measure.pi μ := by
        apply integral_congr_ae
        filter_upwards [hae] with ξ hξ
        change (complexProductWindowSource κ h k a hκ hh ha0 ha1) ξ = _ at hξ
        rw [hξ]
        simp [complexProductWindowSourceField, Real.inner_apply, norm_prod,
          Finset.prod_pow]
      _ = ∏ i, ∫ ξ, ‖complexWindowSourceField (κ i) h (k i) a 1 ξ‖ ^ 2 ∂μ i :=
        integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := μ)
          (fun (i : Fin d) (ξ : ℝ) => ‖complexWindowSourceField (κ i) h (k i) a 1 ξ‖ ^ 2)
      _ = ∏ i, ‖complexWindowSource (κ i) h (k i) a 1 (hκ i) hh ha0 ha1‖ ^ 2 := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        have hsrc := complexWindowSource_coeFn (κ i) h (k i) a 1 (hκ i) hh ha0 ha1
        apply integral_congr_ae
        filter_upwards [hsrc] with ξ hξ
        rw [hξ]
        simp [Real.inner_apply]
  have hnonneg : 0 ≤ ∏ i, ‖complexWindowSource (κ i) h (k i) a 1
      (hκ i) hh ha0 ha1‖ := Finset.prod_nonneg fun i hi => norm_nonneg _
  have hnormsq' := hnormsq
  rw [Finset.prod_pow] at hnormsq'
  exact (sq_eq_sq₀ (norm_nonneg _) hnonneg).mp hnormsq'

theorem complexProductWindowSource_norm_frequency_bound {d : ℕ} (κ : Fin d → ℝ)
    (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (k : Fin d → ℤ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖complexProductWindowSource κ h k a hκ hh ha0 ha1‖ ≤
      ∏ i, (Real.rpow (κ i ^ 2 + (|(k i : ℝ)| + 1) ^ 2) (h + 1 / 2) *
        Real.rpow (a * (Real.rpow (min 1 (κ i ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k i : ℝ) ^ 2) (-(h + 1 / 2))) : ℝ) (1 / 2 : ℝ)) := by
  rw [complexProductWindowSource_norm]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    simpa using complexWindowSource_norm_frequency_bound (κ i) h (k i) a 1
      (hκ i) hh ha0 ha1

theorem rawComplexSheetFeature_inner_productWindow {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : Fin d → ℝ)
    (k : Fin d → ℤ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    inner ℂ (rawComplexSheetFeature κ h hκ hh t)
      (complexProductWindowSource κ h k a hκ hh ha0 ha1) =
      ∏ i, ((windowMultiplier a (t i) : ℂ) *
        Complex.exp (((2 * Real.pi * (k i : ℝ) * t i : ℝ) : ℂ) * Complex.I)) := by
  classical
  let μ := fun i => AlignmentMaternSpectralFeature.spectralMeasure (κ i) h
  letI (i : Fin d) : IsFiniteMeasure (μ i) :=
    AlignmentMaternSpectralFeature.spectralMeasure_isFinite (κ i) h (hκ i) hh
  rw [L2.inner_def]
  have hae₁ := (complexSheetPhase_memLp κ h hκ hh t).coeFn_toLp
  have hae₂ := complexProductWindowSourceMemLp κ h k a hκ hh ha0 ha1 |>.coeFn_toLp
  calc
    _ = ∫ ξ, ∏ i, (star (complexMaternPhase (t i) (ξ i)) *
          complexWindowSourceField (κ i) h (k i) a 1 (ξ i))
        ∂Measure.pi μ := by
      apply integral_congr_ae
      filter_upwards [hae₁, hae₂] with ξ hξ₁ hξ₂
      change inner ℂ ((complexSheetPhase_memLp κ h hκ hh t).toLp _ ξ)
        ((complexProductWindowSourceMemLp κ h k a hκ hh ha0 ha1).toLp _ ξ) = _
      change ((complexSheetPhase_memLp κ h hκ hh t).toLp _ ξ) = _ at hξ₁
      change ((complexProductWindowSourceMemLp κ h k a hκ hh ha0 ha1).toLp _ ξ) = _ at hξ₂
      rw [hξ₁, hξ₂, RCLike.inner_apply']
      simp only [complexSheetPhase, map_prod, complexProductWindowSourceField,
        complexPhase, complexMaternPhase, starRingEnd_apply]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∫ ξ, star (complexMaternPhase (t i) ξ) *
          complexWindowSourceField (κ i) h (k i) a 1 ξ ∂μ i :=
        by simpa only [μ] using
          (integral_fintype_prod_eq_prod
            (fun i ξ => star (complexMaternPhase (t i) ξ) *
              complexWindowSourceField (κ i) h (k i) a 1 ξ))
    _ = ∏ i, ((windowMultiplier a (t i) : ℂ) *
          Complex.exp (((2 * Real.pi * (k i : ℝ) * t i : ℝ) : ℂ) * Complex.I)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hp := complexWindowFeature_inner_eq_mode (κ i) h (t i) (k i) a 1
        (hκ i) hh ha0 ha1
      have hphase := (complexMaternPhaseMemLp (κ i) h (t i) (hκ i) hh).coeFn_toLp
      have hsrc := complexWindowSource_coeFn (κ i) h (k i) a 1 (hκ i) hh ha0 ha1
      have hint : inner ℂ (complexMaternPhaseL2 (κ i) h (t i) (hκ i) hh)
          (complexWindowSource (κ i) h (k i) a 1 (hκ i) hh ha0 ha1) =
          ∫ ξ, star (complexMaternPhase (t i) ξ) *
            complexWindowSourceField (κ i) h (k i) a 1 ξ ∂μ i := by
        apply integral_congr_ae
        filter_upwards [hphase, hsrc] with ξ hξ₁ hξ₂
        change complexMaternPhaseL2 (κ i) h (t i) (hκ i) hh ξ = _ at hξ₁
        change complexWindowSource (κ i) h (k i) a 1 (hκ i) hh ha0 ha1 ξ = _ at hξ₂
        rw [hξ₁, hξ₂, RCLike.inner_apply']
        simp only [complexMaternPhase, starRingEnd_apply]
      rw [hint] at hp
      simpa only [complexPhase, complexMaternPhase, mul_one] using hp

theorem rawComplexSheetFeature_inner_productWindow_smul {d : ℕ} (κ : Fin d → ℝ)
    (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : Fin d → ℝ)
    (k : Fin d → ℤ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (c : ℂ) :
    inner ℂ (rawComplexSheetFeature κ h hκ hh t)
      (c • complexProductWindowSource κ h k a hκ hh ha0 ha1) =
      c * ∏ i, ((windowMultiplier a (t i) : ℂ) *
        Complex.exp (((2 * Real.pi * (k i : ℝ) * t i : ℝ) : ℂ) * Complex.I)) := by
  rw [inner_smul_right, rawComplexSheetFeature_inner_productWindow]

theorem complexProductWindowSource_orthogonal_of_ne {d : ℕ} (κ : Fin d → ℝ)
    (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (k l : Fin d → ℤ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haLt : a < 1) (hkl : k ≠ l) :
    inner ℂ (complexProductWindowSource κ h k a hκ hh ha0 ha1)
      (complexProductWindowSource κ h l a hκ hh ha0 ha1) = 0 := by
  classical
  let μ := fun i => AlignmentMaternSpectralFeature.spectralMeasure (κ i) h
  letI (i : Fin d) : IsFiniteMeasure (μ i) :=
    AlignmentMaternSpectralFeature.spectralMeasure_isFinite (κ i) h (hκ i) hh
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hkl
  have hdis := window_disjoint_of_integer_centers (k i) (l i) a haLt hi
  have hcoe₁ := (complexProductWindowSourceMemLp κ h k a hκ hh ha0 ha1).coeFn_toLp
  have hcoe₂ := (complexProductWindowSourceMemLp κ h l a hκ hh ha0 ha1).coeFn_toLp
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hcoe₁, hcoe₂] with ξ hξ₁ hξ₂
  change complexProductWindowSource κ h k a hκ hh ha0 ha1 ξ = _ at hξ₁
  change complexProductWindowSource κ h l a hκ hh ha0 ha1 ξ = _ at hξ₂
  rw [hξ₁, hξ₂, RCLike.inner_apply']
  have hzero : complexProductWindowSourceField κ h k a ξ = 0 ∨
      complexProductWindowSourceField κ h l a ξ = 0 := by
    by_cases hik : ξ i ∈ window (k i) a
    · have hil : ξ i ∉ window (l i) a := by
        intro hil
        exact (Set.disjoint_left.mp hdis) hik hil
      right
      unfold complexProductWindowSourceField
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [complexWindowSourceField, hil]
    · left
      unfold complexProductWindowSourceField
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [complexWindowSourceField, hik]
  rcases hzero with hzero | hzero <;> simp [hzero]

/-! ### Sobolev-weighted norm bounds -/

theorem complexWindowSource_norm_sobolev_bound (κ h a : ℝ) (k : ℤ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ‖complexWindowSource κ h k a 1 hκ hh (le_of_lt ha0) ha1‖ ≤
      Real.sqrt (a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2))) *
        Real.rpow (1 + (k : ℝ) ^ 2) ((h + 1 / 2) / 2) := by
  have hbase : 0 < 1 + (k : ℝ) ^ 2 := by positivity
  have hu : 0 < κ ^ 2 + (|(k : ℝ)| + 1) ^ 2 := by positivity
  have hconst : 0 < κ ^ 2 + 2 := by positivity
  have hexp : 0 < h + 1 / 2 := by linarith
  have hu_le : κ ^ 2 + (|(k : ℝ)| + 1) ^ 2 ≤
      (κ ^ 2 + 2) * (1 + (k : ℝ) ^ 2) := by
    have habs : |(k : ℝ)| ^ 2 = (k : ℝ) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|(k : ℝ)| - 1)]
  have hpow := complexWindowSource_norm_frequency_bound κ h k a 1 hκ hh
    (le_of_lt ha0) ha1
  let V : ℝ := a * (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
    Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))
  have hV : 0 ≤ V := by
    dsimp [V]
    apply mul_nonneg (le_of_lt ha0)
    apply mul_nonneg
    · exact Real.rpow_nonneg (by positivity) _
    · exact Real.rpow_nonneg hbase.le _
  have hsquare :
      (‖complexWindowSource κ h k a 1 hκ hh (le_of_lt ha0) ha1‖) ^ 2 ≤
        (a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2))) *
          Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := by
    have hpow' := hpow
    have hpow' :
        ‖complexWindowSource κ h k a 1 hκ hh (le_of_lt ha0) ha1‖ ≤
          Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) *
            Real.rpow V (1 / 2 : ℝ) := by
      simpa [norm_one, V] using hpow
    have hnonneg : 0 ≤ Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) :=
      Real.rpow_nonneg hu.le _
    have hnonneg2 : 0 ≤ Real.rpow V (1 / 2 : ℝ) := Real.rpow_nonneg hV _
    have hsquare0 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hnonneg hnonneg2)).2 hpow'
    have hmono := Real.rpow_le_rpow hu.le hu_le (by positivity :
      0 ≤ 2 * (h + 1 / 2))
    have hu2 : Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (2 * (h + 1 / 2)) ≤
        Real.rpow ((κ ^ 2 + 2) * (1 + (k : ℝ) ^ 2)) (2 * (h + 1 / 2)) := hmono
    have hmul := Real.mul_rpow (x := κ ^ 2 + 2) (y := 1 + (k : ℝ) ^ 2)
      (z := 2 * (h + 1 / 2)) hconst.le hbase.le
    have hneg : Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)) *
        Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) = 1 := by
      calc
        _ = Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2) + (h + 1 / 2)) :=
          (Real.rpow_add hbase (-(h + 1 / 2)) (h + 1 / 2)).symm
        _ = 1 := by simp
    have hVhalf : (Real.rpow V (1 / 2 : ℝ)) ^ 2 = V := by
      simpa [Real.rpow_one] using
        (Real.rpow_mul (x := V) hV (1 / 2 : ℝ) (2 : ℝ)).symm
    have huSq : (Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)) ^ 2 =
        Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (2 * (h + 1 / 2)) := by
      calc
        _ = Real.rpow (Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)) 2 :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) ((h + 1 / 2) * 2) :=
          (Real.rpow_mul hu.le (h + 1 / 2) 2).symm
        _ = _ := by congr 1 <;> ring
    have hstart : ‖complexWindowSource κ h k a 1 hκ hh (le_of_lt ha0) ha1‖ ^ 2 ≤
        Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (2 * (h + 1 / 2)) * V := by
      rw [mul_pow, hVhalf, huSq] at hsquare0
      simpa [V] using hsquare0
    have hupper : Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (2 * (h + 1 / 2)) ≤
        Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (2 * (h + 1 / 2)) := by
      calc
        _ ≤ Real.rpow ((κ ^ 2 + 2) * (1 + (k : ℝ) ^ 2)) (2 * (h + 1 / 2)) := hu2
        _ = _ := hmul
    have hyCancel : Real.rpow (1 + (k : ℝ) ^ 2) (2 * (h + 1 / 2)) *
        Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)) =
          Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := by
      calc
        _ = Real.rpow (1 + (k : ℝ) ^ 2)
            (2 * (h + 1 / 2) + (-(h + 1 / 2))) :=
          (Real.rpow_add hbase _ _).symm
        _ = _ := by congr 1 <;> ring
    calc
      _ ≤ Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (2 * (h + 1 / 2)) * V := hstart
      _ ≤ (Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (2 * (h + 1 / 2))) * V :=
        mul_le_mul_of_nonneg_right hupper hV
      _ = (a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2))) *
          Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := by
        dsimp [V]
        calc
          _ = a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2)) *
            (Real.rpow (1 + (k : ℝ) ^ 2) (2 * (h + 1 / 2)) *
              Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) := by ac_rfl
          _ = _ := by rw [hyCancel]; ac_rfl
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg hbase.le _))).1
  have htarget :
      (Real.sqrt (a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2))) *
        Real.rpow (1 + (k : ℝ) ^ 2) ((h + 1 / 2) / 2)) ^ 2 =
      (a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2))) *
        Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := by
    have hy : (Real.rpow (1 + (k : ℝ) ^ 2) ((h + 1 / 2) / 2)) ^ 2 =
        Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := by
      calc
        _ = Real.rpow (Real.rpow (1 + (k : ℝ) ^ 2) ((h + 1 / 2) / 2)) 2 :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow (1 + (k : ℝ) ^ 2) (((h + 1 / 2) / 2) * 2) :=
          (Real.rpow_mul hbase.le ((h + 1 / 2) / 2) 2).symm
        _ = _ := by
          congr 1
          ring
    have hmin : 0 < min 1 (κ ^ 2) / 2 := by positivity
    have hc : 0 ≤ a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2)) := by
      apply mul_nonneg (mul_nonneg (le_of_lt ha0) (Real.rpow_nonneg hmin.le _))
      exact Real.rpow_nonneg (by positivity) _
    rw [mul_pow, Real.sq_sqrt hc, hy]
  calc
    _ ≤ (a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2))) *
        Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := hsquare
    _ = _ := htarget.symm

/-- The scalar constant in the integer-window source estimate. -/
def complexWindowSobolevConst (κ h a : ℝ) : ℝ :=
  a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
    Real.rpow (κ ^ 2 + 2) (2 * (h + 1 / 2))

theorem complexWindowSource_norm_sq_weight_bound (κ h a : ℝ) (k : ℤ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ‖complexWindowSource κ h k a 1 hκ hh (le_of_lt ha0) ha1‖ ^ 2 ≤
      complexWindowSobolevConst κ h a *
        Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := by
  have hnorm := complexWindowSource_norm_sobolev_bound κ h a k hκ hh ha0 ha1
  have hC : 0 ≤ complexWindowSobolevConst κ h a := by
    unfold complexWindowSobolevConst
    apply mul_nonneg (mul_nonneg ha0.le (Real.rpow_nonneg (by positivity) _))
    exact Real.rpow_nonneg (by positivity) _
  unfold complexWindowSobolevConst at hC
  have hy : (Real.rpow (1 + (k : ℝ)^2) ((h + 1/2)/2))^2 =
      Real.rpow (1 + (k : ℝ)^2) (h + 1/2) := by
    calc
      _ = Real.rpow (Real.rpow (1 + (k : ℝ)^2) ((h + 1/2)/2)) 2 :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (1 + (k : ℝ)^2) (((h + 1/2)/2)*2) :=
        (Real.rpow_mul (by positivity : 0 ≤ 1 + (k : ℝ)^2) _ _).symm
      _ = _ := by congr 1; ring
  have hsquare := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _))).2 hnorm
  rw [mul_pow] at hsquare
  change ‖complexWindowSource κ h k a 1 hκ hh (le_of_lt ha0) ha1‖ ^ 2 ≤
    (Real.sqrt (complexWindowSobolevConst κ h a)) ^ 2 *
      (Real.rpow (1 + (k : ℝ)^2) ((h + 1/2)/2)) ^ 2 at hsquare
  have hCfold : 0 ≤ complexWindowSobolevConst κ h a := hC
  rw [Real.sq_sqrt hCfold, hy] at hsquare
  simpa [complexWindowSobolevConst, mul_assoc] using hsquare

def complexProductWindowSobolevConst {d : ℕ} (κ : Fin d → ℝ) (h a : ℝ) : ℝ :=
  ∏ i, complexWindowSobolevConst (κ i) h a

theorem complexProductWindowSource_norm_sq_weight_bound {d : ℕ}
    (κ : Fin d → ℝ) (h a : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (k : Fin d → ℤ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ‖complexProductWindowSource κ h k a hκ hh (le_of_lt ha0) ha1‖ ^ 2 ≤
      complexProductWindowSobolevConst κ h a *
        AlignmentPeriodicSpectralEnergy.spectralWeight (h + 1/2) k := by
  classical
  rw [complexProductWindowSource_norm, ← Finset.prod_pow]
  unfold complexProductWindowSobolevConst
  calc
    ∏ i, ‖complexWindowSource (κ i) h (k i) a 1 (hκ i) hh
        (le_of_lt ha0) ha1‖ ^ 2 ≤
      ∏ i, (complexWindowSobolevConst (κ i) h a *
        Real.rpow (1 + (k i : ℝ)^2) (h + 1/2)) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact sq_nonneg _
          · intro i hi
            exact complexWindowSource_norm_sq_weight_bound (κ i) h a (k i)
              (hκ i) hh ha0 ha1
    _ = (∏ i, complexWindowSobolevConst (κ i) h a) *
        (∏ i, Real.rpow (1 + (k i : ℝ)^2) (h + 1/2)) := by
          rw [Finset.prod_mul_distrib]
    _ = _ := by
      simp [AlignmentPeriodicSpectralEnergy.spectralWeight]

theorem norm_sq_sum_of_pairwise_inner_zero {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : ι → E)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) (s : Finset ι) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha]
      have hc : inner ℂ (v a) (∑ i ∈ s, v i) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact horth a i (by
          intro h
          subst i
          exact ha hi)
      have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v a)
        (∑ i ∈ s, v i) hc
      have hp' : ‖v a + ∑ i ∈ s, v i‖ ^ 2 =
          ‖v a‖ ^ 2 + ‖∑ i ∈ s, v i‖ ^ 2 := by
        simpa [pow_two] using hp
      rw [hp', ih]

noncomputable def periodicWindowSourcePartial {d : ℕ} (κ : Fin d → ℝ) (h a : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (ha0 : 0 < a) (ha1 : a < 1/2)
    (f : RealPeriodic d) (s : Finset (Fin d → ℤ)) :
    ComplexProductL2 κ h :=
  ∑ k ∈ s, realPeriodicFourierCoeff f k •
    complexProductWindowSource κ h k a hκ hh (le_of_lt ha0) (by linarith [ha1])

theorem periodicWindowSourcePartial_norm_sq_le {d : ℕ} (κ : Fin d → ℝ) (h a : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (ha0 : 0 < a) (ha1 : a < 1/2)
    (f : RealPeriodic d)
    (hf : BrownianSharp.SmoothResolution.SobolevUnitBall 2 (h+1/2) f)
    (s : Finset (Fin d → ℤ)) :
    ‖periodicWindowSourcePartial κ h a hκ hh ha0 ha1 f s‖ ^ 2 ≤
      complexProductWindowSobolevConst κ h a *
        (2*(5:ℝ)^(h+1/2))^d := by
  classical
  have horth (k l : Fin d → ℤ) (hkl : k ≠ l) :
      inner ℂ
        (realPeriodicFourierCoeff f k •
          complexProductWindowSource κ h k a hκ hh (le_of_lt ha0) (by linarith [ha1]))
        (realPeriodicFourierCoeff f l •
          complexProductWindowSource κ h l a hκ hh (le_of_lt ha0) (by linarith [ha1])) = 0 := by
    rw [inner_smul_left, inner_smul_right,
      complexProductWindowSource_orthogonal_of_ne κ h hκ hh k l a
        (le_of_lt ha0) (by linarith [ha1]) (by linarith [ha1]) hkl]
    simp
  have hr : 1/2 < h+1/2 := by linarith
  have henergy := BrownianSharp.AlignmentPeriodicSpectralEnergy.sobolev_two_spectral_energy_le
    (h+1/2) (by linarith) f hf
  have hfinite : (∑ k ∈ s,
      AlignmentPeriodicSpectralEnergy.spectralWeight (h+1/2) k *
        ‖realPeriodicFourierCoeff f k‖^2) ≤
      (2*(5:ℝ)^(h+1/2))^d := by
    have hnonneg (k : Fin d → ℤ) :
        0 ≤ AlignmentPeriodicSpectralEnergy.spectralWeight (h+1/2) k *
          ‖realPeriodicFourierCoeff f k‖^2 := by
      apply mul_nonneg _ (sq_nonneg _)
      unfold AlignmentPeriodicSpectralEnergy.spectralWeight
      exact Finset.prod_nonneg fun i hi => Real.rpow_nonneg (by positivity) _
    exact (henergy.1.sum_le_tsum s (fun k hk => hnonneg k)).trans henergy.2
  have hCnonneg : 0 ≤ complexProductWindowSobolevConst κ h a := by
    unfold complexProductWindowSobolevConst
    apply Finset.prod_nonneg
    intro i hi
    unfold complexWindowSobolevConst
    apply mul_nonneg (mul_nonneg ha0.le (Real.rpow_nonneg (by positivity) _))
    exact Real.rpow_nonneg (by positivity) _
  calc
    ‖∑ k ∈ s, realPeriodicFourierCoeff f k •
        complexProductWindowSource κ h k a hκ hh (le_of_lt ha0) (by linarith [ha1])‖^2 =
      ∑ k ∈ s, ‖realPeriodicFourierCoeff f k •
        complexProductWindowSource κ h k a hκ hh (le_of_lt ha0) (by linarith [ha1])‖^2 := by
          exact norm_sq_sum_of_pairwise_inner_zero _ horth s
    _ ≤ complexProductWindowSobolevConst κ h a *
        (∑ k ∈ s, AlignmentPeriodicSpectralEnergy.spectralWeight (h+1/2) k *
          ‖realPeriodicFourierCoeff f k‖^2) := by
      calc
        _ ≤ ∑ k ∈ s, (complexProductWindowSobolevConst κ h a) *
            (AlignmentPeriodicSpectralEnergy.spectralWeight (h+1/2) k *
              ‖realPeriodicFourierCoeff f k‖^2) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_smul]
          rw [mul_pow]
          have hmode := complexProductWindowSource_norm_sq_weight_bound κ h a hκ hh k ha0
            (by linarith [ha1])
          calc
            _ = ‖realPeriodicFourierCoeff f k‖^2 *
                ‖complexProductWindowSource κ h k a hκ hh (le_of_lt ha0)
                  (by linarith [ha1])‖^2 := by simp [mul_pow, mul_comm]
            _ ≤ _ := by
              calc
                _ ≤ ‖realPeriodicFourierCoeff f k‖^2 *
                    (complexProductWindowSobolevConst κ h a *
                      AlignmentPeriodicSpectralEnergy.spectralWeight (h+1/2) k) :=
                  mul_le_mul_of_nonneg_left hmode (sq_nonneg _)
                _ = _ := by ring
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinite hCnonneg

/-- In a complex `L²` source, the real inner product is the real part of the
complex inner product. -/
theorem complexProductL2_real_inner_eq_re {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (x y : ComplexProductL2 κ h) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [L2.inner_def, L2.inner_def]
  simpa only [Complex.inner, RCLike.inner_apply, RCLike.re_to_complex] using
    (integral_re (L2.integrable_inner (𝕜 := ℂ) x y))

noncomputable def windowFourierRealTransform {d : ℕ} :
    C(UnitAddTorus (Fin d), ℂ) →L[ℝ] C(BrownianCubeAnchor d, ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ (BrownianCubeAnchor d)).comp
    (ContinuousMap.compCLM ℝ ℂ (cubeToTorus d))

@[simp] theorem windowFourierRealTransform_apply {d : ℕ}
    (g : C(UnitAddTorus (Fin d),ℂ)) (t : BrownianCubeAnchor d) :
    windowFourierRealTransform g t = (g (cubeToTorus d t)).re := by
  rfl

@[simp] theorem torusFourierPolynomial_apply {d : ℕ}
    (s : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (x : UnitAddTorus (Fin d)) :
    torusFourierPolynomial s c x = ∑ k ∈ s, c k * UnitAddTorus.mFourier k x := by
  simp [torusFourierPolynomial, ContinuousMap.coe_sum,
    ContinuousMap.smul_apply, smul_eq_mul]

/-- A finite collection of spectral window sources maps exactly to the
windowed real Fourier polynomial. -/
theorem complexSheetFeature_partial_eq_windowFourier {d : ℕ}
    (κ : Fin d → ℝ) (h a : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (ha0 : 0 < a) (ha1 : a < 1/2) (f : RealPeriodic d)
    (s : Finset (Fin d → ℤ)) :
    featureOperator (complexSheetFeature κ h hκ hh)
        ((complexFeatureScale κ h hκ hh)⁻¹ •
          periodicWindowSourcePartial κ h a hκ hh ha0 ha1 f s) =
      cubeWindowWeight d a * windowFourierRealTransform
        (torusFourierPolynomial s (realPeriodicFourierCoeff f)) := by
  classical
  ext t
  change inner ℝ
      (complexFeatureScale κ h hκ hh •
        rawComplexSheetFeature κ h hκ hh t.1)
      ((complexFeatureScale κ h hκ hh)⁻¹ •
        periodicWindowSourcePartial κ h a hκ hh ha0 ha1 f s) = _
  rw [real_inner_smul_left, real_inner_smul_right]
  have hscale : complexFeatureScale κ h hκ hh *
      (complexFeatureScale κ h hκ hh)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt (complexFeatureScale_pos κ h hκ hh))
  rw [← mul_assoc, hscale, one_mul]
  rw [periodicWindowSourcePartial, inner_sum]
  rw [ContinuousMap.mul_apply, cubeWindowWeight_apply]
  rw [windowFourierRealTransform_apply]
  rw [torusFourierPolynomial_apply, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [complexProductL2_real_inner_eq_re,
    rawComplexSheetFeature_inner_productWindow_smul κ h hκ hh t.1 k a
      (le_of_lt ha0) (by linarith [ha1]) (realPeriodicFourierCoeff f k)]
  have hprod :
      (∏ i, ((windowMultiplier a (t.1 i) : ℂ) *
        Complex.exp (((2 * Real.pi * (k i : ℝ) * t.1 i : ℝ) : ℂ) * Complex.I))) =
        (∏ i, (windowMultiplier a (t.1 i) : ℂ)) *
          UnitAddTorus.mFourier k (cubeToTorus d t) := by
    calc
      _ = (∏ i, (windowMultiplier a (t.1 i) : ℂ)) *
          (∏ i, Complex.exp (((2 * Real.pi * (k i : ℝ) * t.1 i : ℝ) : ℂ) * Complex.I)) :=
        Finset.prod_mul_distrib
      _ = (∏ i, (windowMultiplier a (t.1 i) : ℂ)) *
          UnitAddTorus.mFourier k (cubeToTorus d t) := by
        congr 1
        change (∏ i, Complex.exp (((2 * Real.pi * (k i : ℝ) * t.1 i : ℝ) : ℂ) * Complex.I)) =
          ∏ i, fourier (k i) ((t.1 i : ℝ) : AddCircle (1 : ℝ))
        apply Finset.prod_congr rfl
        intro i hi
        rw [fourier_coe_apply]
        congr 1
        norm_num
        ring
  rw [hprod]
  simp only [← Complex.ofReal_prod, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Every periodic Sobolev-ball function is represented by a uniformly
bounded source for the normalized tensor Matérn feature. -/
theorem matern_periodic_sobolev_source_embedding {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    ∃ A : ℝ, 0 < A ∧
      ∀ f : RealPeriodic d,
        BrownianSharp.SmoothResolution.SobolevUnitBall 2 (h+1/2) f →
          ∃ z : ComplexProductL2 κ h, ‖z‖ ≤ A ∧
            featureOperator (complexSheetFeature κ h hκ hh) z =
              weightedCubeRestriction (cubeWindowWeight d (1/4)) f := by
  let a : ℝ := 1/4
  let S : ℝ := complexFeatureScale κ h hκ hh
  let C : ℝ := complexProductWindowSobolevConst κ h a
  let E : ℝ := (2*(5:ℝ)^(h+1/2))^d
  let A : ℝ := S⁻¹ * Real.sqrt (C*E)
  have hS : 0 < S := complexFeatureScale_pos κ h hκ hh
  have hC : 0 < C := by
    dsimp [C, complexProductWindowSobolevConst]
    apply Finset.prod_pos
    intro i hi
    unfold complexWindowSobolevConst
    have hκi : 0 < κ i := hκ i
    have ha : 0 < a := by norm_num [a]
    have hmin : 0 < min 1 (κ i ^ 2) :=
      lt_min (by norm_num) (sq_pos_of_pos hκi)
    have hbase : 0 < min 1 (κ i ^ 2) / 2 := by
      apply div_pos
      · exact hmin
      · norm_num
    have hbase2 : 0 < (κ i)^2 + 2 := by positivity
    exact mul_pos (mul_pos ha (Real.rpow_pos_of_pos hbase _))
      (Real.rpow_pos_of_pos hbase2 _)
  have hE : 0 < E := by dsimp [E]; positivity
  have hD : 0 < C*E := mul_pos hC hE
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (inv_pos.mpr hS) (Real.sqrt_pos.2 hD)
  refine ⟨A,hA,?_⟩
  intro f hf
  let F : Finset (Fin d → ℤ) → ComplexProductL2 κ h := fun s =>
    S⁻¹ • periodicWindowSourcePartial κ h a hκ hh (by norm_num [a])
      (by norm_num [a]) f s
  have hF : ∀ s, ‖F s‖ ≤ A := by
    intro s
    have hpartial := periodicWindowSourcePartial_norm_sq_le κ h a hκ hh
      (by norm_num [a]) (by norm_num [a]) f hf s
    have hpartial_norm : ‖periodicWindowSourcePartial κ h a hκ hh
        (by norm_num [a]) (by norm_num [a]) f s‖ ≤ Real.sqrt (C*E) := by
      have hn := norm_nonneg (periodicWindowSourcePartial κ h a hκ hh
        (by norm_num [a]) (by norm_num [a]) f s)
      have hs := Real.sq_sqrt hD.le
      have hp : ‖periodicWindowSourcePartial κ h a hκ hh
          (by norm_num [a]) (by norm_num [a]) f s‖ ^ 2 ≤ C*E := by
        simpa [C,E] using hpartial
      have hsq : ‖periodicWindowSourcePartial κ h a hκ hh
          (by norm_num [a]) (by norm_num [a]) f s‖ ^ 2 ≤
            (Real.sqrt (C*E))^2 := by rw [hs]; exact hp
      exact (sq_le_sq₀ hn (Real.sqrt_nonneg _)).1 hsq
    calc
      ‖F s‖ = S⁻¹ * ‖periodicWindowSourcePartial κ h a hκ hh
          (by norm_num [a]) (by norm_num [a]) f s‖ := by
            change ‖S⁻¹ • periodicWindowSourcePartial κ h a hκ hh
              (by norm_num [a]) (by norm_num [a]) f s‖ = _
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hS)]
      _ ≤ S⁻¹ * Real.sqrt (C*E) :=
        mul_le_mul_of_nonneg_left hpartial_norm (inv_pos.mpr hS).le
      _ = A := rfl
  have hFourier := realPeriodicFourier_hasSum_uniform (h+1/2)
    (by linarith) f hf
  let T : C(UnitAddTorus (Fin d),ℂ) →L[ℝ] C(BrownianCubeAnchor d,ℝ) :=
    windowFourierRealTransform
  have hmapped := T.hasSum hFourier
  have htarget : T (complexifyContinuous f) = periodicCubeRestriction d f := by
    ext t
    simp [T,windowFourierRealTransform,complexifyContinuous,
      periodicCubeRestriction_apply,cubeToTorus]
  have hseries : Tendsto
      (fun s : Finset (Fin d → ℤ) =>
        T (torusFourierPolynomial s (realPeriodicFourierCoeff f)))
      atTop (𝓝 (periodicCubeRestriction d f)) := by
    have hts : Tendsto
        (fun s : Finset (Fin d → ℤ) =>
          ∑ k ∈ s, T (realPeriodicFourierCoeff f k • UnitAddTorus.mFourier k))
        atTop (𝓝 (T (complexifyContinuous f))) := by
      change Tendsto
        (fun s : Finset (Fin d → ℤ) =>
          ∑ k ∈ s, T (realPeriodicFourierCoeff f k • UnitAddTorus.mFourier k))
        atTop (𝓝 (T (complexifyContinuous f)) )
      exact hmapped
    have hsum_eq (s : Finset (Fin d → ℤ)) :
        T (torusFourierPolynomial s (realPeriodicFourierCoeff f)) =
          ∑ k ∈ s, T (realPeriodicFourierCoeff f k • UnitAddTorus.mFourier k) := by
      simp [T,torusFourierPolynomial,map_sum]
    simpa only [hsum_eq,htarget] using hts
  have hwindow : Tendsto
      (fun s : Finset (Fin d → ℤ) => cubeWindowWeight d a *
        T (torusFourierPolynomial s (realPeriodicFourierCoeff f)))
      atTop (𝓝 (cubeWindowWeight d a * periodicCubeRestriction d f)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : Finset (Fin d → ℤ) =>
      cubeWindowWeight d a) atTop (𝓝 (cubeWindowWeight d a))).mul hseries
  have hlim : Tendsto
      (fun s : Finset (Fin d → ℤ) =>
        featureOperator (complexSheetFeature κ h hκ hh) (F s))
      atTop (𝓝 (weightedCubeRestriction (cubeWindowWeight d a) f)) := by
    convert hwindow using 1
    · funext s
      exact complexSheetFeature_partial_eq_windowFourier κ h a hκ hh
        (by norm_num [a]) (by norm_num [a]) f s
    · rfl
  obtain ⟨z,hz,hzf⟩ := exists_source_of_finite_approximations
    (complexSheetFeature κ h hκ hh) A hA F
    (weightedCubeRestriction (cubeWindowWeight d a) f) hF hlim
  exact ⟨z,hz,hzf⟩

end BrownianSharp.AlignmentMaternComplexWindow
