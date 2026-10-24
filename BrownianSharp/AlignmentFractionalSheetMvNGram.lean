import BrownianSharp.AlignmentFractionalSheetRKHS
import BrownianSharp.AlignmentRealL2Scaling
import BrownianSharp.AlignmentFractionalPastTail
import BrownianSharp.AlignmentFractionalSheetPositive

/-!
The full-line Mandelbrot--van Ness feature identities underlying the actual
fractional Brownian covariance. This module keeps the two-sided kernel (in
particular its negative-time correction) explicit.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalSheetMvNGram

open BrownianSharp.AlignmentFractionalSheetRKHS
open BrownianSharp.AlignmentRealL2Scaling
open BrownianSharp.AlignmentFractionalPastTail
open BrownianSharp.AlignmentFractionalSheetPositive
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalL2

/-- The ambient full-line real Hilbert space for the MvN features. -/
abbrev FullLineL2 := Lp ℝ 2 (volume : Measure ℝ)

/-- Zero extension of a positive-time source vector from `[0,1]` to the
whole-line MvN source. -/
def positiveSourceExtensionFunction (g : UnitL2) : ℝ → ℝ :=
  (Set.Icc (0:ℝ) 1).indicator (fun u => g u)

theorem positiveSourceExtension_memLp (g : UnitL2) :
    MemLp (positiveSourceExtensionFunction g) 2 volume := by
  rw [positiveSourceExtensionFunction, memLp_indicator_iff_restrict measurableSet_Icc]
  exact Lp.memLp g

/-- The canonical isometric zero-extension map from `[0,1]` into the full-line
source Hilbert space. -/
noncomputable def positiveSourceExtension : UnitL2 →L[ℝ] FullLineL2 := by
  let L : UnitL2 →ₗ[ℝ] FullLineL2 := {
    toFun := fun g => (positiveSourceExtension_memLp g).toLp
      (positiveSourceExtensionFunction g)
    map_add' := by
      intro f g
      change (positiveSourceExtension_memLp (f+g)).toLp
        (positiveSourceExtensionFunction (f+g)) =
        (positiveSourceExtension_memLp f).toLp (positiveSourceExtensionFunction f) +
        (positiveSourceExtension_memLp g).toLp (positiveSourceExtensionFunction g)
      rw [← MemLp.toLp_add (positiveSourceExtension_memLp f)
        (positiveSourceExtension_memLp g)]
      apply MemLp.toLp_congr
      have hfg : (⇑(f + g) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
          (⇑f : ℝ → ℝ) + ⇑g := Lp.coeFn_add f g
      have hfg' := (ae_restrict_iff' measurableSet_Icc).1 hfg
      filter_upwards [hfg'] with u hu
      by_cases hs : u ∈ Set.Icc (0:ℝ) 1
      · simpa [positiveSourceExtensionFunction, Set.indicator_of_mem hs] using hu hs
      · simp [positiveSourceExtensionFunction, Set.indicator, hs]
    map_smul' := by
      intro c f
      change (positiveSourceExtension_memLp (c • f)).toLp
        (positiveSourceExtensionFunction (c • f)) =
        c • (positiveSourceExtension_memLp f).toLp (positiveSourceExtensionFunction f)
      rw [← MemLp.toLp_const_smul c (positiveSourceExtension_memLp f)]
      apply MemLp.toLp_congr
      have hcf : (⇑(c • f) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
          c • (⇑f : ℝ → ℝ) := Lp.coeFn_smul c f
      have hcf' := (ae_restrict_iff' measurableSet_Icc).1 hcf
      filter_upwards [hcf'] with u hu
      by_cases hs : u ∈ Set.Icc (0:ℝ) 1
      · simpa [positiveSourceExtensionFunction, Set.indicator_of_mem hs] using hu hs
      · simp [positiveSourceExtensionFunction, Set.indicator, hs]
  }
  refine L.mkContinuous 1 ?_
  intro g
  change ‖(positiveSourceExtension_memLp g).toLp
      (positiveSourceExtensionFunction g)‖ ≤ 1 * ‖g‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp (positiveSourceExtension_memLp g))]
  rw [positiveSourceExtensionFunction]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
  simp

theorem positiveSourceExtension_norm (g : UnitL2) :
    ‖positiveSourceExtension g‖ = ‖g‖ := by
  unfold positiveSourceExtension
  change ‖(positiveSourceExtension_memLp g).toLp
    (positiveSourceExtensionFunction g)‖ = ‖g‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp (positiveSourceExtension_memLp g))]
  rw [positiveSourceExtensionFunction]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]

/-- Pairing a whole-line feature with a zero-extended positive-time source is
the same as pairing its restriction with that source. -/
theorem positiveSourceExtension_inner (F : FullLineL2) (g : UnitL2) :
    ⟪F, positiveSourceExtension g⟫ =
      ⟪restrictUnitCLM F, g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  simp only [Real.inner_apply]
  have hJ : (positiveSourceExtension g : ℝ → ℝ) =ᵐ[volume]
      positiveSourceExtensionFunction g := by
    change ((positiveSourceExtension_memLp g).toLp
      (positiveSourceExtensionFunction g) : ℝ → ℝ) =ᵐ[volume]
      positiveSourceExtensionFunction g
    exact MemLp.coeFn_toLp (positiveSourceExtension_memLp g)
  calc
    (∫ u, (F : ℝ → ℝ) u * (positiveSourceExtension g : ℝ → ℝ) u ∂volume) =
        ∫ u, (Set.Icc (0:ℝ) 1).indicator
          (fun u => (F : ℝ → ℝ) u * (g : ℝ → ℝ) u) u ∂volume := by
      apply integral_congr_ae
      filter_upwards [hJ] with u hu
      by_cases hs : u ∈ Set.Icc (0:ℝ) 1
      · rw [hu]
        simp [positiveSourceExtensionFunction, Set.indicator_of_mem hs]
      · have hzero : (positiveSourceExtension g : ℝ → ℝ) u = 0 := by
          rw [hu]
          simp [positiveSourceExtensionFunction, Set.indicator, hs]
        simp [Set.indicator, hs, hzero]
    _ = ∫ u, (F : ℝ → ℝ) u * (g : ℝ → ℝ) u ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ u, (restrictUnitCLM F : ℝ → ℝ) u * (g : ℝ → ℝ) u ∂
        (volume.restrict (Set.Icc (0:ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := 1)
        (by simp) (by simpa using (Measure.restrict_le_self :
          volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume)) F] with u hu
      have hu' : (restrictUnitCLM F : ℝ → ℝ) u = (F : ℝ → ℝ) u := by
        simpa only [restrictUnitCLM] using hu
      rw [hu']

/-- An actual MvN feature vector, constructed only from a proved `L²`
membership certificate for the corresponding full-line kernel. -/
def mvNFullFeature (p t : ℝ)
    (h : MemLp (mvNFullKernel p t) 2 volume) : FullLineL2 :=
  h.toLp (mvNFullKernel p t)

@[simp] theorem mvNFullFeature_ae (p t : ℝ)
    (h : MemLp (mvNFullKernel p t) 2 volume) :
    mvNFullFeature p t h =ᵐ[volume] mvNFullKernel p t :=
  MemLp.coeFn_toLp h

theorem mvNFullFeature_norm_sq (p t : ℝ)
    (h : MemLp (mvNFullKernel p t) 2 volume) :
    ‖mvNFullFeature p t h‖^2 = ∫ u : ℝ, (mvNFullKernel p t u)^2 := by
  exact toLp_norm_sq h

/-- Stationary-increment identity for the full MvN kernel.  The negative
source-time correction is what makes this exact identity hold. -/
theorem mvNFullKernel_increment_shift (p s t u : ℝ) :
    mvNFullKernel p t u - mvNFullKernel p s u =
      mvNFullKernel p (t-s) (u-s) := by
  simp only [mvNFullKernel]
  have h₁ : t-u = (t-s) - (u-s) := by ring
  have h₂ : s-u = -(u-s) := by ring
  rw [h₁, h₂]
  ring

/-- The full MvN kernel is the sum of the positive-source causal part and
the reflected negative-time tail, up to the single irrelevant source point
at zero. -/
theorem mvNFullKernel_eq_positive_add_past_ae {H t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    mvNFullKernel (H-1/2) t =ᵐ[volume]
      (fun u : ℝ => mvNPositiveKernel (H-1/2) t u + pastTailKernel H t u) := by
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (0:ℝ)] with u hu
  by_cases hune : u < 0
  · have htu : 0 < t-u := by linarith [ht.1, hune]
    have hmu : 0 < -u := by linarith [hune]
    have hu' : ¬0 < u := by linarith
    simp [mvNFullKernel, mvNPower, mvNPositiveKernel, pastTailKernel,
      pastTailPower, hune, hu', htu, hmu]
    rw [show -u+t = t-u by ring]
  · have hu0 : 0 < u := lt_of_le_of_ne (le_of_not_gt hune) (Ne.symm hu)
    have hneg : ¬0 < -u := by linarith
    simp [mvNFullKernel, mvNPower, mvNPositiveKernel, pastTailKernel,
      hune, hu0, hneg]

/-- Actual full-line `L²` membership of the MvN feature for every Hurst
parameter in `(0,1)` and every time in `[0,1]`. This joins the positive
causal kernel and the separately controlled negative-time correction. -/
theorem mvNFullKernel_memLp {H t : ℝ} (hH : 0 < H) (hH1 : H < 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    MemLp (mvNFullKernel (H-1/2) t) 2 volume := by
  have hp : MemLp (mvNPositiveKernel (H-1/2) t) 2 volume :=
    mvNPositiveKernel_memLp (by linarith) ht.2
  have hq : MemLp (pastTailKernel H t) 2 volume :=
    pastTailKernel_memLp hH hH1 ht
  have hsum := hp.add hq
  have heq := mvNFullKernel_eq_positive_add_past_ae (H:=H) (t:=t) ht
  change eLpNorm (mvNFullKernel (H-1/2) t) 2 volume < ⊤
  rw [eLpNorm_congr_ae heq]
  exact hsum

/-- The squared distance between two full-line MvN feature vectors is the
squared norm of the increment-time feature.  This is the analytic stationary
increments identity, proved using actual whole-line integrals. -/
theorem mvNFullFeature_increment_norm_sq (p s t : ℝ)
    (hs : MemLp (mvNFullKernel p s) 2 volume)
    (ht : MemLp (mvNFullKernel p t) 2 volume)
    (hd : MemLp (mvNFullKernel p (t-s)) 2 volume) :
    ‖mvNFullFeature p t ht - mvNFullFeature p s hs‖^2 =
      ‖mvNFullFeature p (t-s) hd‖^2 := by
  have hshift : (fun u : ℝ =>
      ((mvNFullFeature p t ht - mvNFullFeature p s hs) u)^2) =ᵐ[volume]
      (fun u : ℝ => (mvNFullKernel p (t-s) (u-s))^2) := by
    filter_upwards [Lp.coeFn_sub (mvNFullFeature p t ht) (mvNFullFeature p s hs),
      MemLp.coeFn_toLp ht, MemLp.coeFn_toLp hs] with u hsub hut hus
    rw [hsub]
    change ((MemLp.toLp (mvNFullKernel p t) ht) u -
      (MemLp.toLp (mvNFullKernel p s) hs) u)^2 = _
    rw [hut, hus]
    rw [mvNFullKernel_increment_shift]
  calc
    ‖mvNFullFeature p t ht - mvNFullFeature p s hs‖^2 =
        ∫ u : ℝ, (mvNFullFeature p t ht - mvNFullFeature p s hs) u ^ 2 :=
          wholeLineL2_norm_sq _
    _ =
        ∫ u : ℝ, (mvNFullKernel p (t-s) (u-s))^2 := by
          exact integral_congr_ae hshift
    _ = ∫ u : ℝ, (mvNFullKernel p (t-s) u)^2 :=
          translated_square_integral (mvNFullKernel p (t-s)) s
    _ = ∫ u : ℝ, (mvNFullFeature p (t-s) hd) u ^ 2 := by
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hd] with u hu
          change (mvNFullKernel p (t-s) u)^2 =
            ((MemLp.toLp (mvNFullKernel p (t-s)) hd) u)^2
          rw [hu]
    _ = ‖mvNFullFeature p (t-s) hd‖^2 :=
          (wholeLineL2_norm_sq (mvNFullFeature p (t-s) hd)).symm

/-- The feature at time zero is the zero vector pointwise. -/
theorem mvNFullKernel_zero (p u : ℝ) : mvNFullKernel p 0 u = 0 := by
  simp [mvNFullKernel]

/-- Kernel scaling for all nonnegative time parameters, with the zero case
isolated so no rpow law at a vanishing dilation is needed. -/
theorem mvNFullKernel_scale_nonneg {p t u : ℝ} (ht : 0 ≤ t) (hp : p ≠ 0) :
    mvNFullKernel p t (t*u) = t^p * mvNFullKernel p 1 u := by
  by_cases htz : t=0
  · subst t
    simp [mvNFullKernel, hp]
  · exact mvNFullKernel_scale (lt_of_le_of_ne ht (Ne.symm htz))

/-- The pointwise increment identity in the opposite time ordering is the
same identity with the two endpoints exchanged. -/
theorem mvNFullKernel_increment_shift_symm (p s t u : ℝ) :
    mvNFullKernel p s u - mvNFullKernel p t u =
      mvNFullKernel p (s-t) (u-t) :=
  mvNFullKernel_increment_shift p t s u

/-- Exact self-similar `L²` norm scaling of the full MvN feature, derived
from its actual pointwise homogeneous kernel and Lebesgue dilation. -/
theorem mvNFullFeature_norm_scale {p t : ℝ} (ht : 0 < t)
    (h1 : MemLp (mvNFullKernel p 1) 2 volume)
    (hT : MemLp (mvNFullKernel p t) 2 volume) :
    ‖mvNFullFeature p t hT‖^2 = t^(2*p+1) * ‖mvNFullFeature p 1 h1‖^2 := by
  apply homogeneous_toLp_norm_sq h1 hT ht p
  intro u
  have hdiv : t * (u/t) = u := by field_simp [ne_of_gt ht]
  simpa only [hdiv] using
    (mvNFullKernel_scale (p:=p) (u:=u/t) ht)

/-- Self-similar feature norm for the MvN family at nonnegative times. -/
theorem mvNFullFeature_norm_sq_time (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1)
    (hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      MemLp (mvNFullKernel (H-1/2) t) 2 volume)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖mvNFullFeature (H-1/2) t (hmem t ht0 ht1)‖^2 =
      t^(2*H) * ‖mvNFullFeature (H-1/2) 1
        (hmem 1 (by norm_num) (by norm_num))‖^2 := by
  by_cases htz : t=0
  · subst t
    have hpow : (0:ℝ)^(2*H)=0 := Real.zero_rpow (by linarith)
    rw [hpow]
    rw [mvNFullFeature_norm_sq]
    simp [mvNFullKernel, mvNPower]
  · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
    rw [mvNFullFeature_norm_scale htp
      (hmem 1 (by norm_num) (by norm_num)) (hmem t ht0 ht1)]
    congr 1
    congr 1
    ring

/-- The actual whole-line MvN feature Gram identity, obtained by polarization
from its proved self-similar norms and stationary increments.  The scalar
factor is the squared norm of the unit-time feature. -/
theorem mvNFullFeature_gram_eq_covariance (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1)
    (hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      MemLp (mvNFullKernel (H-1/2) t) 2 volume)
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ⟪mvNFullFeature (H-1/2) s (hmem s hs0 hs1),
      mvNFullFeature (H-1/2) t (hmem t ht0 ht1)⟫ =
      ‖mvNFullFeature (H-1/2) 1 (hmem 1 (by norm_num) (by norm_num))‖^2 *
        BrownianSharp.AlignmentGaussianRates.fractionalCoordinateCovariance H s t := by
  let Fs := mvNFullFeature (H-1/2) s (hmem s hs0 hs1)
  let Ft := mvNFullFeature (H-1/2) t (hmem t ht0 ht1)
  let C := ‖mvNFullFeature (H-1/2) 1
        (hmem 1 (by norm_num) (by norm_num))‖^2
  have hns := mvNFullFeature_norm_sq_time H hH0 hH1 hmem s hs0 hs1
  have hnt := mvNFullFeature_norm_sq_time H hH0 hH1 hmem t ht0 ht1
  have hnd : ‖Fs-Ft‖^2 = C*|s-t|^(2*H) := by
    by_cases hst : s ≤ t
    · have hd0 : 0 ≤ t-s := sub_nonneg.mpr hst
      have hd1 : t-s ≤ 1 := by linarith
      have hdelta := mvNFullFeature_increment_norm_sq (H-1/2) s t
        (hmem s hs0 hs1) (hmem t ht0 ht1) (hmem (t-s) hd0 hd1)
      change ‖mvNFullFeature (H-1/2) s (hmem s hs0 hs1) -
          mvNFullFeature (H-1/2) t (hmem t ht0 ht1)‖^2 = _
      rw [norm_sub_rev, hdelta,
        mvNFullFeature_norm_sq_time H hH0 hH1 hmem (t-s) hd0 hd1]
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      dsimp [C]
      ring_nf
    · have hts : t ≤ s := le_of_not_ge hst
      have hd0 : 0 ≤ s-t := sub_nonneg.mpr hts
      have hd1 : s-t ≤ 1 := by linarith
      have hdelta := mvNFullFeature_increment_norm_sq (H-1/2) t s
        (hmem t ht0 ht1) (hmem s hs0 hs1) (hmem (s-t) hd0 hd1)
      change ‖mvNFullFeature (H-1/2) s (hmem s hs0 hs1) -
          mvNFullFeature (H-1/2) t (hmem t ht0 ht1)‖^2 = _
      rw [hdelta, mvNFullFeature_norm_sq_time H hH0 hH1 hmem (s-t) hd0 hd1]
      rw [abs_of_nonneg hd0]
      dsimp [C]
      ring_nf
  have hpolar : ‖Fs-Ft‖^2 = ‖Fs‖^2+‖Ft‖^2-2*⟪Fs,Ft⟫ := by
    rw [norm_sub_sq_real]
    ring
  rw [BrownianSharp.AlignmentGaussianRates.fractionalCoordinateCovariance]
  dsimp [Fs, Ft, C] at hnd ⊢
  rw [hns, hnt, hnd] at hpolar
  nlinarith

/-- Unconditional actual MvN feature Gram identity in the full Hurst range.
The `L²` hypotheses are discharged by the positive/past source decomposition
above, not assumed as an axiom. -/
theorem mvNFullFeature_gram_actual (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ⟪mvNFullFeature (H-1/2) s (mvNFullKernel_memLp hH0 hH1 ⟨hs0,hs1⟩),
      mvNFullFeature (H-1/2) t (mvNFullKernel_memLp hH0 hH1 ⟨ht0,ht1⟩)⟫ =
      ‖mvNFullFeature (H-1/2) 1
        (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖^2 *
        BrownianSharp.AlignmentGaussianRates.fractionalCoordinateCovariance H s t := by
  let hm : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      MemLp (mvNFullKernel (H-1/2) τ) 2 volume :=
    fun τ hτ0 hτ1 => mvNFullKernel_memLp hH0 hH1 ⟨hτ0,hτ1⟩
  exact mvNFullFeature_gram_eq_covariance H hH0 hH1 hm s t hs0 hs1 ht0 ht1

/-- Pairing the actual causal RL kernel vector against a source vector is the
same as evaluation of the bounded RL operator. -/
theorem kernelVector_inner_eq_fractionalRL (α : ℝ) (hα : 1/2 < α)
    (g : UnitL2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ⟪kernelVector α t hα ht0 ht1, g⟫ =
      fractionalRL α hα g (⟨t, ⟨ht0, ht1⟩⟩ : UnitInterval) := by
  rw [fractionalRL_apply α hα g t ht0 ht1, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (causalKernel_memLp_unit hα ht0 ht1)]
    with u hu
  simp only [Real.inner_apply]
  have hu' : (kernelVector α t hα ht0 ht1 : ℝ → ℝ) u = causalKernel α t u := by
    simpa [kernelVector] using hu
  rw [hu']

/-- Unit-variance-normalized MvN feature field. Its factor is the actual
positive norm of the full feature at time one. -/
noncomputable def mvNNormalizedFeature (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : FullLineL2 :=
  ‖mvNFullFeature (H-1/2) 1
    (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖⁻¹ •
    mvNFullFeature (H-1/2) t (mvNFullKernel_memLp hH0 hH1 ⟨ht0,ht1⟩)

/-- On positive-time sources, the normalized MvN feature is exactly the
Riemann--Liouville evaluation multiplied by the explicit normalization
constant `Gamma(H+1/2) / ||F_1||`. -/
theorem mvNNormalizedFeature_positiveSource_factor (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (g : UnitL2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ⟪mvNNormalizedFeature H hH0 hH1 t ht0 ht1, positiveSourceExtension g⟫ =
      (Real.Gamma (H+1/2) *
        ‖mvNFullFeature (H-1/2) 1
          (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖⁻¹) *
        fractionalRL (H+1/2) (by linarith) g ⟨t, ⟨ht0,ht1⟩⟩ := by
  let hmem := mvNFullKernel_memLp hH0 hH1 ⟨ht0,ht1⟩
  let hmem1 := mvNFullKernel_memLp hH0 hH1
    (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
  let N := ‖mvNFullFeature (H-1/2) 1 hmem1‖
  have hfactor := restrict_mvNFullKernel_eq_RL (p := H-1/2) (t := t)
    (by linarith) ht0 ht1 hmem
  have hfactor' : restrictUnitCLM (mvNFullFeature (H-1/2) t hmem) =
      Real.Gamma (H-1/2+1) • kernelVector (H-1/2+1) t (by linarith) ht0 ht1 := by
    simpa [mvNFullFeature] using hfactor
  have hfactor'' : restrictUnitCLM (mvNFullFeature (H-1/2) t hmem) =
      Real.Gamma (H+1/2) • kernelVector (H+1/2) t (by linarith) ht0 ht1 := by
    simpa only [show H-1/2+1 = H+1/2 by ring] using hfactor'
  change ⟪N⁻¹ • mvNFullFeature (H-1/2) t hmem,
      positiveSourceExtension g⟫ = _
  rw [real_inner_smul_left, positiveSourceExtension_inner, hfactor'',
    real_inner_smul_left,
    kernelVector_inner_eq_fractionalRL (H+1/2) (by linarith) g t ht0 ht1]
  dsimp [N, hmem1]
  ring

/-- After normalization by its nonzero unit-time norm, the actual MvN
feature's Gram kernel is exactly the fBm covariance, including H below one
half. -/
theorem mvNNormalizedFeature_gram_eq_covariance (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ⟪mvNNormalizedFeature H hH0 hH1 s hs0 hs1,
      mvNNormalizedFeature H hH0 hH1 t ht0 ht1⟫ =
        BrownianSharp.AlignmentGaussianRates.fractionalCoordinateCovariance H s t := by
  let N := ‖mvNFullFeature (H-1/2) 1
    (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖
  have hNpos : 0 < N := by
    dsimp [N]
    exact mvNFullKernel_one_norm_pos (H-1/2)
      (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)
  have hgram := mvNFullFeature_gram_actual H hH0 hH1 s t hs0 hs1 ht0 ht1
  change ⟪N⁻¹ • mvNFullFeature (H-1/2) s
      (mvNFullKernel_memLp hH0 hH1 ⟨hs0,hs1⟩),
    N⁻¹ • mvNFullFeature (H-1/2) t
      (mvNFullKernel_memLp hH0 hH1 ⟨ht0,ht1⟩)⟫ = _
  rw [real_inner_smul_left, real_inner_smul_right, hgram]
  have hN : ‖mvNFullFeature (H-1/2) 1
      (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖ = N := rfl
  rw [hN]
  field_simp [ne_of_gt hNpos]


end BrownianSharp.AlignmentFractionalSheetMvNGram
