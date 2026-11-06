import BrownianSharp.AlignmentPaperFractionalFourierBridge
import BrownianSharp.AlignmentFractionalTail

/-! Fourier-derived membership and scaling estimates for the causal RL
profile. The source is compactly supported, so the global Fatou/Plancherel
bound itself supplies the L² membership used by the dilation argument. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace BrownianSharp.AlignmentPaperFractionalFourierMembership

open BrownianSharp.AlignmentFractionalTail
open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentPaperFractionalFourier
open BrownianSharp.AlignmentPaperFractionalFourierBridge
open BrownianSharp.AlignmentPaperFractionalSchwartzSource
open BrownianSharp.AlignmentFractionalDensity

/-- The actual zero-extended causal profile is L² by the Fourier/Fatou
estimate. Measurability is supplied by the causal-profile definition. -/
theorem causalRLProfile_fourier_memLp_two {q : ℕ} {r β : ℝ}
    (hr : 0 < r) (hrq : r < q) (hβq : β = (q : ℝ) - r)
    (hβhalf : 1/2 < β) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupport : Function.support F ⊆ Set.Icc (0 : ℝ) 1) :
    AEStronglyMeasurable
        (fun t : ℝ => (causalRLProfile β (iteratedDeriv q F) t : ℂ)) volume ∧
      MemLp (fun t : ℝ => (causalRLProfile β (iteratedDeriv q F) t : ℂ))
        2 volume := by
  have hFq : Continuous (iteratedDeriv q F) := by
    simpa only [iteratedDeriv_eq_iterate] using
      (ContDiff.iterate_deriv q hF).continuous
  have hprofileMeas : Measurable (causalRLProfile β (iteratedDeriv q F)) :=
    causalRLProfile_measurable hβhalf (iteratedDeriv q F) hFq
  have hprofileAes : AEStronglyMeasurable
      (fun t : ℝ => (causalRLProfile β (iteratedDeriv q F) t : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp hprofileMeas).aestronglyMeasurable
  have hglobal := causalRLProfile_global_eLpNorm_le_fractionalFourierWeight
    hr hrq hβq hβhalf F hF hFsupport
  have hweight : MemLp
      (fun ξ : ℝ => (2 * Real.pi * |ξ|)^r *
        ‖𝓕 (realCompactSchwartz F hF
          (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hFsupport)) ξ‖)
      2 volume := by
    exact fractionalFourierWeight_memLp_two hr hrq
      (realCompactSchwartz F hF
        (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hFsupport))
  have hfinite : MeasureTheory.eLpNorm
      (fun t : ℝ => (causalRLProfile β (iteratedDeriv q F) t : ℂ)) 2 volume < ⊤ :=
    lt_of_le_of_lt hglobal hweight.eLpNorm_lt_top
  exact ⟨hprofileAes, hfinite⟩

/-- A finite-horizon RL energy is bounded by the global profile energy when
the latter's L² membership comes from the Fourier Fatou bound. -/
theorem rlIntegral_finite_energy_le_global_of_fourier {β : ℝ}
    (hβ : 1/2 < β) (q : ℕ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hmem : MemLp
      (fun t : ℝ => (causalRLProfile β (iteratedDeriv q F) t : ℂ)) 2 volume)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, (rlIntegral β (iteratedDeriv q F) t)^2) ≤
      ∫ t, (causalRLProfile β (iteratedDeriv q F) t)^2 ∂(volume : Measure ℝ) := by
  have hFq : Continuous (iteratedDeriv q F) := by
    simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv q hF).continuous
  let G : ℝ → ℝ := causalRLProfile β (iteratedDeriv q F)
  let G2 : ℝ → ℝ := fun t => (G t)^2
  have hnormMem : MemLp (fun t : ℝ => ‖(G t : ℂ)‖) 2 volume := hmem.norm
  have hsqNorm : Integrable (fun t : ℝ => ‖(G t : ℂ)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hnormMem.aestronglyMeasurable).mp hnormMem
  have hsq : Integrable G2 volume := by
    apply hsqNorm.congr
    filter_upwards with t
    simp [G2, G, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hIoc :
      (∫ t in Set.Ioc (0 : ℝ) T, (rlIntegral β (iteratedDeriv q F) t)^2) =
        ∫ t in Set.Ioc (0 : ℝ) T, G2 t ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    simp [G2, G, causalRLProfile, not_le.mpr ht0]
  calc
    (∫ t in (0 : ℝ)..T, (rlIntegral β (iteratedDeriv q F) t)^2) =
        ∫ t in Set.Ioc (0 : ℝ) T, (rlIntegral β (iteratedDeriv q F) t)^2 :=
      intervalIntegral.integral_of_le (μ := volume)
        (f := fun t => (rlIntegral β (iteratedDeriv q F) t)^2) hT.le
    _ = ∫ t in Set.Ioc (0 : ℝ) T, G2 t ∂volume := hIoc
    _ ≤ ∫ t, G2 t ∂volume :=
      setIntegral_le_integral hsq (ae_of_all _ fun t => sq_nonneg (G t))
    _ = ∫ t, (causalRLProfile β (iteratedDeriv q F) t)^2 ∂volume := rfl

/-- Shifted smooth-atom preimages with the global-energy step supplied by
Fourier-derived L² membership, without the separate tail-decay membership
argument. -/
theorem smooth_atom_shift_preimage_norm_sq_le_fourier {α β c m : ℝ}
    (hα : 1/2 < α) (q : ℕ) (hqα : α < q) (hβ : 1/2 < β)
    (hβq : β = (q : ℝ) - α) (hc : 0 < c) (hm : 0 ≤ m) (hmc : m < c)
    (F : ℝ → ℝ) (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hleft : ∀ x ≤ 0, iteratedDeriv q F x = 0)
    (hFsupport : Function.support F ⊆ Set.Icc (0 : ℝ) 1) :
    ‖profileToL2 (fractionalOnC β hβ
      (derivativeProfile q (fun x => F (c*x-m))
        (hF.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))))‖^2 ≤
      c^(2*α-1) *
        (∫ t, (causalRLProfile β (iteratedDeriv q F) t)^2 ∂(volume : Measure ℝ)) := by
  have hmem := causalRLProfile_fourier_memLp_two
    (q := q) (r := α) (β := β) (by linarith) hqα hβq hβ F hF hFsupport
  have hmc_le : m ≤ c := le_of_lt hmc
  have hT : 0 < c-m := sub_pos.mpr hmc
  rw [smooth_atom_shift_preimage_norm_sq hα q hqα hβ hβq hc hm hmc_le
    F hF hleft]
  exact mul_le_mul_of_nonneg_left
    (rlIntegral_finite_energy_le_global_of_fourier hβ q F hF hmem.2 (c-m) hT)
    (Real.rpow_nonneg hc.le _)

end BrownianSharp.AlignmentPaperFractionalFourierMembership
