import BrownianSharp.AlignmentPaperFractionalFourierBridge
import BrownianSharp.AlignmentPaperFractionalFourierMembership

/-! Dyadic smooth-atom preimages with their global source-energy constant
derived from the actual Fourier/Plancherel/Fatou bridge. -/
noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace BrownianSharp.AlignmentPaperFractionalFourierPreimage

open BrownianSharp.AlignmentFractionalTail
open BrownianSharp.AlignmentPaperFractionalFourierBridge
open BrownianSharp.AlignmentPaperFractionalFourierMembership
open BrownianSharp.AlignmentPaperFractionalSchwartzSource
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalTranslation

private theorem smoothAtom_support_Icc :
    Function.support BrownianSharp.smoothAtom ⊆ Set.Icc (0:ℝ) 1 := by
  intro x hx
  constructor
  · by_contra hn
    have hxneg : x < 0 := lt_of_not_ge hn
    exact hx (BrownianSharp.smoothAtom_support x (Or.inl hxneg.le))
  · by_contra hn
    have hpos : 1 < x := lt_of_not_ge hn
    exact hx (BrownianSharp.smoothAtom_support x (Or.inr hpos.le))

/-- Genuine dyadic fractional preimages, with the uniform constant supplied
by the actual Fourier-derived global causal-profile energy. -/
theorem smoothAtom_dyadic_fractional_preimage_fourier {α : ℝ}
    (hα : 1/2 < α) :
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ s : ℕ, ∀ m : ℕ, m < 2^s →
        ∃ g : UnitL2,
          BrownianSharp.AlignmentFractionalTranslation.fractionalRL α hα g =
            BrownianSharp.AlignmentFractionalDensity.restrictProfile
              (fun t => BrownianSharp.smoothAtom (((2^s:ℝ) * t) - m))
              ((BrownianSharp.smoothAtom_contDiff.comp
                ((contDiff_const.mul contDiff_id).sub contDiff_const)).continuous) ∧
          ‖g‖^2 ≤ Cα * (2:ℝ)^((2*α-1)*(s:ℝ)) := by
  let q : ℕ := Nat.ceil α + 2
  have hceilLower : α ≤ (Nat.ceil α:ℝ) := Nat.le_ceil α
  have hqα : α < (q:ℝ) := by
    dsimp [q]
    push_cast
    linarith [hceilLower]
  let β : ℝ := (q:ℝ)-α
  have hβ : 1/2 < β := by
    dsimp [β,q]
    push_cast
    linarith [hceilLower]
  have hβq : β = (q:ℝ)-α := rfl
  rcases smoothAtom_fractional_atom_conditions q with ⟨hzero,hSupport,hleft⟩
  have hαpos : 0 < α := by linarith
  have hatomSupport : Function.support BrownianSharp.smoothAtom ⊆ Set.Icc (0:ℝ) 1 :=
    smoothAtom_support_Icc
  let hcompact : HasCompactSupport BrownianSharp.smoothAtom :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hatomSupport
  let ψ : 𝓢(ℝ,ℂ) :=
    realCompactSchwartz BrownianSharp.smoothAtom BrownianSharp.smoothAtom_contDiff hcompact
  let W : ℝ → ℝ := fun ξ =>
    (2 * Real.pi * |ξ|)^α * ‖(𝓕 ψ) ξ‖
  let J : ℝ := ∫ ξ, W ξ ^ 2
  let E : ℝ := ∫ t,
    (causalRLProfile β (iteratedDeriv q BrownianSharp.smoothAtom) t)^2
      ∂(volume : Measure ℝ)
  have hJnonneg : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg_of_ae (ae_of_all _ fun ξ => sq_nonneg (W ξ))
  have hprofileFourier := causalRLProfile_fourier_memLp_two
    (q := q) (r := α) (β := β) hαpos hqα hβq hβ
    BrownianSharp.smoothAtom BrownianSharp.smoothAtom_contDiff smoothAtom_support_Icc
  have hprofileComplex : MemLp
      (fun t : ℝ => (causalRLProfile β
        (iteratedDeriv q BrownianSharp.smoothAtom) t : ℂ)) 2 volume :=
    hprofileFourier.2
  have hweightMem := fractionalFourierWeight_memLp_two hαpos hqα ψ
  have hglobal := causalRLProfile_global_eLpNorm_le_fractionalFourierWeight
    hαpos hqα hβq hβ BrownianSharp.smoothAtom
    BrownianSharp.smoothAtom_contDiff smoothAtom_support_Icc
  have hglobalWeight :
      MeasureTheory.eLpNorm
          (fun t : ℝ => (causalRLProfile β
            (iteratedDeriv q BrownianSharp.smoothAtom) t : ℂ)) 2 volume ≤
        MeasureTheory.eLpNorm W 2 volume := by
    apply hglobal.trans
    apply le_of_eq
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards with ξ
    simp [W, ψ, SchwartzMap.fourier_coe]
  have hEcomplex :
      (∫ t, ‖(causalRLProfile β
        (iteratedDeriv q BrownianSharp.smoothAtom) t : ℂ)‖ ^ (2:ℝ)) = E := by
    dsimp [E]
    apply integral_congr_ae
    filter_upwards with t
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hJnorm : (∫ ξ, ‖W ξ‖ ^ (2:ℝ)) = J := by
    dsimp [J]
    apply integral_congr_ae
    filter_upwards with ξ
    have hW : 0 ≤ W ξ := by
      dsimp [W]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
    simp [Real.norm_eq_abs, abs_of_nonneg hW]
  have hprofileFormula := hprofileComplex.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2:ENNReal) ≠ 0) (by norm_num : (2:ENNReal) ≠ ⊤)
  have hweightFormula := hweightMem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2:ENNReal) ≠ 0) (by norm_num : (2:ENNReal) ≠ ⊤)
  have hprofileRoot : MeasureTheory.eLpNorm
      (fun t : ℝ => (causalRLProfile β
        (iteratedDeriv q BrownianSharp.smoothAtom) t : ℂ)) 2 volume =
      ENNReal.ofReal (Real.sqrt E) := by
    rw [hprofileFormula]
    have hI :
        (∫ a, ‖(causalRLProfile β
          (iteratedDeriv q BrownianSharp.smoothAtom) a : ℂ)‖ ^
            ENNReal.toReal (2:ENNReal)) = E := by
      simpa using hEcomplex
    rw [hI]
    norm_num [Real.sqrt_eq_rpow]
  have hweightRoot : MeasureTheory.eLpNorm W 2 volume =
      ENNReal.ofReal (Real.sqrt J) := by
    have hformula : MeasureTheory.eLpNorm W 2 volume =
        ENNReal.ofReal
          ((∫ a, ‖W a‖ ^ ENNReal.toReal (2:ENNReal)) ^ (ENNReal.toReal (2:ENNReal))⁻¹) := by
      simpa only [W] using hweightFormula
    rw [hformula]
    have hI :
        (∫ a, ‖W a‖ ^ ENNReal.toReal (2:ENNReal)) = J := by
      simpa using hJnorm
    rw [hI]
    norm_num [Real.sqrt_eq_rpow]
  have hroot : Real.sqrt E ≤ Real.sqrt J := by
    have h := hglobalWeight
    rw [hprofileRoot, hweightRoot] at h
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg J)).mp h
  have hE_le_J : E ≤ J :=
    (Real.sqrt_le_sqrt_iff hJnonneg).mp hroot
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact integral_nonneg_of_ae (ae_of_all _ fun t =>
      sq_nonneg (causalRLProfile β (iteratedDeriv q BrownianSharp.smoothAtom) t))
  refine ⟨J+1, by linarith, ?_⟩
  intro s m hm
  let c : ℝ := (2^s:ℝ)
  let mR : ℝ := m
  have hc : 0 < c := by dsimp [c]; positivity
  have hmR : 0 ≤ mR := by dsimp [mR]; exact Nat.cast_nonneg _
  have hmc : mR < c := by
    dsimp [c,mR]
    exact_mod_cast hm
  let H : ℝ → ℝ := fun t => BrownianSharp.smoothAtom (c*t-mR)
  have hH : ContDiff ℝ (∞ : ℕ∞ω) H := by
    exact BrownianSharp.smoothAtom_contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hjet := shiftedSmoothAtom_jets_zero q hc hmR
  let g : UnitL2 := BrownianSharp.AlignmentFractionalDensity.profileToL2
    (BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ
      (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q H hH))
  have hpre :=
    BrownianSharp.AlignmentFractionalDensity.smooth_atom_fractional_preimage_L2
      α hα q hqα hβ H hH hjet
  have hbound := smooth_atom_shift_preimage_norm_sq_le_fourier
    hα q hqα hβ hβq hc hmR hmc BrownianSharp.smoothAtom
    BrownianSharp.smoothAtom_contDiff hleft hatomSupport
  have hboundE : ‖g‖^2 ≤ c^(2*α-1) * E := by
    simpa [g, H, E] using hbound
  have hpow : c^(2*α-1) = (2:ℝ)^((2*α-1)*(s:ℝ)) := by
    dsimp [c]
    rw [← Real.rpow_natCast (2:ℝ) s]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (s:ℝ) (2*α-1)]
    congr 1 <;> ring
  have hfinal : ‖g‖^2 ≤ (J+1) * (2:ℝ)^((2*α-1)*(s:ℝ)) := by
    calc
      ‖g‖^2 ≤ c^(2*α-1) * E := hboundE
      _ ≤ c^(2*α-1) * (J+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hc.le _)
      _ = (J+1) * (2:ℝ)^((2*α-1)*(s:ℝ)) := by rw [hpow, mul_comm]
  refine ⟨g, ?_, hfinal⟩
  change BrownianSharp.AlignmentFractionalTranslation.fractionalRL α hα
    (BrownianSharp.AlignmentFractionalDensity.profileToL2
      (BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ
        (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q H hH))) =
    BrownianSharp.AlignmentFractionalDensity.restrictProfile H hH.continuous
  exact hpre

end BrownianSharp.AlignmentPaperFractionalFourierPreimage
