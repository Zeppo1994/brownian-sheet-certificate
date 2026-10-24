import BrownianSharp.PeriodicMixedFinal
import BrownianSharp.AlignmentPeriodicWindowEntropy
import BrownianSharp.AlignmentFractionalSheetRKHS

/-! A bounded periodic Sobolev source embedding supplies the sharp feature-ball
entropy lower bound. The embedding remains an explicit input in this generic
lemma and is discharged by the Matérn spectral-window construction. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal
namespace BrownianSharp.AlignmentPeriodicFeatureEntropy
open Torus SmoothResolution AlignmentFractionalSheetRKHS
open AlignmentPeriodicCubeRestriction AlignmentPeriodicWindowEntropy

theorem entropyNumber_mono {X : Type*} [PseudoEMetricSpace X]
    {K J : Set X} (hK : K ⊆ J) (k : ℕ) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ HaarQuarter.TheoremD.entropyNumber k J := by
  unfold HaarQuarter.TheoremD.entropyNumber
  apply le_sInf
  rintro q ⟨ρ,rfl,hcover⟩
  exact sInf_le ⟨ρ,rfl,(Metric.externalCoveringNumber_mono_set hK).trans hcover⟩

theorem feature_entropy_lower_of_periodic_embedding
    {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (hd : 2 ≤ d) (r : ℝ) (hr : 1/2 < r)
    (K : C(BrownianCubeAnchor d,H)) (w : C(BrownianCubeAnchor d,ℝ))
    (c A : ℝ) (hc : 0 < c) (hA : 0 < A) (hw : ∀ t, c ≤ ‖w t‖)
    (hembed : ∀ f : RealPeriodic d, SobolevUnitBall 2 r f →
      ∃ z : H, ‖z‖ ≤ A ∧ featureOperator K z = weightedCubeRestriction w f) :
    ∃ cE : ℝ, 0 < cE ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (cE*logarithmicIndexRate r (r*(d-1:ℕ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (featureOperator K '' Metric.closedBall (0:H) 1) := by
  have hpr : (2:ℝ)⁻¹ < r := by norm_num; exact hr
  obtain ⟨cP,hcP,k₀,hk₀,hP⟩ := periodicMixedEntropy_certified d hd 2 r
    (by norm_num) hpr (2:ENNReal) (by norm_num)
  let u : C(BrownianCubeAnchor d,ℝ) := A⁻¹ • w
  have hu : ∀ t, c/A ≤ ‖u t‖ := by
    intro t
    simp only [u,ContinuousMap.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hA)]
    have ht := mul_le_mul_of_nonneg_left (hw t) (inv_pos.mpr hA).le
    simpa only [div_eq_mul_inv,mul_comm,Real.norm_eq_abs] using ht
  have hsub : weightedCubeRestriction u '' {f : RealPeriodic d | SobolevUnitBall 2 r f} ⊆
      featureOperator K '' Metric.closedBall (0:H) 1 := by
    rintro f ⟨v,hv,rfl⟩
    obtain ⟨z,hzn,hze⟩ := hembed v hv
    refine ⟨A⁻¹ • z,?_,?_⟩
    · rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hA)]
      have hz := mul_le_mul_of_nonneg_left hzn (inv_pos.mpr hA).le
      simpa [hA.ne'] using hz
    · rw [map_smul,hze]
      ext t
      simp [weightedCubeRestriction,u,smul_eq_mul,mul_assoc]
  let cE := (c/A)*cP/2
  refine ⟨cE,div_pos (mul_pos (div_pos hc hA) hcP) (by norm_num),k₀,hk₀,?_⟩
  intro k hk
  have hbound := weightedCubeRestriction_entropy_lower u (c/A) (div_pos hc hA) hu
    {f : RealPeriodic d | SobolevUnitBall 2 r f} k
    (cP*logarithmicIndexRate r (r*(d-1:ℕ)+1/2) k) (hP k hk).1
  have hfinal := hbound.trans (entropyNumber_mono hsub k)
  convert hfinal using 1
  dsimp [cE]
  congr 1
  ring

end BrownianSharp.AlignmentPeriodicFeatureEntropy
