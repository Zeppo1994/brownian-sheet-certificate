import BrownianSharp.AlignmentFractionalSheetRKHS
import BrownianSharp.AlignmentRealL2Scaling

/-! Positive-time MvN source features and their literal RL restriction. -/
noncomputable section
open MeasureTheory
namespace BrownianSharp.AlignmentFractionalSheetPositive
open AlignmentFractionalSheetRKHS AlignmentFractionalKernel
open AlignmentFractionalL2 AlignmentFractionalTranslation

def mvNPositiveKernel (p t u : ℝ) : ℝ :=
  if 0 < u then mvNPower p (t-u) else 0

theorem mvNPositiveKernel_eq_indicator {p t : ℝ} (hp : -(1/2:ℝ) < p)
    (ht1 : t ≤ 1) (u : ℝ) :
    mvNPositiveKernel p t u =
      (Set.Ioi (0:ℝ)).indicator
        (fun u => Real.Gamma (p+1)*kernelCut (p+1) (t-u)) u := by
  have hΓ : Real.Gamma (p+1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  by_cases hu : 0 < u
  · rw [mvNPositiveKernel,if_pos hu]
    simp only [Set.indicator, Set.mem_Ioi, if_pos hu]
    by_cases hut : u < t
    · have hx : 0 < t-u := sub_pos.mpr hut
      have hx1 : t-u ≤ 1 := by linarith
      have hmem : t-u ∈ Set.Ioc (0:ℝ) 1 := ⟨hx,hx1⟩
      rw [mvNPower,if_pos hx,kernelCut,Set.indicator_of_mem hmem,kernel]
      rw [show p+1-1=p by ring]
      field_simp
    · have hx : t-u ≤ 0 := sub_nonpos.mpr (le_of_not_gt hut)
      simp [mvNPower,not_lt.mpr hx,kernelCut,Set.mem_Ioc,hx]
  · simp [mvNPositiveKernel,hu]

theorem mvNPositiveKernel_memLp {p t : ℝ} (hp : -(1/2:ℝ) < p)
    (ht1 : t ≤ 1) : MemLp (mvNPositiveKernel p t) 2 (volume : Measure ℝ) := by
  have hα : 1/2 < p+1 := by linarith
  have hc := (kernelCut_memLp hα).comp_measurePreserving
    (reflectionTranslation_measurePreserving t)
  have hcc : MemLp (fun u : ℝ => Real.Gamma (p+1)*kernelCut (p+1) (t-u)) 2 volume := by
    simpa only [Function.comp_apply,reflectionTranslation,ContinuousMap.coe_mk] using
      hc.const_mul (Real.Gamma (p+1))
  have hi := hcc.indicator (s := Set.Ioi (0:ℝ)) measurableSet_Ioi
  convert hi using 1
  funext u
  exact mvNPositiveKernel_eq_indicator hp ht1 u

theorem mvNFullKernel_eq_Gamma_causal {p t u : ℝ} (hp : -(1/2:ℝ) < p)
    (hu0 : 0 ≤ u) :
    mvNFullKernel p t u = Real.Gamma (p+1)*causalKernel (p+1) t u := by
  have hΓ : Real.Gamma (p+1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hneg : ¬0 < -u := by linarith
  by_cases hut : u < t
  · have hpos : 0 < t-u := sub_pos.mpr hut
    rw [mvNFullKernel,mvNPower,if_pos hpos,mvNPower,if_neg hneg,sub_zero,
      causalKernel,if_pos hut,kernel]
    rw [show p+1-1=p by ring]
    field_simp
  · have hpos : ¬0 < t-u := by linarith
    simp [mvNFullKernel,mvNPower,hpos,hneg,causalKernel,hut]

theorem restrict_mvNFullKernel_eq_RL {p t : ℝ} (hp : -(1/2:ℝ) < p)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hf : MemLp (mvNFullKernel p t) 2 (volume : Measure ℝ)) :
    restrictUnitCLM (hf.toLp (mvNFullKernel p t)) =
      Real.Gamma (p+1) • kernelVector (p+1) t (by linarith) ht0 ht1 := by
  apply Lp.ext
  let hα : 1/2 < p+1 := by linarith
  have hr : restrictUnitCLM (hf.toLp (mvNFullKernel p t)) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)] hf.toLp (mvNFullKernel p t) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := 1) (by simp)
      (by simpa using (Measure.restrict_le_self :
        volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume)) _
  have hfe := ae_mono (Measure.restrict_le_self :
    volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume) (MemLp.coeFn_toLp hf)
  have hk : (kernelVector (p+1) t hα ht0 ht1 : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)] causalKernel (p+1) t := by
    exact MemLp.coeFn_toLp (causalKernel_memLp_unit hα ht0 ht1)
  have hs := Lp.coeFn_smul (Real.Gamma (p+1)) (kernelVector (p+1) t hα ht0 ht1)
  filter_upwards [hr,hfe,hk,hs,ae_restrict_mem measurableSet_Icc]
    with u hru hfu hku hsu hu
  rw [hru,hfu,hsu]
  change mvNFullKernel p t u =
    Real.Gamma (p+1)*(kernelVector (p+1) t hα ht0 ht1) u
  rw [hku]
  exact mvNFullKernel_eq_Gamma_causal hp hu.1

theorem mvNFullKernel_one_positive {p u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) (1/2)) :
    0 < mvNFullKernel p 1 u := by
  have hpos : 0 < 1-u := by linarith [hu.2]
  have hneg : ¬0 < -u := by linarith [hu.1]
  simp only [mvNFullKernel,mvNPower,if_pos hpos,if_neg hneg,sub_zero]
  exact Real.rpow_pos_of_pos hpos p

theorem mvNFullKernel_one_norm_pos (p : ℝ)
    (hf : MemLp (mvNFullKernel p 1) 2 (volume : Measure ℝ)) :
    0 < ‖hf.toLp (mvNFullKernel p 1)‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hz : mvNFullKernel p 1 =ᵐ[volume] (0 : ℝ → ℝ) :=
    (MemLp.coeFn_toLp hf).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  have hnull : volume {u : ℝ | mvNFullKernel p 1 u ≠ 0} = 0 := ae_iff.mp hz
  have hsub : Set.Ioo (0:ℝ) (1/2) ⊆ {u : ℝ | mvNFullKernel p 1 u ≠ 0} := by
    intro u hu
    exact ne_of_gt (mvNFullKernel_one_positive hu)
  have hvol : volume (Set.Ioo (0:ℝ) (1/2)) = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hnull) bot_le
  norm_num [Real.volume_Ioo] at hvol

end BrownianSharp.AlignmentFractionalSheetPositive
