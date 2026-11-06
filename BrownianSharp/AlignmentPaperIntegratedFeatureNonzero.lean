import BrownianSharp.AlignmentGaussianIntegratedSourceModel

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperIntegratedFeatureNonzero
open HaarQuarter AlignmentFractionalTensorOperator AlignmentGaussianBochner

def cubeCorner (d:ℕ):BrownianCubeAnchor d :=
  ⟨fun _=>1,fun _=>⟨by norm_num,by norm_num⟩⟩

/-- The true tensor RL evaluation feature at the upper cube corner is nonzero:
its Gamma-normalized kernel is positive throughout the open unit cube. -/
theorem tensorKernelFamily_corner_ne_zero {d:ℕ}
    (a:Fin d→ℝ) (ha:∀i,1/2<a i) :
    tensorKernelFamily a ha (cubeCorner d)≠0 := by
  let μ : Measure (Fin d→ℝ) :=
    (Measure.pi fun _:Fin d=>(volume:Measure ℝ)).restrict (CameronMartin.unitCubeSet d)
  let S:Set (Fin d→ℝ):=Set.pi Set.univ (fun _:Fin d=>Set.Ioo (0:ℝ) 1)
  have hS:MeasurableSet S := MeasurableSet.univ_pi (fun _=>measurableSet_Ioo)
  have hsub:S⊆CameronMartin.unitCubeSet d := by
    intro u hu i hi
    have h:=hu i (by simp)
    exact ⟨h.1.le,h.2.le⟩
  have hmass:μ S=1 := by
    rw [Measure.restrict_apply hS,Set.inter_eq_left.mpr hsub]
    simp [S,Measure.pi_pi,Real.volume_Ioo]
  have hpos:∀u∈S,0<Latest.fractionalTensorKernel a (cubeCorner d) u := by
    intro u hu
    apply Finset.prod_pos
    intro i hi
    have hui:=hu i (by simp)
    change 0<(if u i<1 then (Real.Gamma (a i))⁻¹*(1-u i)^(a i-1) else 0)
    rw [if_pos hui.2]
    exact mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith [ha i])))
      (Real.rpow_pos_of_pos (by linarith [hui.2]) _)
  intro hz
  have hae:Latest.fractionalTensorKernel a (cubeCorner d)=ᵐ[μ] (0:(Fin d→ℝ)→ℝ) :=
    (tensorKernelFamily_ae a ha (cubeCorner d)).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hz)
  have hnull:μ {u|Latest.fractionalTensorKernel a (cubeCorner d) u≠0}=0:=ae_iff.mp hae
  have hmass0:μ S=0:=le_antisymm
    ((measure_mono (fun u hu=>(hpos u hu).ne')).trans_eq hnull) bot_le
  rw [hmass] at hmass0
  exact one_ne_zero hmass0

/-- The actual integrated Brownian feature used in the covariance theorem
has a nonzero evaluation at the same corner. -/
theorem integratedFeatureField_corner_ne_zero {d:ℕ} (m:Fin d→ℕ) :
    integratedFeatureField m (cubeCorner d)≠0 := by
  intro hz
  have he:=AlignmentGaussianIntegratedSourceModel.integratedFeature_embedding_eq_kernel
    m (cubeCorner d)
  rw [hz,map_zero] at he
  have hn:=congrArg norm he
  change ‖(0:CameronMartin.AmbientL2 d)‖=
    ‖CameronMartin.unitCubeZeroExtend
      (AlignmentGaussianIntegratedSourceModel.integerIntegratedKernelFeature m (cubeCorner d))‖ at hn
  rw [norm_zero,CameronMartin.unitCubeZeroExtend_norm] at hn
  have hk:=norm_eq_zero.mp hn.symm
  exact tensorKernelFamily_corner_ne_zero
    (fun i=>(m i:ℝ)+1) (by intro i; nlinarith [show (0:ℝ)≤(m i:ℝ) from Nat.cast_nonneg (m i)]) hk

end BrownianSharp.AlignmentPaperIntegratedFeatureNonzero
