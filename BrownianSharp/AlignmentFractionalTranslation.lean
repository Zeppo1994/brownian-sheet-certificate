import BrownianSharp.AlignmentFractionalL2
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentFractionalTranslation

open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentFractionalL2

abbrev FullL2 := Lp ℝ 2 (volume : Measure ℝ)

/-- Restriction is realized by the canonical map between `Lp` spaces under
measure domination. -/
noncomputable def restrictUnitCLM : FullL2 →L[ℝ] UnitL2 :=
  Lp.LpToLpOfMeasureLeSMul (p := 2) (μ := volume.restrict (Set.Icc (0:ℝ) 1))
    (ν := volume) (c := 1) (by simp)
    (by simpa using (Measure.restrict_le_self : volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume))

theorem restrictUnitCLM_norm_le : ‖restrictUnitCLM‖ ≤ 1 := by
  exact le_trans (Lp.norm_LpToLpOfMeasureLeSMul_le (p := 2) (c := 1) (by simp)
    (by simpa using (Measure.restrict_le_self : volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume))) (by norm_num)

/-- The kernel truncated to its unit-scale support. -/
def kernelCut (α x : ℝ) : ℝ := (Set.Ioc (0:ℝ) 1).indicator (kernel α) x

theorem kernelCut_memLp {α : ℝ} (hα : 1/2 < α) :
    MemLp (kernelCut α) 2 (volume : Measure ℝ) := by
  change MemLp ((Set.Ioc (0:ℝ) 1).indicator (kernel α)) 2 volume
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  have h1 : IntervalIntegrable (kernel α) volume 0 1 := kernel_intervalIntegrable hα
  have h2 : IntervalIntegrable (fun x : ℝ => (kernel α x)^2) volume 0 1 :=
    kernel_sq_intervalIntegrable hα (by norm_num)
  have hi : Integrable (kernel α) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h1
  have hi2 : Integrable (fun x : ℝ => (kernel α x)^2)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h2
  exact (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).2 hi2

/-- Translation and reflection of the truncated kernel, as a global `L²`
vector. -/
noncomputable def fullKernelVector (α : ℝ) (hα : 1/2 < α) : FullL2 :=
  (kernelCut_memLp hα).toLp (kernelCut α)

def reflectionTranslation (t : ℝ) : C(ℝ, ℝ) :=
  ⟨fun u => t-u, continuous_const.sub continuous_id⟩

theorem reflectionTranslation_continuous : Continuous (fun t : ℝ => reflectionTranslation t) := by
  let J : C(ℝ × ℝ, ℝ) := ⟨fun p => p.1 - p.2, by fun_prop⟩
  change Continuous (fun t : ℝ => J.curry t)
  exact J.curry.continuous

theorem reflectionTranslation_measurePreserving (t : ℝ) :
    MeasurePreserving (reflectionTranslation t) (volume : Measure ℝ) volume := by
  exact volume.measurePreserving_sub_left t

/-- The translated truncated kernel varies continuously in global `L²` as its
parameter varies. -/
noncomputable def translatedFullKernelFamily (α : ℝ) (hα : 1/2 < α) :
    C(UnitInterval, FullL2) := by
  let f : UnitInterval → FullL2 := fun _ => fullKernelVector α hα
  have hf : Continuous f := continuous_const
  have hg : Continuous (fun t : UnitInterval => reflectionTranslation t.1) := by
    exact reflectionTranslation_continuous.comp continuous_subtype_val
  have hfamily : Continuous (fun t : UnitInterval =>
      Lp.compMeasurePreserving (reflectionTranslation t.1)
        (reflectionTranslation_measurePreserving t.1) (fullKernelVector α hα)) :=
    hf.compMeasurePreservingLp hg (fun z => reflectionTranslation_measurePreserving z.1) (by norm_num)
  exact ⟨fun t => Lp.compMeasurePreserving (reflectionTranslation t.1)
      (reflectionTranslation_measurePreserving t.1) (fullKernelVector α hα), hfamily⟩

/-- Restricting the translated global kernel gives a continuous family of
causal RL kernels in the fixed source `L²` space. -/
noncomputable def translatedUnitKernelFamily (α : ℝ) (hα : 1/2 < α) :
    C(UnitInterval, UnitL2) := by
  let F := translatedFullKernelFamily α hα
  exact ⟨fun t => restrictUnitCLM (F t), restrictUnitCLM.continuous.comp F.continuous⟩

/-- On the unit square the translated, truncated kernel is exactly the causal
kernel, including the chosen zero value at the diagonal. -/
theorem kernelCut_translate_eq_causal {α t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    kernelCut α (t-u) = causalKernel α t u := by
  by_cases h : u < t
  · have hpos : 0 < t-u := sub_pos.mpr h
    have hle : t-u ≤ 1 := by linarith
    simp [kernelCut, causalKernel, h, Set.mem_Ioc, hpos, hle]
  · have hle : t-u ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
    simp [kernelCut, causalKernel, h, Set.mem_Ioc, hle]

/-- The continuous family above is represented by the literal causal kernel
used in the RL integral. -/
theorem translatedUnitKernelFamily_eq_kernelVector (α t : ℝ) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    translatedUnitKernelFamily α hα ⟨t, ⟨ht0, ht1⟩⟩ =
      kernelVector α t hα ht0 ht1 := by
  change restrictUnitCLM (translatedFullKernelFamily α hα ⟨t, ⟨ht0, ht1⟩⟩) =
      kernelVector α t hα ht0 ht1
  apply Lp.ext
  have hrestrict : restrictUnitCLM (translatedFullKernelFamily α hα ⟨t, ⟨ht0, ht1⟩⟩) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)]
      translatedFullKernelFamily α hα ⟨t, ⟨ht0, ht1⟩⟩ :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := 1) (by simp)
      (by simpa using (Measure.restrict_le_self : volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume)) _
  have htrans : translatedFullKernelFamily α hα ⟨t, ⟨ht0, ht1⟩⟩ =ᵐ[volume]
      (fun u => kernelCut α (t-u)) := by
    change Lp.compMeasurePreserving (reflectionTranslation t)
      (reflectionTranslation_measurePreserving t) (fullKernelVector α hα) =ᵐ[volume] _
    have hcomp := Lp.coeFn_compMeasurePreserving (fullKernelVector α hα)
      (reflectionTranslation_measurePreserving t)
    have h0 : fullKernelVector α hα =ᵐ[volume] kernelCut α :=
      MemLp.coeFn_toLp (kernelCut_memLp hα)
    have h0' := (reflectionTranslation_measurePreserving t).quasiMeasurePreserving.ae_eq_comp h0
    exact hcomp.trans h0'
  have hle : volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume := Measure.restrict_le_self
  have htrans' := ae_mono hle htrans
  have hv := MemLp.coeFn_toLp (causalKernel_memLp_unit hα ht0 ht1)
  have huIcc : ∀ᵐ u ∂(volume.restrict (Set.Icc (0:ℝ) 1)), u ∈ Set.Icc 0 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hrestrict, htrans', hv, huIcc] with u hu hr hvu hmem
  rcases hmem with ⟨hu0, hu1⟩
  calc
    restrictUnitCLM (translatedFullKernelFamily α hα ⟨t, ⟨ht0, ht1⟩⟩) u =
        translatedFullKernelFamily α hα ⟨t, ⟨ht0, ht1⟩⟩ u := hu
    _ = kernelCut α (t-u) := hr
    _ = causalKernel α t u := kernelCut_translate_eq_causal ht0 ht1 hu0 hu1
    _ = kernelVector α t hα ht0 ht1 u := hvu.symm


/-- The restricted evaluation kernels have a uniform bound inherited from the
global translation orbit. -/
theorem translatedUnitKernelFamily_norm_le (α : ℝ) (hα : 1/2 < α)
    (t : UnitInterval) :
    ‖translatedUnitKernelFamily α hα t‖ ≤ ‖fullKernelVector α hα‖ := by
  change ‖restrictUnitCLM (translatedFullKernelFamily α hα t)‖ ≤ _
  calc
    ‖restrictUnitCLM (translatedFullKernelFamily α hα t)‖ ≤
        ‖restrictUnitCLM‖ * ‖translatedFullKernelFamily α hα t‖ :=
      restrictUnitCLM.le_opNorm _
    _ ≤ 1 * ‖translatedFullKernelFamily α hα t‖ :=
      mul_le_mul_of_nonneg_right restrictUnitCLM_norm_le (norm_nonneg _)
    _ = ‖fullKernelVector α hα‖ := by
      simp [translatedFullKernelFamily, Lp.norm_compMeasurePreserving]

/-- The RL evaluation at a fixed `t`, now using a genuinely varying kernel
vector in the compact parameter interval. -/
noncomputable def fractionalEvaluation (α t : ℝ) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : UnitL2 →L[ℝ] ℝ :=
  evaluationFunctional α t hα ht0 ht1

/-- The Riemann--Liouville operator as a bounded map from source `L²` to
continuous functions on `[0,1]`. -/
noncomputable def fractionalRL (α : ℝ) (hα : 1/2 < α) :
    UnitL2 →L[ℝ] C(UnitInterval, ℝ) := by
  let L : UnitL2 →ₗ[ℝ] C(UnitInterval, ℝ) := {
    toFun := fun g => ⟨fun t => fractionalEvaluation α t.1 hα t.2.1 t.2.2 g, by
      let K := translatedUnitKernelFamily α hα
      have hc : Continuous (fun t : UnitInterval =>
          (innerSL ℝ g) (K t)) := (innerSL ℝ g).continuous.comp K.continuous
      have heq : (fun t : UnitInterval => fractionalEvaluation α t.1 hα
          t.2.1 t.2.2 g) = fun t => (innerSL ℝ g) (K t) := by
        funext t
        rw [fractionalEvaluation, evaluationFunctional, innerSL_apply_apply]
        rw [translatedUnitKernelFamily_eq_kernelVector α t.1 hα t.2.1 t.2.2]
        rw [innerSL_apply_apply]
        exact real_inner_comm _ _
      exact hc.congr (fun t => (congrFun heq t).symm)⟩
    map_add' := by
      intro f g
      ext t
      exact (fractionalEvaluation α t.1 hα t.2.1 t.2.2).map_add f g
    map_smul' := by
      intro c f
      ext t
      exact (fractionalEvaluation α t.1 hα t.2.1 t.2.2).map_smul c f
  }
  refine LinearMap.mkContinuous L ‖fullKernelVector α hα‖ ?_
  intro g
  apply (ContinuousMap.norm_le (f := L g)
    (C := ‖fullKernelVector α hα‖ * ‖g‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro t
  calc
    ‖L g t‖ = ‖fractionalEvaluation α t.1 hα t.2.1 t.2.2 g‖ := rfl
    _ ≤ ‖fractionalEvaluation α t.1 hα t.2.1 t.2.2‖ * ‖g‖ :=
      (fractionalEvaluation α t.1 hα t.2.1 t.2.2).le_opNorm g
    _ = ‖kernelVector α t.1 hα t.2.1 t.2.2‖ * ‖g‖ := by
      rw [fractionalEvaluation, evaluationFunctional_norm]
    _ ≤ ‖fullKernelVector α hα‖ * ‖g‖ := by
      have hkernel : ‖kernelVector α t.1 hα t.2.1 t.2.2‖ ≤
          ‖fullKernelVector α hα‖ := by
        rw [← translatedUnitKernelFamily_eq_kernelVector α t.1 hα t.2.1 t.2.2]
        exact translatedUnitKernelFamily_norm_le α hα t
      exact mul_le_mul_of_nonneg_right hkernel (norm_nonneg _)

/-- Pointwise integral formula for the continuous RL operator. -/
theorem fractionalRL_apply (α : ℝ) (hα : 1/2 < α) (g : UnitL2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    fractionalRL α hα g ⟨t, ⟨ht0, ht1⟩⟩ =
      ∫ u, causalKernel α t u * g u ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  change fractionalEvaluation α t hα ht0 ht1 g = _
  exact evaluationFunctional_apply α t hα ht0 ht1 g

end BrownianSharp.AlignmentFractionalTranslation
