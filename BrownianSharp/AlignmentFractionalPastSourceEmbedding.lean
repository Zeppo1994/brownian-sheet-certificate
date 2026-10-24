import BrownianSharp.AlignmentFractionalSheetMvNGram
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Actual zero-extension/reflection of the past source into the full MvN source. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalPastSourceEmbedding
open AlignmentFractionalSheetMvNGram

abbrev PastPositiveL2 := Lp ℝ 2 (volume.restrict (Set.Ioi (0:ℝ)))

def pastPositiveExtensionFunction (g : PastPositiveL2) : ℝ → ℝ :=
  (Set.Ioi (0:ℝ)).indicator (fun u => g u)

theorem pastPositiveExtension_memLp (g : PastPositiveL2) :
    MemLp (pastPositiveExtensionFunction g) 2 volume := by
  rw [pastPositiveExtensionFunction, memLp_indicator_iff_restrict measurableSet_Ioi]
  exact Lp.memLp g

/-- The canonical isometric zero-extension map from `[0,1]` into the full-line
source Hilbert space. -/
noncomputable def pastPositiveExtension : PastPositiveL2 →L[ℝ] FullLineL2 := by
  let L : PastPositiveL2 →ₗ[ℝ] FullLineL2 := {
    toFun := fun g => (pastPositiveExtension_memLp g).toLp
      (pastPositiveExtensionFunction g)
    map_add' := by
      intro f g
      change (pastPositiveExtension_memLp (f+g)).toLp
        (pastPositiveExtensionFunction (f+g)) =
        (pastPositiveExtension_memLp f).toLp (pastPositiveExtensionFunction f) +
        (pastPositiveExtension_memLp g).toLp (pastPositiveExtensionFunction g)
      rw [← MemLp.toLp_add (pastPositiveExtension_memLp f)
        (pastPositiveExtension_memLp g)]
      apply MemLp.toLp_congr
      have hfg : (⇑(f + g) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
          (⇑f : ℝ → ℝ) + ⇑g := Lp.coeFn_add f g
      have hfg' := (ae_restrict_iff' measurableSet_Ioi).1 hfg
      filter_upwards [hfg'] with u hu
      by_cases hs : u ∈ Set.Ioi (0:ℝ)
      · simpa [pastPositiveExtensionFunction, Set.indicator_of_mem hs] using hu hs
      · simp [pastPositiveExtensionFunction, Set.indicator, hs]
    map_smul' := by
      intro c f
      change (pastPositiveExtension_memLp (c • f)).toLp
        (pastPositiveExtensionFunction (c • f)) =
        c • (pastPositiveExtension_memLp f).toLp (pastPositiveExtensionFunction f)
      rw [← MemLp.toLp_const_smul c (pastPositiveExtension_memLp f)]
      apply MemLp.toLp_congr
      have hcf : (⇑(c • f) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
          c • (⇑f : ℝ → ℝ) := Lp.coeFn_smul c f
      have hcf' := (ae_restrict_iff' measurableSet_Ioi).1 hcf
      filter_upwards [hcf'] with u hu
      by_cases hs : u ∈ Set.Ioi (0:ℝ)
      · simpa [pastPositiveExtensionFunction, Set.indicator_of_mem hs] using hu hs
      · simp [pastPositiveExtensionFunction, Set.indicator, hs]
  }
  refine L.mkContinuous 1 ?_
  intro g
  change ‖(pastPositiveExtension_memLp g).toLp
      (pastPositiveExtensionFunction g)‖ ≤ 1 * ‖g‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp (pastPositiveExtension_memLp g))]
  rw [pastPositiveExtensionFunction]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi]
  simp

theorem pastPositiveExtension_norm (g : PastPositiveL2) :
    ‖pastPositiveExtension g‖ = ‖g‖ := by
  unfold pastPositiveExtension
  change ‖(pastPositiveExtension_memLp g).toLp
    (pastPositiveExtensionFunction g)‖ = ‖g‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp (pastPositiveExtension_memLp g))]
  rw [pastPositiveExtensionFunction]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi]


def fullLineReflection : FullLineL2 →ₗᵢ[ℝ] FullLineL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun u : ℝ => -u)
    (Measure.measurePreserving_neg (volume : Measure ℝ))

def negativeSourceEmbedding : PastPositiveL2 →L[ℝ] FullLineL2 :=
  fullLineReflection.toContinuousLinearMap.comp pastPositiveExtension

theorem negativeSourceEmbedding_norm (g : PastPositiveL2) :
    ‖negativeSourceEmbedding g‖ = ‖g‖ := by
  change ‖fullLineReflection (pastPositiveExtension g)‖ = _
  rw [fullLineReflection.norm_map, pastPositiveExtension_norm]

theorem pastPositiveExtension_ae (g : PastPositiveL2) :
    pastPositiveExtension g =ᵐ[volume] (Set.Ioi (0:ℝ)).indicator (fun u => g u) :=
  MemLp.coeFn_toLp (pastPositiveExtension_memLp g)

theorem negativeSourceEmbedding_ae (g : PastPositiveL2) :
    negativeSourceEmbedding g =ᵐ[volume]
      (fun u : ℝ => if u<0 then g (-u) else 0) := by
  have hr := Lp.coeFn_compMeasurePreserving (pastPositiveExtension g)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (pastPositiveExtension_ae g)
  filter_upwards [hr,hp] with u hu hv
  change (negativeSourceEmbedding g : ℝ → ℝ) u = _
  change (Lp.compMeasurePreserving (fun u : ℝ => -u) _ (pastPositiveExtension g) : ℝ → ℝ) u = _
  rw [hu,hv]
  simp [Function.comp_def, Set.indicator, Set.mem_Ioi]

end BrownianSharp.AlignmentFractionalPastSourceEmbedding
