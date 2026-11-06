import BrownianSharp.AlignmentPaperGaussianQuantileBounds

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperGaussianEnlargementTail

/-- Turn an actual enlargement mass estimate into the precise tail probability
used in the fourth-moment codebook estimate. -/
theorem complement_le_of_enlargement {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {G : Set X} (hG : MeasurableSet G)
    {p φ R s : ℝ} (hp : 0<p) (hp1 : p<1) (hφ : 0≤φ)
    (hlog : -Real.log p≤φ) (hs : 0≤s) (hR : Real.sqrt (2*φ)+s≤R)
    (hmass : Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile p+R)≤μ.real G) :
    μ Gᶜ≤ENNReal.ofReal (Real.exp (-s^2/2)) := by
  have ht := AlignmentPaperGaussianQuantileBounds.enlargement_tail_of_neg_log_le
    hp hp1 hφ hlog hs hR
  have hr : μ.real Gᶜ≤Real.exp (-s^2/2) := by
    rw [measureReal_compl hG,probReal_univ]
    linarith
  rw [←ENNReal.ofReal_toReal (measure_ne_top μ Gᶜ)]
  exact ENNReal.ofReal_le_ofReal hr

end BrownianSharp.AlignmentPaperGaussianEnlargementTail
