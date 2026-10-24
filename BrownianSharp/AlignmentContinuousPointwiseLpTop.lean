import BrownianSharp.AlignmentContinuousLInfinity

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentContinuousPointwiseLpTop

theorem continuous_enorm_le_eLpNorm_top
    {α E : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure α)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (f : C(α, E)) (x : α) :
    ‖f x‖ₑ ≤ eLpNorm (fun y => f y) ⊤ μ := by
  have hmeas : AEStronglyMeasurable (fun y => f y) μ :=
    f.continuous.aestronglyMeasurable
  have hae : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ eLpNorm (fun z => f z) ⊤ μ := by
    rw [eLpNorm_exponent_top hmeas]
    exact ae_le_eLpNormEssSup
  have hclosed : IsClosed {y : α | ‖f y‖ₑ ≤
      eLpNorm (fun z => f z) ⊤ μ} :=
    isClosed_le f.continuous.enorm continuous_const
  have hall : {y : α | ‖f y‖ₑ ≤ eLpNorm (fun z => f z) ⊤ μ} = Set.univ :=
    hclosed.ae_eq_univ_iff_eq.mp (ae_eq_univ.mpr hae)
  have hx : x ∈ {y : α | ‖f y‖ₑ ≤ eLpNorm (fun z => f z) ⊤ μ} := by
    rw [hall]
    trivial
  exact hx

theorem continuous_eLpNorm_top_eq_ofReal_norm
    {α E : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure α)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (f : C(α, E)) :
    eLpNorm (fun y => f y) ⊤ μ = ENNReal.ofReal ‖f‖ := by
  have hupper : eLpNorm (fun y => f y) ⊤ μ ≤ ENNReal.ofReal ‖f‖ := by
    rw [eLpNorm_exponent_top f.continuous.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
  have hne : eLpNorm (fun y => f y) ⊤ μ ≠ ⊤ :=
    ne_of_lt (hupper.trans_lt ENNReal.ofReal_lt_top)
  have hpoint (x : α) :
      ‖f x‖ ≤ (eLpNorm (fun y => f y) ⊤ μ).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hne).mp
    simpa only [ofReal_norm] using continuous_enorm_le_eLpNorm_top μ f x
  have hnorm : ‖f‖ ≤ (eLpNorm (fun y => f y) ⊤ μ).toReal :=
    (ContinuousMap.norm_le f ENNReal.toReal_nonneg).2 hpoint
  apply le_antisymm hupper
  simpa only [ENNReal.ofReal_toReal hne] using ENNReal.ofReal_le_ofReal hnorm

end BrownianSharp.AlignmentContinuousPointwiseLpTop
