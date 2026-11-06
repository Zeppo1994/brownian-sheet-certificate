import BrownianSharp.AlignmentPaperQuantizationAtomicBridge
import BrownianSharp.AlignmentPaperEmpiricalWasserstein

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperQuantizationEmpiricalComparison
open AlignmentPaperEmpiricalWasserstein

/-- Optimal finite quantization is bounded by the actual expected empirical
transport error. No measurability premise for the nearest representatives is
left to the caller. The outer expectation here is the nonnegative integral. -/
theorem quantization_le_expectedEmpiricalWassersteinTwo
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ:Measure X) [IsProbabilityMeasure μ] (m:ℕ) (hm:0<m) :
    quantizationQ1 μ m hm≤quantizationQ2 μ m hm ∧
      quantizationQ2 μ m hm≤expectedEmpiricalWassersteinTwo μ m hm := by
  have hmeas : ∀c:Fin m→X,Measurable (fun y=>finiteCodebookDistortion hm c y) :=
    fun c=>AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable hm c
  refine ⟨quantizationQ1_le_Q2 μ m hm hmeas,?_⟩
  letI:IsProbabilityMeasure (iidSampleLaw μ m):=iidSampleLaw_isProbability μ m
  calc
    quantizationQ2 μ m hm=(∫⁻ _:Fin m→X,quantizationQ2 μ m hm∂iidSampleLaw μ m) := by simp
    _ ≤ expectedEmpiricalWassersteinTwo μ m hm := by
      apply lintegral_mono
      intro x
      exact (quantizationQ1_le_Q2_le_empiricalWassersteinTwo μ m hm x hmeas).2

end BrownianSharp.AlignmentPaperQuantizationEmpiricalComparison
