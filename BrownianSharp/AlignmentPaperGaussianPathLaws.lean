import BrownianSharp.AlignmentPaperGaussianFeatureBridge

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BrownianSharp.AlignmentPaperGaussianPathLaws

def IsCenteredPathLaw {α : Type*} [TopologicalSpace α]
    (C : α → α → ℝ) (μ : Measure C(α,ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ IsGaussianProcess (fun (x:α) (f:C(α,ℝ))=>f x) μ ∧
    (∀ x, ∫ f:C(α,ℝ), f x ∂μ=0) ∧
    (∀ x y, cov[fun f:C(α,ℝ)=>f x,fun f:C(α,ℝ)=>f y;μ]=C x y)

/-- Passing to the actual continuous-path law preserves the finite Gaussian
laws, means and covariances. -/
theorem isCenteredPathLaw_map
    {α Ω : Type*} [TopologicalSpace α] [CompactSpace α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] {P:Measure Ω} [IsProbabilityMeasure P]
    (F:Ω→C(α,ℝ)) (hF:Measurable F)
    (hX:IsGaussianProcess (fun x ω=>F ω x) P)
    (hmean:∀x,∫ω,F ω x∂P=0) (C:α→α→ℝ)
    (hcov:∀x y,cov[fun ω=>F ω x,fun ω=>F ω y;P]=C x y) :
    IsCenteredPathLaw C (P.map F) := by
  refine ⟨inferInstance,?_,?_,?_⟩
  · refine ⟨fun I=>?_⟩
    let e:C(α,ℝ)→(I→ℝ) := fun f=>I.restrict (fun x=>f x)
    have he:Measurable e := by
      apply measurable_pi_iff.mpr
      intro i
      exact ContinuousMap.measurable_eval i.val
    refine ⟨he.aemeasurable,?_⟩
    rw [Measure.map_map he hF]
    exact (hX.hasGaussianLaw I).isGaussian_map
  · intro x
    rw [integral_map hF.aemeasurable (ContinuousMap.measurable_eval x).aestronglyMeasurable]
    exact hmean x
  · intro x y
    rw [covariance_map (ContinuousMap.measurable_eval x).aestronglyMeasurable
      (ContinuousMap.measurable_eval y).aestronglyMeasurable hF.aemeasurable]
    exact hcov x y

/-- The covariance determines the centered continuous Gaussian path law. -/
theorem centeredPathLaw_unique {α:Type*} [TopologicalSpace α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    {C:α→α→ℝ} {μ ν:Measure C(α,ℝ)}
    (hμ:IsCenteredPathLaw C μ) (hν:IsCenteredPathLaw C ν) : μ=ν := by
  letI:=hμ.1
  letI:=hν.1
  have h := AlignmentPaperGaussianFeatureBridge.continuous_path_law_eq_of_same_covariance
    (P:=μ) (Q:=ν) id id measurable_id measurable_id hμ.2.1 hν.2.1
      hμ.2.2.1 hν.2.2.1 (fun x y=>(hμ.2.2.2 x y).trans (hν.2.2.2 x y).symm)
  simpa using h

/-- Constants attached to the unique covariance law can be chosen before
all realizations of that law, including realizations on different spaces. -/
theorem exists_uniform_of_unique_law {A B:Type*} [Nonempty B] (S:Set A)
    (hunique:∀a∈S,∀b∈S,a=b) (P:A→B→Prop)
    (h:∀a∈S,∃b,P a b) : ∃b,∀a∈S,P a b := by
  classical
  by_cases hne:S.Nonempty
  · obtain ⟨a,ha⟩:=hne
    obtain ⟨b,hb⟩:=h a ha
    refine ⟨b,?_⟩
    intro a' ha'
    simpa [hunique a' ha' a ha] using hb
  · exact ⟨Classical.choice (inferInstance : Nonempty B), by simpa [Set.not_nonempty_iff_eq_empty.mp hne]⟩

end BrownianSharp.AlignmentPaperGaussianPathLaws
