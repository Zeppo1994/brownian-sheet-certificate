import BrownianSharp.AlignmentPaperSpatialConfinement

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BrownianSharp.AlignmentPaperSupportedRows
open AlignmentPaperSpatialExponential AlignmentPaperSpatialConfinement

variable {α κ:Type*} [MeasurableSpace α] [Fintype κ]

/-- Outside the spatial support, reuse one actual supported row. This creates
globally unit rows without adding any new constraint to the small-field event. -/
def supportedRows (A:Set α) (a:α→κ→ℝ) (x₀:α):α→κ→ℝ := by
  classical
  exact fun x i=>if x∈A then a x i else a x₀ i

theorem supportedRows_unit (A:Set α) (a:α→κ→ℝ) (x₀:α) (hx₀:x₀∈A)
    (ha:∀x∈A,∑i,a x i^2=1) : ∀x,∑i,supportedRows A a x₀ x i^2=1 := by
  classical
  intro x
  by_cases hx:x∈A
  · simpa [supportedRows,hx] using ha x hx
  · simpa [supportedRows,hx] using ha x₀ hx₀

theorem supportedRows_measurable (A:Set α) (hA:MeasurableSet A)
    (a:α→κ→ℝ) (ha:∀i,Measurable (fun x=>a x i)) (x₀:α) :
    ∀i,Measurable (fun x=>supportedRows A a x₀ x i) := by
  classical
  intro i
  exact (ha i).piecewise hA measurable_const

theorem supportedRows_ae_eq (μ:Measure α) (A:Set α) (a:α→κ→ℝ) (x₀:α)
    (hA:∀ᵐx∂μ,x∈A) : supportedRows A a x₀=ᵐ[μ]a := by
  classical
  filter_upwards [hA] with x hx
  funext i
  simp [supportedRows,hx]

theorem spatialCoshAverage_supportedRows_eq (μ:Measure α) (A:Set α)
    (a:α→κ→ℝ) (x₀:α) (hA:∀ᵐx∂μ,x∈A) (τ:ℝ) :
    spatialCoshAverage μ τ (supportedRows A a x₀)=spatialCoshAverage μ τ a := by
  funext z
  unfold spatialCoshAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [supportedRows_ae_eq μ A a x₀ hA] with x hx
  rw [hx]

theorem supportedRows_bound (A:Set α) (a:α→κ→ℝ) (x₀:α) (hx₀:x₀∈A)
    (z:κ→ℝ) (r:ℝ) (h:∀x∈A,|∑i,a x i*z i|≤r) :
    ∀x,|∑i,supportedRows A a x₀ x i*z i|≤r := by
  classical
  intro x
  by_cases hx:x∈A
  · simpa [supportedRows,hx] using h x hx
  · simpa [supportedRows,hx] using h x₀ hx₀

/-- The exact spatial overlap variance bound also works for literal rows
unit only on their full-measure spatial region. -/
theorem supported_variance_le_spatial_overlap_remainder
    (μ:Measure α) [IsProbabilityMeasure μ] (A:Set α) (hA:MeasurableSet A)
    (hsupport:∀ᵐx∂μ,x∈A) (x₀:α) (hx₀:x₀∈A)
    (a:α→κ→ℝ) (τ:ℝ) (hτ:0≤τ)
    (ha:∀x∈A,∑i,a x i^2=1) (haMeas:∀i,Measurable (fun x=>a x i)) :
    variance (spatialCoshAverage μ τ a) (productStandardGaussian κ)≤
      ∫p:α×α,(τ^2*(∑i,a p.1 i*a p.2 i)^2/2*
        Real.exp (τ*|∑i,a p.1 i*a p.2 i|))∂μ.prod μ := by
  have hpair:∀ᵐp:α×α∂μ.prod μ,p.1∈A ∧ p.2∈A := by
    apply (Measure.ae_prod_iff_ae_ae (hA.prod hA)).2
    filter_upwards [hsupport] with x hx
    filter_upwards [hsupport] with y hy
    exact ⟨hx,hy⟩
  calc
    _ = variance (spatialCoshAverage μ τ (supportedRows A a x₀))
        (productStandardGaussian κ) := by
      rw [spatialCoshAverage_supportedRows_eq μ A a x₀ hsupport τ]
    _ ≤ ∫p:α×α,(τ^2*(∑i,supportedRows A a x₀ p.1 i*
        supportedRows A a x₀ p.2 i)^2/2*
        Real.exp (τ*|∑i,supportedRows A a x₀ p.1 i*
          supportedRows A a x₀ p.2 i|))∂μ.prod μ :=
      AlignmentPaperSpatialVariance.variance_le_spatial_overlap_remainder
        μ (supportedRows A a x₀) τ hτ (supportedRows_unit A a x₀ hx₀ ha)
        (supportedRows_measurable A hA a haMeas x₀)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hpair] with p hp
      simp [supportedRows,hp.1,hp.2]

/-- The final confinement estimate applies to rows unit on a full-measure
spatial set. The variance premise concerns the literal original spatial
average, and the event only constrains rows on that set. -/
theorem supported_row_confinement_of_variance
    (μ:Measure α) [IsProbabilityMeasure μ] (A:Set α) (hA:MeasurableSet A)
    (hsupport:∀ᵐx∂μ,x∈A) (x₀:α) (hx₀:x₀∈A)
    (τ:ℝ) (hτ:8≤τ) (a:α→κ→ℝ)
    (ha:∀x∈A,∑i,a x i^2=1) (haMeas:∀i,Measurable (fun x=>a x i))
    {C D:ℝ} (hC:0<C) (hD:0<D) (hsmall:C*τ^2/D≤1/16)
    (hvar:variance (spatialCoshAverage μ τ a) (productStandardGaussian κ)≤C*τ^2/D) :
    (productStandardGaussian κ).real {z|∀x∈A,|∑i,a x i*z i|≤Real.sqrt τ/4}≤
      Real.exp (-(Concentration.standardGaussianQuantile (3/4)^2/(1152*C))*D) := by
  have hvar':variance (spatialCoshAverage μ τ (supportedRows A a x₀))
      (productStandardGaussian κ)≤C*τ^2/D := by
    rw [spatialCoshAverage_supportedRows_eq μ A a x₀ hsupport τ]
    exact hvar
  have hbound:=spatial_row_confinement_of_variance μ τ hτ
    (supportedRows A a x₀) (supportedRows_unit A a x₀ hx₀ ha)
    (supportedRows_measurable A hA a haMeas x₀) hC hD hsmall hvar'
  apply (measureReal_mono (fun z hz=>supportedRows_bound A a x₀ hx₀ z _ hz)).trans hbound

end BrownianSharp.AlignmentPaperSupportedRows
