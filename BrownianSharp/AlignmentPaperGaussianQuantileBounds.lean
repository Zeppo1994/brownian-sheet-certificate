import BrownianSharp.Concentration

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BrownianSharp.AlignmentPaperGaussianQuantileBounds
open Concentration

/-- Symmetry of Mathlib's real standard Gaussian, with the strict CDF
convention used in the certificate. -/
theorem standardGaussianCDF_neg (t : ℝ) :
    standardGaussianCDF (-t)=1-standardGaussianCDF t := by
  let μ := gaussianReal 0 1
  have hm : μ.map (fun x : ℝ => -x)=μ := by
    simpa [μ] using (gaussianReal_map_neg (μ := (0:ℝ)) (v := (1:ℝ≥0)))
  have hs : μ (Set.Iic (-t))=μ (Set.Ici t) := by
    have h := congrArg (fun ν : Measure ℝ => ν (Set.Iic (-t))) hm
    rw [Measure.map_apply measurable_neg measurableSet_Iic] at h
    have heq : (fun x : ℝ => -x) ⁻¹' Set.Iic (-t)=Set.Ici t := by
      ext x
      simp
    simpa [heq] using h.symm
  calc
    standardGaussianCDF (-t)=μ.real (Set.Iic (-t)) := by
      rw [standardGaussianCDF_eq_cdf, cdf_eq_real]
    _ = μ.real (Set.Ici t) := congrArg ENNReal.toReal hs
    _ = 1-standardGaussianCDF t := by
      change μ.real (Set.Ici t)=1-μ.real (Set.Iio t)
      simpa using (measureReal_compl (μ := μ) (s := Set.Iio t) measurableSet_Iio)

theorem standardGaussianCDF_upper_tail {t : ℝ} (ht : 0 ≤ t) :
    1-standardGaussianCDF t ≤ Real.exp (-t^2/2) := by
  rw [← standardGaussianCDF_neg]
  exact gaussianReal_lower_tail_exp ht

/-- A bound on the actual small-ball logarithm controls its standard-Gaussian
quantile, without assuming an unproved inverse-CDF estimate. -/
theorem quantile_lower_of_neg_log_le {p φ : ℝ}
    (hp : 0<p) (hp1 : p<1) (hφ : 0≤φ) (hlog : -Real.log p≤φ) :
    -Real.sqrt (2*φ) ≤ standardGaussianQuantile p := by
  have hs : (Real.sqrt (2*φ))^2=2*φ := Real.sq_sqrt (by positivity)
  have htail : standardGaussianCDF (-Real.sqrt (2*φ)) ≤ Real.exp (-φ) := by
    have h := gaussianReal_lower_tail_exp (Real.sqrt_nonneg (2*φ))
    change standardGaussianCDF (-Real.sqrt (2*φ)) ≤ Real.exp (-(Real.sqrt (2*φ))^2/2) at h
    have he : -(Real.sqrt (2*φ))^2/2 = -φ := by rw [hs]; ring
    rw [he] at h
    exact h
  have hexp : Real.exp (-φ)≤p := by
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by linarith)
  apply standardGaussianCDF_strictMono.le_iff_le.mp
  rw [standardGaussianCDF_standardGaussianQuantile hp hp1]
  exact htail.trans hexp

/-- The enlargement CDF consequently has a quantitative polynomial tail once
the dilation exceeds the small-ball quantile scale. -/
theorem enlargement_tail_of_neg_log_le {p φ R s : ℝ}
    (hp : 0<p) (hp1 : p<1) (hφ : 0≤φ) (hlog : -Real.log p≤φ)
    (hs : 0≤s) (hR : Real.sqrt (2*φ)+s≤R) :
    1-standardGaussianCDF (standardGaussianQuantile p+R) ≤ Real.exp (-s^2/2) := by
  have hq := quantile_lower_of_neg_log_le hp hp1 hφ hlog
  have hsq : s≤standardGaussianQuantile p+R := by linarith
  exact (sub_le_sub_left (standardGaussianCDF_strictMono.monotone hsq) 1).trans
    (standardGaussianCDF_upper_tail hs)

end BrownianSharp.AlignmentPaperGaussianQuantileBounds
