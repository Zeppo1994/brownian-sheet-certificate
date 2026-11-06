import BrownianSharp.AlignmentPaperGenericContinuumVariance
import BrownianSharp.AlignmentPaperContinuumConfinementRates

/-! Arbitrary admissible unit rows: the actual spatial covariance geometry
implies confinement outside exponentially small Gaussian coefficient measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace BrownianSharp.AlignmentPaperGenericContinuumConfinement
open AlignmentPaperGenericContinuumVariance AlignmentPaperSupportedRows
open AlignmentPaperContinuumConfinementRates
open AlignmentPaperContinuumShellBudgetScale

/-- Uniform unit-row confinement from the genuine continuum hull geometry.
All variance and normalized-region integral estimates are internally proved. -/
theorem eventually_regionRows_confinement {d:ℕ} (hd:2≤d) {q L:ℝ}
    (hq:0<q) (hL:0<L) (s:∀n:ℕ,RegionRows d n (LayerIndex d n) q L) :
    ∃ c b:ℝ,0<c ∧ 0<b ∧ ∃N:ℕ,∀n:ℕ,N≤n →
      (productStandardGaussian (LayerIndex d n)).real
        {z | ∀x∈(s n).region,|∑i,(s n).rows x i*z i|≤c*Real.sqrt (n:ℝ)} ≤
        Real.exp (-b*nativeDimension d n) := by
  let C:ℝ:=q⁻¹^2*continuumShellConstant d L
  let slope:ℝ:=Real.log 2/(4*L*(Nat.factorial (d-1):ℝ))
  let η:ℝ:=min 1 (slope/2)
  have hCs:0<continuumShellConstant d L:=continuumShellConstant_pos d hL
  have hC:0<C:=by dsimp [C]; positivity
  have hslope:0<slope:=by dsimp [slope]; exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hη:0<η:=lt_min (by norm_num) (half_pos hslope)
  have hη1:η≤1:=min_le_left _ _
  have hηs:2*η≤slope:=by
    have h:=min_le_right (1:ℝ) (slope/2)
    dsimp [η]
    linarith
  obtain ⟨Np,hp⟩:=eventually_gradeEvenPower_bounds hη
  obtain ⟨Ns,hs⟩:=eventually_evenPower_variance_small (d:=d) (by omega) hη hη1
    (show 0<4*C by positivity)
  let b:ℝ:=Concentration.standardGaussianQuantile (3/4)^2/(1152*C)
  have hb:0<b:=by dsimp [b]; exact div_pos (sq_pos_of_pos gaussian_threeQuarter_quantile_pos) (by positivity)
  let N:ℕ:=max (max Np Ns) (max (Nat.ceil (8/η)) 1)
  refine ⟨Real.sqrt η/8,b,div_pos (Real.sqrt_pos.mpr hη) (by norm_num),hb,N,?_⟩
  intro n hn
  have hnP:Np≤n:=by dsimp [N] at hn; omega
  have hnS:Ns≤n:=by dsimp [N] at hn; omega
  have hceil:Nat.ceil (8/η)≤n:=by dsimp [N] at hn; omega
  let p:=gradeEvenPower η n
  obtain ⟨hpu,hpl,_⟩:=hp n hnP
  have hnη:8/η≤(n:ℝ):=(Nat.le_ceil (8/η)).trans (by exact_mod_cast hceil)
  have hpn:η*(n:ℝ)≤2*(p:ℝ):=by dsimp [p]; nlinarith
  have hp8:8≤2*(p:ℝ):=by have h:=(div_le_iff₀ hη).mp hnη; linarith
  have hτbound:2*(p:ℝ)≤slope*((n:ℝ)+1):=by
    have h:=mul_le_mul_of_nonneg_right hηs (by positivity : 0≤(n:ℝ)+1)
    nlinarith
  have hvar:=regionRows_variance_le_uniform hd hq hL
    (show 0≤2*(p:ℝ) by positivity) hτbound (s n)
  have hD:0<nativeDimension d n:=(pow_pos (by norm_num : (0:ℝ)<2) n).trans_le
    (nativeDimension_ge_dyadic d n (by omega))
  have hsmall:C*(2*(p:ℝ))^2/nativeDimension d n≤1/16:=by
    convert hs n hnS using 1 <;> dsimp [p] <;> ring
  have hm:0<AlignmentPaperContinuumGoodRegion.cubeLebesgue d (s n).region:=
    (ENNReal.ofReal_pos.mpr hq).trans_le (s n).mass_lower
  let μ:=normalizedRegionProbability (s n).region
  letI:IsProbabilityMeasure μ:=normalizedRegion_isProbability (s n).region hm
  have hsupp:∀ᵐx∂μ,x∈(s n).region:=normalizedRegion_ae_mem _ (s n).region_measurable
  obtain ⟨x₀,hx₀⟩:=hsupp.exists
  have hcore:=supported_row_confinement_of_variance μ (s n).region (s n).region_measurable
    hsupp x₀ hx₀ (2*(p:ℝ)) hp8 (s n).rows (s n).unit (s n).rows_measurable
    hC hD hsmall hvar
  have hr:Real.sqrt η/8*Real.sqrt (n:ℝ)≤Real.sqrt (2*(p:ℝ))/4:=by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,div_pow,Real.sq_sqrt hη.le,Real.sq_sqrt (by positivity : 0≤(n:ℝ)),
      div_pow,Real.sq_sqrt (by positivity : 0≤2*(p:ℝ))]
    nlinarith
  apply (measureReal_mono ?_).trans hcore
  intro z hz x hx
  exact (hz x hx).trans hr

end BrownianSharp.AlignmentPaperGenericContinuumConfinement
