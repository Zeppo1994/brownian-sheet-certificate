import BrownianSharp.AlignmentPaperContinuumProfileSum
import BrownianSharp.AlignmentPaperSupportedRows

/-! The continuum hull-shell variance argument for arbitrary supported unit
rows. Its hypotheses are the actual two-point geometric bounds; no variance
or confinement estimate is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace BrownianSharp.AlignmentPaperGenericContinuumVariance
open AlignmentPaperContinuumGoodRegion AlignmentPaperContinuumHulls
open AlignmentPaperContinuumVariance AlignmentPaperContinuumProfileSum
open AlignmentPaperSpatialExponential AlignmentPaperSupportedRows

variable {κ:Type*} [Fintype κ]

def rowCorrelation {d:ℕ} (a:(Fin d→ℝ)→κ→ℝ) (x y:Fin d→ℝ) : ℝ :=
  ∑i,a x i*a y i

def pairRemainder {d:ℕ} (τ:ℝ) (a:(Fin d→ℝ)→κ→ℝ)
    (p:(Fin d→ℝ)×(Fin d→ℝ)) : ℝ :=
  τ^2/2 * rowCorrelation a p.1 p.2 ^2 *
    Real.exp (τ*|rowCorrelation a p.1 p.2|)

def normalizedRegionProbability {d:ℕ} (A:Set (Fin d→ℝ)) : Measure (Fin d→ℝ) :=
  (cubeLebesgue d A)⁻¹ • (cubeLebesgue d).restrict A

theorem normalizedRegion_isProbability {d:ℕ} (A:Set (Fin d→ℝ))
    (hm:0<cubeLebesgue d A) : IsProbabilityMeasure (normalizedRegionProbability A) := by
  refine ⟨?_⟩
  have htop:cubeLebesgue d A≠⊤ := measure_ne_top _ _
  simp only [normalizedRegionProbability,Measure.smul_apply,Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt hm) htop

theorem normalizedRegion_ae_mem {d:ℕ} (A:Set (Fin d→ℝ)) (hA:MeasurableSet A) :
    ∀ᵐx∂normalizedRegionProbability A,x∈A := by
  unfold normalizedRegionProbability
  exact Measure.ae_smul_measure (ae_restrict_mem hA) _

theorem normalizedRegion_prod_eq {d:ℕ} (A:Set (Fin d→ℝ)) :
    (normalizedRegionProbability A).prod (normalizedRegionProbability A)=
      ((cubeLebesgue d A)⁻¹)^2 •
        ((cubeLebesgue d).prod (cubeLebesgue d)).restrict (A×ˢA) := by
  unfold normalizedRegionProbability
  rw [Measure.prod_smul_left,Measure.prod_smul_right,Measure.prod_restrict]
  simp [smul_smul,pow_two]

private theorem remainder_le_of_abs_le {τ ρ c:ℝ} (hτ:0≤τ) (hc:0≤c)
    (hρ:|ρ|≤c) :
    τ^2/2*ρ^2*Real.exp (τ*|ρ|)≤τ^2/2*c^2*Real.exp (τ*c) := by
  have hs:ρ^2≤c^2 := by
    have hm:=mul_self_le_mul_self (abs_nonneg ρ) hρ
    nlinarith [sq_abs ρ]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hs (by positivity))
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hρ hτ))
    (Real.exp_nonneg _) (by positivity)

private theorem shellBound_nonneg {d n:ℕ} (τ L:ℝ) (u:Fin d→ℕ) :
    0≤continuumShellRemainderBound (d:=d) (n:=n) τ L u := by
  unfold continuumShellRemainderBound
  split_ifs <;> positivity

private theorem majorant_ge_shell {d n N:ℕ} (τ L:ℝ)
    (p:(Fin d→ℝ)×(Fin d→ℝ)) (u:BoundedHullProfile d N)
    (hu:p∈spatialPairHullShell u.1) :
    continuumShellRemainderBound (d:=d) (n:=n) τ L u.1≤
      continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p := by
  classical
  have hsum : continuumShellRemainderBound (d:=d) (n:=n) τ L u.1≤
      ∑v:BoundedHullProfile d N,continuumShellRemainderBound (d:=d) (n:=n) τ L v.1*
        (if p∈spatialPairHullShell v.1 then 1 else 0) := by
    calc
      _ = continuumShellRemainderBound (d:=d) (n:=n) τ L u.1*
          (if p∈spatialPairHullShell u.1 then 1 else 0) := by simp [hu]
      _ ≤ _ := Finset.single_le_sum
        (f:=fun v:BoundedHullProfile d N=>continuumShellRemainderBound (d:=d) (n:=n) τ L v.1*
          (if p∈spatialPairHullShell v.1 then 1 else 0))
        (fun v hv=>mul_nonneg (shellBound_nonneg τ L v.1)
          (by split_ifs <;> positivity)) (Finset.mem_univ u)
  unfold continuumFiniteShellMajorant
  exact hsum.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))

/-- The finite hull cover dominates the true row-correlation remainder for
any supported unit-row family satisfying the dyadic overlap bounds. -/
theorem pairRemainder_le_majorant {d n N:ℕ} (hd:2≤d) {τ L:ℝ}
    (hτ:0≤τ) (hL:0≤L) (A:Set (Fin d→ℝ))
    (hcoords:∀x∈A,∀i,x i∈Set.Ico (0:ℝ) 1)
    (a:(Fin d→ℝ)→κ→ℝ) (hunit:∀x∈A,∑i,a x i^2=1)
    (hzero:∀x∈A,∀y∈A,∀u:Fin d→ℕ,
      (fun i=>(x i,y i))∈tensorOppositeHullShell u → (∑i,u i)<n → rowCorrelation a x y=0)
    (hcap:∀x∈A,∀y∈A,∀u:Fin d→ℕ,
      (fun i=>(x i,y i))∈tensorOppositeHullShell u → n≤(∑i,u i) →
      |rowCorrelation a x y|≤shapeOverlapCap d n ((∑i,u i)-n) L)
    (p:(Fin d→ℝ)×(Fin d→ℝ)) (hx:p.1∈A) (hy:p.2∈A) :
    pairRemainder τ a p≤continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p := by
  classical
  rcases spatialPair_firstSeparation_or_residual (N:=N) p (hcoords _ hx) (hcoords _ hy) with hs|hr
  · obtain ⟨u,hu⟩:=hs
    apply le_trans ?_ (majorant_ge_shell τ L p u (by simpa [spatialPairHullShell] using hu))
    by_cases hle:n≤∑i,u.1 i
    · have hb := remainder_le_of_abs_le hτ
        (shapeOverlapCap_nonneg (by omega : 1≤d) n ((∑i,u.1 i)-n) hL)
        (hcap p.1 hx p.2 hy u.1 hu hle)
      simpa [pairRemainder,continuumShellRemainderBound,hle] using hb
    · simp [pairRemainder,continuumShellRemainderBound,hle,hzero p.1 hx p.2 hy u.1 hu (by omega)]
  · have hρ:|rowCorrelation a p.1 p.2|≤1 :=
      AlignmentPaperSpatialVariance.row_overlap_abs_le_one (a p.1) (a p.2)
        (hunit p.1 hx) (hunit p.2 hy)
    have hR:pairRemainder τ a p≤τ^2/2*Real.exp τ := by
      simpa [pairRemainder] using remainder_le_of_abs_le hτ (by norm_num : (0:ℝ)≤1) hρ
    have hsum:0≤∑v:BoundedHullProfile d N,
        continuumShellRemainderBound (d:=d) (n:=n) τ L v.1*
          (if p∈spatialPairHullShell v.1 then 1 else 0) :=
      Finset.sum_nonneg (fun v hv=>mul_nonneg (shellBound_nonneg τ L v.1)
        (by split_ifs <;> positivity))
    have hr' : (fun i=>(p.1 i,p.2 i))∈tensorCoordinateResidual N := hr
    unfold continuumFiniteShellMajorant
    simpa [hr'] using hR.trans (le_add_of_nonneg_left hsum)

theorem majorant_integrable_normalized {d n N:ℕ} (τ L:ℝ)
    (A:Set (Fin d→ℝ)) (hm:0<cubeLebesgue d A) :
    Integrable (continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L)
      ((normalizedRegionProbability A).prod (normalizedRegionProbability A)) := by
  rw [normalizedRegion_prod_eq]
  exact (continuumFiniteShellMajorant_integrable (d:=d) (n:=n) (N:=N)
    (τ:=τ) (L:=L)).restrict.smul_measure
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt hm)))

theorem normalizedRegion_majorant_integral_le {d n N:ℕ} (hd:1≤d) (τ L:ℝ)
    (A:Set (Fin d→ℝ)) (hτ:0≤τ) (hL:0≤L) :
    (∫p,continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p
      ∂(normalizedRegionProbability A).prod (normalizedRegionProbability A)) ≤
      (((cubeLebesgue d A)⁻¹)^2).toReal *
        (∫p,continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p
          ∂(cubeLebesgue d).prod (cubeLebesgue d)) := by
  rw [normalizedRegion_prod_eq,integral_smul_measure,smul_eq_mul]
  apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  apply setIntegral_le_integral
    (continuumFiniteShellMajorant_integrable (d:=d) (n:=n) (N:=N) (τ:=τ) (L:=L))
  filter_upwards [] with p
  exact continuumFiniteShellMajorant_nonneg hd hτ hL p

/-- True spatial variance is controlled by the integrated finite hull cover
for an arbitrary admissible unit-row family on a positive-mass region. -/
theorem region_variance_le_majorant {d n N:ℕ} (hd:2≤d) {τ L:ℝ}
    (hτ:0≤τ) (hL:0≤L) (A:Set (Fin d→ℝ)) (hA:MeasurableSet A)
    (hm:0<cubeLebesgue d A) (hcoords:∀x∈A,∀i,x i∈Set.Ico (0:ℝ) 1)
    (a:(Fin d→ℝ)→κ→ℝ) (haMeas:∀i,Measurable (fun x=>a x i))
    (hunit:∀x∈A,∑i,a x i^2=1)
    (hzero:∀x∈A,∀y∈A,∀u:Fin d→ℕ,
      (fun i=>(x i,y i))∈tensorOppositeHullShell u → (∑i,u i)<n → rowCorrelation a x y=0)
    (hcap:∀x∈A,∀y∈A,∀u:Fin d→ℕ,
      (fun i=>(x i,y i))∈tensorOppositeHullShell u → n≤(∑i,u i) →
      |rowCorrelation a x y|≤shapeOverlapCap d n ((∑i,u i)-n) L) :
    variance (spatialCoshAverage (normalizedRegionProbability A) τ a)
      (productStandardGaussian κ) ≤
      (((cubeLebesgue d A)⁻¹)^2).toReal *
        (∫p,continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p
          ∂(cubeLebesgue d).prod (cubeLebesgue d)) := by
  let μ:=normalizedRegionProbability A
  letI:IsProbabilityMeasure μ:=normalizedRegion_isProbability A hm
  have hsupp:∀ᵐx∂μ,x∈A:=normalizedRegion_ae_mem A hA
  obtain ⟨x₀,hx₀⟩:=hsupp.exists
  have hpair:∀ᵐp:(Fin d→ℝ)×(Fin d→ℝ)∂μ.prod μ,p.1∈A ∧ p.2∈A := by
    apply (Measure.ae_prod_iff_ae_ae (hA.prod hA)).2
    filter_upwards [hsupp] with x hx
    filter_upwards [hsupp] with y hy
    exact ⟨hx,hy⟩
  have hpoint:∀ᵐp∂μ.prod μ,pairRemainder τ a p≤
      continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p := by
    filter_upwards [hpair] with p hp
    exact pairRemainder_le_majorant hd hτ hL A hcoords a hunit hzero hcap p hp.1 hp.2
  have hMajInt:=majorant_integrable_normalized (d:=d) (n:=n) (N:=N) τ L A hm
  have hRmeas:Measurable (pairRemainder τ a) := by
    unfold pairRemainder rowCorrelation
    fun_prop
  have hRInt:Integrable (pairRemainder τ a) (μ.prod μ) := by
    apply hMajInt.mono' hRmeas.aestronglyMeasurable
    filter_upwards [hpoint] with p hp
    simpa [Real.norm_eq_abs,abs_of_nonneg (show 0≤pairRemainder τ a p by
      unfold pairRemainder; positivity)] using hp
  have hvar:variance (spatialCoshAverage μ τ a) (productStandardGaussian κ)≤
      ∫p,pairRemainder τ a p∂μ.prod μ := by
    have hb:=supported_variance_le_spatial_overlap_remainder μ A hA hsupp x₀ hx₀
      a τ hτ hunit haMeas
    convert hb using 1
    congr 1
    funext p
    dsimp [pairRemainder,rowCorrelation]
    ring
  exact hvar.trans ((integral_mono_ae hRInt hMajInt hpoint).trans
    (normalizedRegion_majorant_integral_le (by omega) τ L A hτ hL))

/-- Geometric data supplied by an actual family of dyadic tensor atoms. The
fields are spatial support, normalization and two-point overlap facts. -/
structure RegionRows (d n:ℕ) (ι:Type*) [Fintype ι] (q L:ℝ) where
  region : Set (Fin d→ℝ)
  region_measurable : MeasurableSet region
  mass_lower : ENNReal.ofReal q≤cubeLebesgue d region
  coordinates : ∀x∈region,∀i,x i∈Set.Ico (0:ℝ) 1
  rows : (Fin d→ℝ)→ι→ℝ
  rows_measurable : ∀i,Measurable (fun x=>rows x i)
  unit : ∀x∈region,∑i,rows x i^2=1
  zero : ∀x∈region,∀y∈region,∀u:Fin d→ℕ,
    (fun i=>(x i,y i))∈tensorOppositeHullShell u → (∑i,u i)<n → rowCorrelation rows x y=0
  cap : ∀x∈region,∀y∈region,∀u:Fin d→ℕ,
    (fun i=>(x i,y i))∈tensorOppositeHullShell u → n≤(∑i,u i) →
    |rowCorrelation rows x y|≤shapeOverlapCap d n ((∑i,u i)-n) L

/-- Full normalized-region variance after summing every shell and letting the
terminal coordinate residual tend to zero. -/
theorem regionRows_variance_le_shell_scale {d n:ℕ} (hd:2≤d) {q L τ:ℝ}
    (hq:0<q) (hL:0<L) (hτ:0≤τ)
    (hτbound:τ≤(Real.log 2/(4*L*(Nat.factorial (d-1):ℝ)))*((n:ℝ)+1))
    (s:RegionRows d n κ q L) :
    variance (spatialCoshAverage (normalizedRegionProbability s.region) τ s.rows)
      (productStandardGaussian κ) ≤
      (((cubeLebesgue d s.region)⁻¹)^2).toReal *
        (AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L *τ^2/nativeDimension d n) := by
  let pref:ℝ:=(((cubeLebesgue d s.region)⁻¹)^2).toReal
  let B:ℝ:=AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L*τ^2/nativeDimension d n
  let c:ℝ:=τ^2/2*Real.exp τ*(d:ℝ)
  have hm:0<cubeLebesgue d s.region:=(ENNReal.ofReal_pos.mpr hq).trans_le s.mass_lower
  have hpref:0≤pref:=ENNReal.toReal_nonneg
  have hc:0≤c:=by dsimp [c]; positivity
  have hfinite:∀N:ℕ,
      variance (spatialCoshAverage (normalizedRegionProbability s.region) τ s.rows)
        (productStandardGaussian κ) ≤pref*B+pref*c*(1/2:ℝ)^N := by
    intro N
    have hcore:=region_variance_le_majorant (d:=d) (n:=n) (N:=N) hd hτ hL.le
      s.region s.region_measurable hm s.coordinates s.rows s.rows_measurable s.unit s.zero s.cap
    have hs:=boundedProfile_actual_shell_sum_le_layer_card (d:=d) (n:=n) (N:=N)
      hd hτ hL (le_rfl : Real.log 2/(4*L*(Nat.factorial (d-1):ℝ))≤_ ) hτbound
    have hr:=AlignmentPaperContinuumResidual.spatialPairCoordinateResidual_real_measure_le (d:=d) N
    have hInt:(∫p,continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p
        ∂(cubeLebesgue d).prod (cubeLebesgue d))≤B+c*(1/2:ℝ)^N := by
      rw [continuumFiniteShellMajorant_integral_eq]
      calc
        _ ≤ (AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L*τ^2/
            ((2:ℝ)^n*hyperbolicCount d n))+
            (τ^2/2*Real.exp τ)*((d:ℝ)*(1/2:ℝ)^N) :=
          add_le_add hs (mul_le_mul_of_nonneg_left hr (by positivity))
        _ = _ := by dsimp [B,c,nativeDimension]; ring
    calc
      _ ≤ pref*(∫p,continuumFiniteShellMajorant (d:=d) (n:=n) (N:=N) τ L p
          ∂(cubeLebesgue d).prod (cubeLebesgue d)) := hcore
      _ ≤ pref*(B+c*(1/2:ℝ)^N) := mul_le_mul_of_nonneg_left hInt hpref
      _ = _ := by ring
  have hpow:Tendsto (fun N:ℕ=>(1/2:ℝ)^N) Filter.atTop (𝓝 0):=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim:Tendsto (fun N:ℕ=>pref*B+pref*c*(1/2:ℝ)^N) Filter.atTop (𝓝 (pref*B)) := by
    convert tendsto_const_nhds.add (hpow.const_mul (pref*c)) using 1 <;> simp
  exact ge_of_tendsto' hlim hfinite

/-- Uniform positive region mass removes the normalization coefficient. -/
theorem regionRows_variance_le_uniform {d n:ℕ} (hd:2≤d) {q L τ:ℝ}
    (hq:0<q) (hL:0<L) (hτ:0≤τ)
    (hτbound:τ≤(Real.log 2/(4*L*(Nat.factorial (d-1):ℝ)))*((n:ℝ)+1))
    (s:RegionRows d n κ q L) :
    variance (spatialCoshAverage (normalizedRegionProbability s.region) τ s.rows)
      (productStandardGaussian κ) ≤
      (q⁻¹^2*AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L)*τ^2/nativeDimension d n := by
  have hbase:=regionRows_variance_le_shell_scale hd hq hL hτ hτbound s
  have hinv:(cubeLebesgue d s.region)⁻¹≤(ENNReal.ofReal q)⁻¹ :=
    ENNReal.inv_le_inv.mpr s.mass_lower
  have hsquare:(cubeLebesgue d s.region)⁻¹^2≤(ENNReal.ofReal q)⁻¹^2 :=by gcongr
  have haTop:(ENNReal.ofReal q)⁻¹^2≠(⊤:ENNReal) :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hq)))
  have hpref:(((cubeLebesgue d s.region)⁻¹)^2).toReal≤q⁻¹^2 := by
    calc
      _ ≤ ((ENNReal.ofReal q)⁻¹^2).toReal:=ENNReal.toReal_mono haTop hsquare
      _ = _ := by simp [hq.le]
  have hfac:0≤AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L*τ^2/nativeDimension d n := by
    have hC:0<AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L :=
      AlignmentPaperContinuumShellBudgetScale.continuumShellConstant_pos d hL
    dsimp [nativeDimension,hyperbolicCount]
    positivity
  calc
    _ ≤ (((cubeLebesgue d s.region)⁻¹)^2).toReal*
        (AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L*τ^2/nativeDimension d n):=hbase
    _ ≤ q⁻¹^2*(AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d L*τ^2/nativeDimension d n):=
      mul_le_mul_of_nonneg_right hpref hfac
    _ = _ :=by ring

end BrownianSharp.AlignmentPaperGenericContinuumVariance
