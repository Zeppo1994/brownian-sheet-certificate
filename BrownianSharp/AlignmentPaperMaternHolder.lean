import BrownianSharp.AlignmentMaternTensorFeature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPaperMaternHolder
open AlignmentMaternSpectralFeature AlignmentMaternScalarFeature AlignmentMaternContinuousFeature

/-- A fractional frequency moment is dominated by a lower-smoothness Matérn
density, so Mathlib-backed density integrability supplies the moment. -/
theorem weighted_density_le (κ h θ ξ:ℝ) (hκ:0<κ) (hθ:0≤θ) :
    |ξ|^(2*θ)*density κ h ξ≤density κ (h-θ) ξ := by
  have habs : |ξ|^(2*θ)=(ξ^2)^θ := by
    rw [show 2*θ=(2:ℝ)*θ by rfl,Real.rpow_mul (abs_nonneg ξ),Real.rpow_two,sq_abs]
  have hpow:(ξ^2)^θ≤(κ^2+ξ^2)^θ :=
    Real.rpow_le_rpow (sq_nonneg _) (by nlinarith [sq_nonneg κ]) hθ
  calc
    _ ≤ (κ^2+ξ^2)^θ*density κ h ξ :=
      mul_le_mul_of_nonneg_right (by simpa [habs] using hpow) (density_pos κ h ξ hκ).le
    _ = density κ (h-θ) ξ := by
      unfold density
      change Real.rpow (κ^2+ξ^2) θ*Real.rpow (κ^2+ξ^2) (-(h+1/2)) =
        Real.rpow (κ^2+ξ^2) (-(h-θ+1/2))
      calc
        _ = Real.rpow (κ^2+ξ^2) (θ+(-(h+1/2))) :=
          (Real.rpow_add (by positivity : 0<κ^2+ξ^2) θ (-(h+1/2))).symm
        _ = _ := by congr 1; ring

theorem frequency_moment_integrable (κ h θ:ℝ) (hκ:0<κ)
    (hθ:0≤θ) (hθh:θ<h) :
    Integrable (fun ξ:ℝ=>|ξ|^(2*θ)*density κ h ξ) volume := by
  have ht : 0≤2*θ := by positivity
  have hc : Continuous (fun ξ:ℝ=>|ξ|^(2*θ)*density κ h ξ) :=
    (Real.continuous_rpow_const ht).comp continuous_abs |>.mul (density_continuous κ h hκ)
  apply (density_integrable κ (h-θ) hκ (sub_pos.mpr hθh)).mono' hc.aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (density_pos κ h ξ hκ).le)]
  exact weighted_density_le κ h θ ξ hκ hθ

/-- Interpolate the standard sine/cosine Lipschitz bound with their uniform
bound; both are established Mathlib trigonometric estimates. -/
theorem scalarPhase_sub_abs_le_holder (s t ξ θ:ℝ) (hθ:0<θ) (hθ1:θ≤1) :
    |scalarPhase s ξ-scalarPhase t ξ|≤4*|2*Real.pi*ξ*(s-t)|^θ := by
  let z:ℝ:=|2*Real.pi*ξ*(s-t)|
  have hz:0≤z:=abs_nonneg _
  have hlip:|scalarPhase s ξ-scalarPhase t ξ|≤2*z := by
    have hc:=Real.abs_cos_sub_cos_le (2*Real.pi*ξ*s) (2*Real.pi*ξ*t)
    have hs:=Real.abs_sin_sub_sin_le (2*Real.pi*ξ*s) (2*Real.pi*ξ*t)
    have he:2*Real.pi*ξ*s-2*Real.pi*ξ*t=2*Real.pi*ξ*(s-t):=by ring
    rw [he] at hc hs
    calc
      _ = |(Real.cos (2*Real.pi*ξ*s)-Real.cos (2*Real.pi*ξ*t))+
        (Real.sin (2*Real.pi*ξ*s)-Real.sin (2*Real.pi*ξ*t))| := by congr 1; unfold scalarPhase; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 2*z := by dsimp [z]; linarith
  have hbound:|scalarPhase s ξ-scalarPhase t ξ|≤4 :=
    (abs_sub _ _).trans (by linarith [scalarPhase_abs_le s ξ,scalarPhase_abs_le t ξ])
  change |scalarPhase s ξ-scalarPhase t ξ|≤4*z^θ
  by_cases hz0:z=0
  · rw [hz0,Real.zero_rpow hθ.ne']
    rw [hz0] at hlip
    linarith
  · by_cases hz1:z≤1
    · have hp:z≤z^θ := by
        simpa using Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hz (Ne.symm hz0)) hz1 hθ1
      nlinarith
    · have hp:1≤z^θ:=Real.one_le_rpow (le_of_not_ge hz1) hθ.le
      nlinarith

theorem frequency_moment_spectral_integrable (κ h θ:ℝ) (hκ:0<κ)
    (hθ:0≤θ) (hθh:θ<h) :
    Integrable (fun ξ:ℝ=>|ξ|^(2*θ)) (spectralMeasure κ h) := by
  unfold spectralMeasure
  apply (integrable_withDensity_iff (density_continuous κ h hκ).measurable.ennreal_ofReal
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)).2
  have hmom:=frequency_moment_integrable κ h θ hκ hθ hθh
  have he:∀ξ:ℝ,(ENNReal.ofReal (density κ h ξ)).toReal=density κ h ξ :=
    fun ξ=>ENNReal.toReal_ofReal (density_pos κ h ξ hκ).le
  simpa only [he,mul_comm] using hmom

def scalarHolderSquareConstant (κ h θ:ℝ):ℝ :=
  16*(2*Real.pi)^(2*θ)*(∫ ξ:ℝ,|ξ|^(2*θ)∂spectralMeasure κ h)

theorem scalarHolderSquareConstant_nonneg (κ h θ:ℝ) :
    0≤scalarHolderSquareConstant κ h θ := by
  unfold scalarHolderSquareConstant
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun _=>Real.rpow_nonneg (abs_nonneg _) _)

/-- Quantitative increment bound for the actual cosine-plus-sine L2 feature. -/
theorem scalarFeature_increment_sq_le (κ h θ s t:ℝ)
    (hκ:0<κ) (hh:0<h) (hθ:0<θ) (hθ1:θ≤1) (hθh:θ<h) :
    ‖scalarFeature κ h s hκ hh-scalarFeature κ h t hκ hh‖^2≤
      scalarHolderSquareConstant κ h θ*|s-t|^(2*θ) := by
  let μ:=spectralMeasure κ h
  let A:=16*(2*Real.pi)^(2*θ)*|s-t|^(2*θ)
  have hA:0≤A:=by dsimp [A]; positivity
  have hbound (ξ:ℝ):(scalarPhase s ξ-scalarPhase t ξ)^2≤A*|ξ|^(2*θ) := by
    have hp:=scalarPhase_sub_abs_le_holder s t ξ θ hθ hθ1
    have hpsq: (scalarPhase s ξ-scalarPhase t ξ)^2≤
        (4*|2*Real.pi*ξ*(s-t)|^θ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hp 2
    have hpowe: (|2*Real.pi*ξ*(s-t)|^θ)^2=|2*Real.pi*ξ*(s-t)|^(2*θ) := by
      rw [←Real.rpow_natCast (|2*Real.pi*ξ*(s-t)|^θ) 2,←Real.rpow_mul (abs_nonneg _)]
      congr 1
      ring
    have hfactor: |2*Real.pi*ξ*(s-t)|^(2*θ)=
        (2*Real.pi)^(2*θ)*|ξ|^(2*θ)*|s-t|^(2*θ) := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_pos Real.pi_pos]
      rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
      rw [Real.mul_rpow (by positivity) (abs_nonneg _),
        Real.mul_rpow (by positivity) (abs_nonneg _)]
    calc
      _ ≤ (4*|2*Real.pi*ξ*(s-t)|^θ)^2:=hpsq
      _ = A*|ξ|^(2*θ) := by rw [mul_pow,hpowe,hfactor]; dsimp [A]; ring
  have hmom:=frequency_moment_spectral_integrable κ h θ hκ hθ.le hθh
  rw [AlignmentSigmaFiniteL2Tensor.realLp_norm_sq]
  have hae:(fun ξ:ℝ=>(scalarFeature κ h s hκ hh-scalarFeature κ h t hκ hh) ξ^2)=ᵐ[μ]
      (fun ξ=>(scalarPhase s ξ-scalarPhase t ξ)^2) := by
    filter_upwards [Lp.coeFn_sub (scalarFeature κ h s hκ hh) (scalarFeature κ h t hκ hh),
      (scalarPhaseMemLp κ h s hκ hh).coeFn_toLp,
      (scalarPhaseMemLp κ h t hκ hh).coeFn_toLp] with ξ hsub hs ht
    change (scalarFeature κ h s hκ hh-scalarFeature κ h t hκ hh) ξ=
      scalarFeature κ h s hκ hh ξ-scalarFeature κ h t hκ hh ξ at hsub
    change scalarFeature κ h s hκ hh ξ=scalarPhase s ξ at hs
    change scalarFeature κ h t hκ hh ξ=scalarPhase t ξ at ht
    rw [hsub,hs,ht]
  rw [integral_congr_ae hae]
  calc
    (∫ ξ,(scalarPhase s ξ-scalarPhase t ξ)^2∂μ)≤∫ ξ,A*|ξ|^(2*θ)∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun _=>sq_nonneg _)
        (hmom.const_mul A) (ae_of_all _ hbound)
    _ = A*(∫ ξ,|ξ|^(2*θ)∂μ) := integral_const_mul _ _
    _ = scalarHolderSquareConstant κ h θ*|s-t|^(2*θ) := by
      dsimp [A,μ,scalarHolderSquareConstant]
      ring

def axisHolderConstant (κ h θ:ℝ) (hκ:0<κ) (hh:0<h):ℝ :=
  ‖scalarFeature κ h 0 hκ hh‖⁻¹*Real.sqrt (scalarHolderSquareConstant κ h θ)

theorem axisHolderConstant_nonneg (κ h θ:ℝ) (hκ:0<κ) (hh:0<h) :
    0≤axisHolderConstant κ h θ hκ hh := by
  unfold axisHolderConstant
  positivity

theorem normalizedAxis_holder (κ h θ s t:ℝ)
    (hκ:0<κ) (hh:0<h) (hθ:0<θ) (hθ1:θ≤1) (hθh:θ<h) :
    ‖normalizedAxis κ h s hκ hh-normalizedAxis κ h t hκ hh‖≤
      axisHolderConstant κ h θ hκ hh*|s-t|^θ := by
  have hC:=scalarHolderSquareConstant_nonneg κ h θ
  have hs:=scalarFeature_increment_sq_le κ h θ s t hκ hh hθ hθ1 hθh
  have hp:(|s-t|^θ)^2=|s-t|^(2*θ) := by
    rw [←Real.rpow_natCast (|s-t|^θ) 2,←Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hsq: ‖scalarFeature κ h s hκ hh-scalarFeature κ h t hκ hh‖^2≤
      (Real.sqrt (scalarHolderSquareConstant κ h θ)*|s-t|^θ)^2 := by
    rw [mul_pow,Real.sq_sqrt hC,hp]
    exact hs
  have hn:‖scalarFeature κ h s hκ hh-scalarFeature κ h t hκ hh‖≤
      Real.sqrt (scalarHolderSquareConstant κ h θ)*|s-t|^θ := by
    have hr:0≤Real.sqrt (scalarHolderSquareConstant κ h θ)*|s-t|^θ:=by positivity
    nlinarith [norm_nonneg (scalarFeature κ h s hκ hh-scalarFeature κ h t hκ hh)]
  unfold normalizedAxis axisHolderConstant
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn (by positivity:
    0≤‖scalarFeature κ h 0 hκ hh‖⁻¹)

/-- Global quantitative regularity of the actual normalized tensor Matérn
feature, with every fixed exponent below both h and one. -/
theorem maternSheetFeature_holder {d:ℕ} (κ:Fin d→ℝ) (h θ:ℝ)
    (hκ:∀i,0<κ i) (hh:0<h) (hθ:0<θ) (hθ1:θ≤1) (hθh:θ<h) :
    ∃ C:ℝ,0<C ∧ ∀x y:HaarQuarter.BrownianCubeAnchor d,
      ‖AlignmentMaternTensorFeature.maternSheetFeature κ h hκ hh x-
        AlignmentMaternTensorFeature.maternSheetFeature κ h hκ hh y‖≤C*(dist x y)^θ := by
  classical
  letI (i:Fin d):IsFiniteMeasure (spectralMeasure (κ i) h):=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  let μ:Fin d→Measure ℝ:=fun i=>spectralMeasure (κ i) h
  let T:=AlignmentSigmaFiniteL2Tensor.tensorContinuous (μ:=μ)
  let v (x:HaarQuarter.BrownianCubeAnchor d):∀i,Lp ℝ 2 (μ i):=
    fun i=>normalizedAxis (κ i) h (x.val i) (hκ i) hh
  let L:ℝ:=∑i:Fin d,axisHolderConstant (κ i) h θ (hκ i) hh
  have hL:0≤L:=Finset.sum_nonneg (fun i _=>axisHolderConstant_nonneg _ _ _ _ _)
  have hT:‖T‖≤1:=by
    dsimp [T,AlignmentSigmaFiniteL2Tensor.tensorContinuous]
    exact MultilinearMap.mkContinuous_norm_le
      (AlignmentSigmaFiniteL2Tensor.tensorMultilinear (μ:=μ)) (by norm_num)
      (by intro w; simp [AlignmentSigmaFiniteL2Tensor.tensorMultilinear,
        AlignmentSigmaFiniteL2Tensor.productVector_norm])
  refine ⟨1+(d:ℝ)*L,by positivity,?_⟩
  intro x y
  have hv (z:HaarQuarter.BrownianCubeAnchor d):‖v z‖≤1:=by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro i
    exact (normalizedAxis_norm (κ i) h (z.val i) (hκ i) hh).le
  have hcoord (i:Fin d):|x.val i-y.val i|≤dist x y:=by
    change |x.val i-y.val i|≤‖x.val-y.val‖
    simpa using norm_le_pi_norm (x.val-y.val) i
  have hLcoord (i:Fin d):axisHolderConstant (κ i) h θ (hκ i) hh≤L:=
    Finset.single_le_sum (fun j _=>axisHolderConstant_nonneg _ _ _ _ _) (Finset.mem_univ i)
  have hdiff:‖v x-v y‖≤L*(dist x y)^θ:=by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    have hs:=normalizedAxis_holder (κ i) h θ (x.val i) (y.val i) (hκ i) hh hθ hθ1 hθh
    exact hs.trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hcoord i) hθ.le)
      (axisHolderConstant_nonneg _ _ _ _ _)).trans
        (mul_le_mul_of_nonneg_right (hLcoord i) (by positivity)))
  have hmulti:=T.norm_image_sub_le (v x) (v y)
  have hm:‖T (v x)-T (v y)‖≤(d:ℝ)*(L*(dist x y)^θ):=by
    have hmax:max ‖v x‖ ‖v y‖≤1:=max_le (hv x) (hv y)
    calc
      _ ≤ ‖T‖*(d:ℝ)*max ‖v x‖ ‖v y‖^(d-1)*‖v x-v y‖:=by simpa using hmulti
      _ ≤ 1*(d:ℝ)*(1:ℝ)^(d-1)*(L*(dist x y)^θ):=by gcongr
      _ = _:=by simp
  change ‖T (v x)-T (v y)‖≤_
  exact hm.trans (by nlinarith [Real.rpow_nonneg (dist_nonneg (x:=x) (y:=y)) θ])

def maternHolderExponent (h:ℝ):ℝ:=min (h/2) (1/2)

theorem maternHolderExponent_pos {h:ℝ} (hh:0<h):0<maternHolderExponent h:=
  lt_min (by positivity) (by norm_num)

/-- The global squared-increment input for the actual graded Gaussian
small-ball construction, with a strictly positive exponent for every h>0. -/
theorem maternSheetFeature_increment_holder {d:ℕ} (κ:Fin d→ℝ) (h:ℝ)
    (hκ:∀i,0<κ i) (hh:0<h) :
    ∃ R:ℝ,0<R ∧ ∀x y:HaarQuarter.BrownianCubeAnchor d,
      ‖AlignmentMaternTensorFeature.maternSheetFeature κ h hκ hh x-
        AlignmentMaternTensorFeature.maternSheetFeature κ h hκ hh y‖^2≤
          R*(dist x y)^(2*maternHolderExponent h) := by
  have hθ:=maternHolderExponent_pos hh
  have hθ1:maternHolderExponent h≤1:=by
    have hmin:=min_le_right (h/2) (1/2:ℝ)
    change min (h/2) (1/2:ℝ)≤1
    linarith
  have hθh:maternHolderExponent h<h:=
    (min_le_left (h/2) (1/2:ℝ)).trans_lt (by linarith)
  obtain ⟨C,hC,hbound⟩:=maternSheetFeature_holder κ h (maternHolderExponent h) hκ hh hθ hθ1 hθh
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro x y
  have hp:((dist x y)^(maternHolderExponent h))^2=
      (dist x y)^(2*maternHolderExponent h):=by
    rw [←Real.rpow_natCast ((dist x y)^(maternHolderExponent h)) 2,
      ←Real.rpow_mul dist_nonneg]
    congr 1
    ring
  have hs:=pow_le_pow_left₀ (norm_nonneg _) (hbound x y) 2
  rw [mul_pow,hp] at hs
  exact hs

end BrownianSharp.AlignmentPaperMaternHolder
