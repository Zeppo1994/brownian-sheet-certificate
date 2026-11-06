import BrownianSharp.AlignmentPaperGenericSmoothBumpSynthesis
import BrownianSharp.AlignmentPaperGenericBumpCertified
import BrownianSharp.AlignmentPaperContinuumSynthesis
import BrownianSharp.AlignmentPaperQuantization
import BrownianSharp.GaussianRows
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import BrownianSharp.AlignmentExponentialContinuousCover
import BrownianSharp.AlignmentExponentialBoxEntropy
import BrownianSharp.AlignmentEndpointGaussianBox
import BrownianSharp.AlignmentPeriodicCutoffClasses
import BrownianSharp.AlignmentPeriodicCutoffScaling
import BrownianSharp.AlignmentLatestPeriodicEntropy
import BrownianSharp.AlignmentPaperPeriodicComplete
import BrownianSharp.AlignmentAmbientWidth
import BrownianSharp.PeriodicCoverRate
import Mathlib.Tactic

/-! Entropy lower bounds for the literal coordinatewise mean-zero periodic Besov
class, using the actual mean-zero smooth bump and its Gaussian confinement. -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace BrownianSharp.AlignmentPaperMeanZeroBesovEntropy

open BrownianSharp.AlignmentPaperGenericSmoothBumpBesov
open BrownianSharp.AlignmentPaperGenericBumpCertified
open BrownianSharp.AlignmentPaperContinuumGenericBump
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus

/-- Literal coordinatewise mean-zero condition on a periodic function. -/
def CoordinatewiseMeanZero {d : ℕ} (f : RealPeriodic d) : Prop :=
  ∀ i : Fin d, ∀ x : Fin d → UnitAddCircle,
    (∫ t : UnitAddCircle, f (Function.update x i t)
      ∂AddCircle.haarAddCircle) = 0

def MeanZeroBesovClass {d : ℕ} (p : ℝ≥0∞) (r : ℝ) (theta : ℝ≥0∞) : Set (RealPeriodic d) :=
  {f | BesovUnitBall p r theta f ∧ CoordinatewiseMeanZero f}

/-- Finite-theta Besov unit balls are stable under contractions. -/
theorem besovUnitBall_smul_of_le_one {d : ℕ} (p : ℝ≥0∞) (r : ℝ)
    (theta : ℝ≥0∞) (htop : theta ≠ ⊤)
    (hθ : 0 < theta.toReal) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : RealPeriodic d)
    (hf : SmoothResolution.BesovUnitBall p r theta f) :
    SmoothResolution.BesovUnitBall p r theta (c • f) := by
  rw [SmoothResolution.BesovUnitBall, if_neg htop] at hf ⊢
  letI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
    rw [BrownianSharp.unitAddTorus_volume_eq_productHaar]
    infer_instance
  have hscale := AlignmentPeriodicCutoffScaling.BesovEnergy_smul
    (d:=d) (φ:=AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff)
    hc p r theta f
  have hscale' :
      (∑' s : Fin d → ℕ, SmoothResolution.weightedBlockNorm p r s (c • f) ^ theta.toReal) =
        ENNReal.ofReal (c ^ theta.toReal) *
          (∑' s : Fin d → ℕ, SmoothResolution.weightedBlockNorm p r s f ^ theta.toReal) := by
    simpa using hscale
  rw [hscale']
  have hpow : c ^ theta.toReal ≤ 1 := Real.rpow_le_one hc.le hc1 hθ.le
  have hfactor : ENNReal.ofReal (c ^ theta.toReal) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact hpow
  calc
    ENNReal.ofReal (c ^ theta.toReal) *
        (∑' s : Fin d → ℕ, SmoothResolution.weightedBlockNorm p r s f ^ theta.toReal)
      ≤ 1 * 1 := mul_le_mul hfactor hf (by positivity) (by norm_num)
    _ = 1 := one_mul 1

open BrownianSharp.AlignmentPaperMeanZeroBump

/-- Every periodized zeroth-order copy of a zero-integral bump has zero
circle mean. -/
theorem periodizedDerivative_mean_zero {ψ : SmoothCompactBump}
    {b : AdmissibleBump} (hψ : ψ.atom = b.atom)
    (hmean : (∫ x in (0:ℝ)..1, b.atom x) = 0)
    (s j : ℕ) (hj : j < 2^s) :
    (∫ x : UnitAddCircle, periodizedDerivative ψ s j hj 0 x
      ∂AddCircle.haarAddCircle) = 0 := by
  let H : UnitAddCircle → ℝ := fun x => periodizedDerivative ψ s j hj 0 x
  have hpre := AddCircle.intervalIntegral_preimage (T := (1:ℝ)) (t := (0:ℝ)) H
  have hunit : (∫ x : UnitAddCircle, H x ∂AddCircle.haarAddCircle) =
      ∫ x in (0:ℝ)..1, H (x : UnitAddCircle) := by
    rw [AddCircle.integral_haarAddCircle]
    norm_num
    rw [← hpre]
    norm_num only [zero_add]
  rw [hunit]
  calc
    (∫ x in (0:ℝ)..1, H (x : UnitAddCircle)) =
        ∫ x in (0:ℝ)..1, b.atom ((2:ℝ)^s*x-(j:ℝ)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      change periodizedDerivative ψ s j hj 0 (x : UnitAddCircle) = _
      rw [periodizedDerivative_unit_interval ψ s j hj 0 x ⟨hx.1.le, hx.2⟩]
      simp only [iteratedDeriv_zero, dyadicLift]
      rw [hψ]
    _ = 0 := dyadic_bump_integral_zero b hmean s j hj

private theorem genericPeriodicAtom_update_factor {d n : ℕ}
    (ψ : SmoothCompactBump) (a : LayerIndex d n) (x : Fin d → UnitAddCircle)
    (i : Fin d) (t : UnitAddCircle) :
    genericPeriodicAtom ψ a (Function.update x i t) =
      periodizedDerivative ψ (layerIndexDepth a i) (layerIndexCell a i)
        (layerIndexCell_lt a i) 0 t *
      ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
        periodizedDerivative ψ (layerIndexDepth a j) (layerIndexCell a j)
          (layerIndexCell_lt a j) 0 (x j) := by
  classical
  simp only [genericPeriodicAtom, ContinuousMap.coe_mk]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Function.update_of_ne hji]

/-- The generic periodic tensor atoms inherit the zero mean in every
coordinate from the one-dimensional zero-integral bump. -/
theorem genericPeriodicAtom_coordinate_mean_zero {d n : ℕ}
    (ψ : SmoothCompactBump) (b : AdmissibleBump) (hψ : ψ.atom = b.atom)
    (hmean : (∫ x in (0:ℝ)..1, b.atom x) = 0)
    (a : LayerIndex d n) (i : Fin d) (x : Fin d → UnitAddCircle) :
    (∫ t : UnitAddCircle,
      genericPeriodicAtom ψ a (Function.update x i t)
        ∂AddCircle.haarAddCircle) = 0 := by
  classical
  rw [show (fun t : UnitAddCircle =>
      genericPeriodicAtom ψ a (Function.update x i t)) =
      (fun t => periodizedDerivative ψ (layerIndexDepth a i)
        (layerIndexCell a i) (layerIndexCell_lt a i) 0 t *
        ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
          periodizedDerivative ψ (layerIndexDepth a j) (layerIndexCell a j)
            (layerIndexCell_lt a j) 0 (x j)) by
      funext t
      exact genericPeriodicAtom_update_factor ψ a x i t]
  rw [integral_mul_const]
  simp [periodizedDerivative_mean_zero hψ hmean]

/-- Closed-cube evaluation of the zeroth-order periodized atom agrees with
the genuine admissible bump on its dyadic cell. -/
theorem periodizedDerivative_closed_interval {ψ : SmoothCompactBump}
    {b : AdmissibleBump} (hψ : ψ.atom = b.atom)
    (s j : ℕ) (hj : j < 2^s) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    periodizedDerivative ψ s j hj 0 (x : UnitAddCircle) =
      b.atom ((2:ℝ)^s*x-(j:ℝ)) := by
  by_cases hlt : x < 1
  · rw [periodizedDerivative_unit_interval ψ s j hj 0 x ⟨hx.1,hlt⟩]
    simp only [iteratedDeriv_zero, dyadicLift, hψ]
  · have hxeq : x = 1 := by linarith [hx.2]
    subst x
    have hone : ((1:ℝ):UnitAddCircle) = 0 := by
      exact_mod_cast AddCircle.coe_period (p:=(1:ℝ))
    rw [hone]
    have hz := periodizedDerivative_unit_interval ψ s j hj 0 0 (by norm_num)
    rw [show ((0:ℝ):UnitAddCircle)=0 from rfl] at hz
    rw [hz]
    simp only [iteratedDeriv_zero, dyadicLift, hψ]
    have hneg : (2:ℝ)^s*0-(j:ℝ) ≤ 0 := by simp
    have hpos : 1 ≤ (2:ℝ)^s*1-(j:ℝ) := by
      have hjr : (j:ℝ)+1 ≤ (2:ℝ)^s := by exact_mod_cast Nat.succ_le_of_lt hj
      linarith
    rw [b.eq_zero_of_outside (Or.inl hneg), b.eq_zero_of_outside (Or.inr hpos)]

/-- The periodic generic synthesis is the actual continuum bump sum on the
closed fundamental cube. -/
theorem genericPeriodicSynthesis_cube_eq {d n : ℕ}
    (ψ : SmoothCompactBump) (b : AdmissibleBump) (hψ : ψ.atom = b.atom)
    (z : LayerIndex d n → ℝ) (x : Fin d → ℝ)
    (hx : x ∈ AlignmentPaperContinuumGoodRegion.cubeSet d) :
    genericPeriodicSynthesisLinear ψ z
        (AlignmentPaperContinuumSynthesis.realCubeToTorus x) =
      bumpSynthesis b z x := by
  classical
  change (∑ a : LayerIndex d n, z a • genericPeriodicAtom ψ a)
      (AlignmentPaperContinuumSynthesis.realCubeToTorus x) = _
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  unfold bumpSynthesis BrownianSharp.AlignmentPaperContinuumGenericBump.cubeBumpAtom
  apply Finset.sum_congr rfl
  intro a ha
  calc
    z a * ∏ i : Fin d,
        periodizedDerivative ψ (layerIndexDepth a i) (layerIndexCell a i)
          (layerIndexCell_lt a i) 0 (x i : UnitAddCircle) =
      z a * ∏ i : Fin d, b.atom
        ((2:ℝ)^(layerIndexDepth a i)*(x i)-(layerIndexCell a i:ℝ)) := by
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          exact periodizedDerivative_closed_interval hψ
            (layerIndexDepth a i) (layerIndexCell a i) (layerIndexCell_lt a i) (x i)
            (hx i (Set.mem_univ i))
    _ = (∏ i : Fin d, b.atom
        ((2:ℝ)^(layerIndexDepth a i)*(x i)-(layerIndexCell a i:ℝ))) * z a := by ring

/-- Coefficient synthesis preserves every coordinate mean exactly. -/
theorem genericPeriodicSynthesis_coordinate_mean_zero {d n : ℕ}
    (ψ : SmoothCompactBump) (b : AdmissibleBump) (hψ : ψ.atom = b.atom)
    (hmean : (∫ x in (0:ℝ)..1, b.atom x) = 0)
    (xcoef : LayerIndex d n → ℝ) :
    CoordinatewiseMeanZero (genericPeriodicSynthesisLinear ψ xcoef) := by
  classical
  intro i x
  dsimp only [genericPeriodicSynthesisLinear]
  change (∫ t : UnitAddCircle,
      (∑ a : LayerIndex d n, xcoef a • genericPeriodicAtom ψ a)
        (Function.update x i t) ∂AddCircle.haarAddCircle) = 0
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro a ha
    rw [integral_const_mul]
    simp [genericPeriodicAtom_coordinate_mean_zero ψ b hψ hmean a i x]
  · intro a ha
    have hcont : Continuous (fun t : UnitAddCircle =>
        genericPeriodicAtom ψ a (Function.update x i t)) := by
      apply (genericPeriodicAtom ψ a).continuous.comp
      exact continuous_const.update i continuous_id
    have hmul : Continuous (fun t : UnitAddCircle =>
        xcoef a * genericPeriodicAtom ψ a (Function.update x i t)) := by
      simpa [mul_comm] using hcont.const_mul (xcoef a)
    exact hmul.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- A fixed scale of every coefficient-box synthesis lies in the literal
coordinatewise-mean-zero Besov class. -/
theorem exists_meanZero_scaled_box_synthesis
    {d : ℕ} (hd : 2 ≤ d) (ψ : SmoothCompactBump) (b : AdmissibleBump)
    (hψ : ψ.atom = b.atom) (hmean : (∫ x in (0:ℝ)..1, b.atom x) = 0)
    (M r : ℝ) (theta p : ℝ≥0∞) (hM : 0 < M) (hr : 0 < r)
    (htop : theta ≠ ⊤) (hθ : 2 ≤ theta.toReal) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ xcoef : LayerIndex d n → ℝ,
      (∀ j, |xcoef j| ≤ M) →
      (c * periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
          genericPeriodicSynthesisLinear ψ xcoef ∈
        MeanZeroBesovClass p r theta := by
  have hθ' : 1 ≤ theta :=
    (ENNReal.toReal_le_toReal ENNReal.one_ne_top htop).1 (by norm_num; linarith)
  obtain ⟨c,hc,hbox⟩ := generic_exists_scaled_box_synthesis_Besov_spatial
    hd ψ M r theta p hM hr hθ' hp
  refine ⟨c,hc,?_⟩
  intro n xcoef hcoeff
  obtain ⟨amp,hamp,hamp1,hbesov,hlower⟩ := hbox n xcoef hcoeff
  let A : ℝ := c * periodicSynthesisScale d n r (1/2-1/theta.toReal)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hc (periodicSynthesisScale_pos (by omega) r
      (1/2-1/theta.toReal))
  have hAamp : A ≤ amp := by
    have htheta : (1/2-1/theta.toReal)-1/2 = -(1/theta.toReal) := by ring
    have hscale : c * (2:ℝ)^(-r*(n:ℝ)) *
        (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) =
        c * periodicSynthesisScale d n r (1/2-1/theta.toReal) := by
      rw [periodicSynthesisScale, shape_card d n (by omega), hyperbolicCount, htheta]
      ring
    dsimp [A]
    rw [← hscale]
    exact hlower
  let scale : ℝ := A / amp
  have hscale : 0 < scale := div_pos hA hamp
  have hscale1 : scale ≤ 1 := (div_le_one hamp).2 hAamp
  have hcontract := besovUnitBall_smul_of_le_one p r theta htop
    (by linarith : 0 < theta.toReal) hscale hscale1
    (amp • genericPeriodicSynthesisLinear ψ xcoef) hbesov
  have hmap : scale • (amp • genericPeriodicSynthesisLinear ψ xcoef) =
      A • genericPeriodicSynthesisLinear ψ xcoef := by
    rw [smul_smul]
    congr 1
    dsimp [scale]
    field_simp
  have hbesovA : SmoothResolution.BesovUnitBall p r theta
      (A • genericPeriodicSynthesisLinear ψ xcoef) := by
    rw [← hmap]
    exact hcontract
  have hmeanA : CoordinatewiseMeanZero
      (A • genericPeriodicSynthesisLinear ψ xcoef) := by
    intro i x
    change (∫ t : UnitAddCircle,
      A * genericPeriodicSynthesisLinear ψ xcoef (Function.update x i t)
        ∂AddCircle.haarAddCircle) = 0
    rw [integral_const_mul]
    rw [genericPeriodicSynthesis_coordinate_mean_zero ψ b hψ hmean xcoef i x]
    simp
  exact ⟨hbesovA,hmeanA⟩

/-- The finite generic synthesis viewed as a continuous random path. -/
private def genericPeriodicPath {d n : ℕ} (ψ : SmoothCompactBump) :
    (LayerIndex d n → ℝ) → C(UnitAddTorus (Fin d), ℝ) :=
  genericPeriodicSynthesisLinear ψ

/-- Finite generic-bump syntheses are centered Gaussian processes under the
actual product standard Gaussian coefficient law. -/
theorem genericPeriodicPath_isGaussianProcess {d n : ℕ}
    (ψ : SmoothCompactBump) :
    IsGaussianProcess
      (fun x : UnitAddTorus (Fin d) =>
        fun z : LayerIndex d n → ℝ => genericPeriodicPath ψ z x)
      (productStandardGaussian (LayerIndex d n)) := by
  classical
  constructor
  intro I
  let E : RealPeriodic d →ₗ[ℝ] (I → ℝ) :=
    LinearMap.pi (fun i : I => (ContinuousMap.evalCLM ℝ (i : UnitAddTorus (Fin d))).toLinearMap)
  let L : (LayerIndex d n → ℝ) →ₗ[ℝ] (I → ℝ) :=
    E.comp (genericPeriodicSynthesisLinear (d:=d) (n:=n) ψ)
  let G : LayerIndex d n → (LayerIndex d n → ℝ) → ℝ := fun a z => z a
  have hG : ∀ a, Measurable (G a) := fun a => measurable_pi_apply a
  have hLaw : ∀ a, (productStandardGaussian (LayerIndex d n)).map (G a) =
      gaussianReal 0 1 := by
    intro a
    simp [G, productStandardGaussian_coordinate_law]
  have hcoord := fun a =>
    (GaussianRows.coordinate_hasLaw G hG hLaw a).hasGaussianLaw
  have hindep : iIndepFun G (productStandardGaussian (LayerIndex d n)) :=
    productStandardGaussian_coordinates_independent (LayerIndex d n)
  have hjoint : HasGaussianLaw (fun z a => G a z)
      (productStandardGaussian (LayerIndex d n)) :=
    iIndepFun.hasGaussianLaw hcoord hindep
  have hmap := hjoint.map L.toContinuousLinearMap
  have hEq (z : LayerIndex d n → ℝ) :
      I.restrict (fun x => genericPeriodicPath ψ z x) = L z := by
    funext i
    rfl
  have hEq' (z : LayerIndex d n → ℝ) :
      L (fun a => G a z) = I.restrict (fun x => genericPeriodicPath ψ z x) := by
    rw [show (fun a : LayerIndex d n => G a z) = z by funext a; rfl]
    exact (hEq z).symm
  exact hmap.congr (ae_of_all _ hEq')

/-- The translated-ball cap after multiplying the generic synthesis by a
fixed positive amplitude. The confinement radius is stated before scaling. -/
theorem genericPeriodicPath_scaled_translated_ball_mass_le
    {d n : ℕ} (ψ : SmoothCompactBump) (b : AdmissibleBump)
    (hψ : ψ.atom = b.atom) {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a)
    (ρ : NNReal)
    (hconf : productStandardGaussian (LayerIndex d n)
      {z | ∀ x ∈ AlignmentPaperContinuumGoodRegion.cubeSet d,
        |bumpSynthesis b z x| ≤ Real.sqrt 2 * ((ρ:ℝ)/A)} ≤
          ENNReal.ofReal (Real.exp (-a))) :
    ∀ f : C(UnitAddTorus (Fin d), ℝ),
      productStandardGaussian (LayerIndex d n)
        {z | edist (A • genericPeriodicPath ψ z) f ≤ (ρ:ℝ≥0∞)} ≤
          ENNReal.ofReal (Real.exp (-a/2)) := by
  classical
  let P := productStandardGaussian (LayerIndex d n)
  let F : (LayerIndex d n → ℝ) → C(UnitAddTorus (Fin d), ℝ) :=
    fun z => A • genericPeriodicPath ψ z
  have hbase : Continuous (genericPeriodicPath (d:=d) (n:=n) ψ) := by
    change Continuous (genericPeriodicSynthesisLinear (d:=d) (n:=n) ψ)
    exact LinearMap.continuous_of_finiteDimensional
      (genericPeriodicSynthesisLinear (d:=d) (n:=n) ψ)
  have hcont : Continuous F := hbase.const_smul A
  have hF : Measurable F := hcont.measurable
  have hX : IsGaussianProcess (fun x z => F z x) P := by
    simpa [P, F] using (genericPeriodicPath_isGaussianProcess ψ).smul (fun _ : UnitAddTorus (Fin d) => A)
  have hmean : ∀ x, ∫ z, F z x ∂P = 0 := by
    intro x
    let G : LayerIndex d n → (LayerIndex d n → ℝ) → ℝ := fun i z => z i
    let c : LayerIndex d n → ℝ := fun i => genericPeriodicAtom ψ i x
    have hG : ∀ i, Measurable (G i) := fun i => measurable_pi_apply i
    have hLaw : ∀ i, P.map (G i) = gaussianReal 0 1 := by
      intro i
      simp [P, G, productStandardGaussian_coordinate_law]
    have hmean' := GaussianRows.row_mean G hG hLaw c
    have hmean0 : ∫ z, genericPeriodicPath ψ z x ∂P = 0 := by
      simpa [G, c, P, genericPeriodicPath, genericPeriodicSynthesisLinear,
        GaussianRows.row, smul_eq_mul, mul_comm] using hmean'
    change (∫ z, A * genericPeriodicPath ψ z x ∂P) = 0
    rw [integral_const_mul, hmean0]
    simp
  intro f
  have hshift := centered_gaussian_translated_ball_mass_sq_le
    F hF hX hmean f (ρ:ℝ) (by positivity)
  have hleft : (P.map F) (Metric.closedBall f (ρ:ℝ)) =
      P {z | edist (F z) f ≤ (ρ:ℝ≥0∞)} := by
    rw [Measure.map_apply hF measurableSet_closedBall]
    congr 1
    ext z
    simp [Metric.mem_closedBall, edist_dist, dist_comm]
  have hcenter : (P.map F)
      (Metric.closedBall (0 : C(UnitAddTorus (Fin d), ℝ))
        (Real.sqrt 2 * (ρ:ℝ))) ≤ ENNReal.ofReal (Real.exp (-a)) := by
    rw [Measure.map_apply hF measurableSet_closedBall]
    apply le_trans (measure_mono ?_) hconf
    intro z hz
    intro x hx
    have hnormS : ‖F z‖ ≤ Real.sqrt 2 * (ρ:ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnormBase : ‖genericPeriodicPath ψ z‖ ≤
        Real.sqrt 2 * ((ρ:ℝ)/A) := by
      have hmul : ‖genericPeriodicPath ψ z‖ * A ≤ Real.sqrt 2 * (ρ:ℝ) := by
        simpa [F, norm_smul, Real.norm_eq_abs, abs_of_pos hA, mul_comm] using hnormS
      calc
        ‖genericPeriodicPath ψ z‖ ≤ (Real.sqrt 2 * (ρ:ℝ))/A :=
          (le_div_iff₀ hA).2 hmul
        _ = Real.sqrt 2 * ((ρ:ℝ)/A) := by ring
    let torusx := AlignmentPaperContinuumSynthesis.realCubeToTorus x
    have hpoint := (genericPeriodicPath ψ z).norm_coe_le_norm torusx
    have hval : |genericPeriodicPath ψ z torusx| ≤
        Real.sqrt 2 * ((ρ:ℝ)/A) := by
      calc
        |genericPeriodicPath ψ z torusx| =
            ‖genericPeriodicPath ψ z torusx‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖genericPeriodicPath ψ z‖ := hpoint
        _ ≤ _ := hnormBase
    have heval : genericPeriodicPath ψ z torusx = bumpSynthesis b z x :=
      genericPeriodicSynthesis_cube_eq ψ b hψ z x hx
    simpa [heval] using hval
  have hshift' :
      (P {z | edist (F z) f ≤ (ρ:ℝ≥0∞)})^2 ≤ ENNReal.ofReal (Real.exp (-a)) := by
    calc
      _ = ((P.map F) (Metric.closedBall f (ρ:ℝ)))^2 := by rw [hleft]
      _ ≤ (P.map F) (Metric.closedBall 0 (Real.sqrt 2*(ρ:ℝ))) := hshift
      _ ≤ _ := hcenter
  have hsquare : (Real.exp (-a/2))^2 = Real.exp (-a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  let xmass := P {z | edist (F z) f ≤ (ρ:ℝ≥0∞)}
  have hxle : xmass ≤ 1 := by
    calc
      xmass ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp [P]
  have hxfinite : xmass ≠ ∞ := ne_of_lt (lt_of_le_of_lt hxle (by simp))
  have hreal : xmass.toReal^2 ≤ Real.exp (-a) := by
    have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top hshift'
    rw [ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.exp (-a))] at hm
    exact hm
  have hroot : xmass.toReal ≤ Real.exp (-a/2) := by
    have hsqrt := Real.sqrt_le_sqrt hreal
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hsqrt
    have hrhs : Real.sqrt (Real.exp (-a)) = Real.exp (-a/2) := by
      rw [← hsquare, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hsqrt.trans_eq hrhs
  have hmass : xmass ≤ ENNReal.ofReal (Real.exp (-a/2)) := by
    rw [← ENNReal.ofReal_toReal hxfinite]
    exact ENNReal.ofReal_le_ofReal hroot
  simpa [P, F, xmass] using hmass

private theorem exists_gaussian_box_for_cost {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ENNReal.ofReal (Real.exp (-δ)) ≤
      gaussianReal 0 1 (Set.Icc (-M) M) := by
  obtain ⟨M,hM,hgauss⟩ := exists_standardGaussian_box_for_exponent
    (b:=4*δ) (by positivity)
  have hgauss' : ENNReal.ofReal (Real.exp (-δ)) ≤
      gaussianReal 0 1 (Set.Icc (-M) M) := by
    convert hgauss using 1 <;> congr 1 <;> ring
  exact ⟨M,hM,hgauss'⟩

private theorem coefficientBox_nativeDimension_mass {d n : ℕ}
    (hd : 1 ≤ d) {M δ : ℝ} (hδ : 0 < δ)
    (hgauss : ENNReal.ofReal (Real.exp (-δ)) ≤
      gaussianReal 0 1 (Set.Icc (-M) M)) :
    ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
      productStandardGaussian (LayerIndex d n) (coefficientBox M) := by
  let μ : LayerIndex d n → Measure ℝ := fun _ => gaussianReal 0 1
  have hcoord : ∀ i, ENNReal.ofReal (Real.exp (-(4*δ)/4)) ≤
      μ i (Set.Icc (-M) M) := by
    intro i
    change ENNReal.ofReal (Real.exp (-(4*δ)/4)) ≤
      gaussianReal 0 1 (Set.Icc (-M) M)
    rw [show -(4*δ)/4 = -δ by ring]
    exact hgauss
  have hbox := productMeasure_coefficientBox_exp_lower μ
    (by intro i; infer_instance) M (4*δ) (by positivity) hcoord
  have hdim : (Fintype.card (LayerIndex d n):ℝ) = nativeDimension d n := by
    rw [layerIndex_card d n hd, nativeDimension, hyperbolicCount]
    push_cast
    ring
  have hexp : -(4*δ)*(Fintype.card (LayerIndex d n):ℝ)/4 =
      -δ*nativeDimension d n := by rw [hdim]; ring
  have hbox' : ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
      productStandardGaussian (LayerIndex d n) (coefficientBox M) := by
    have hh := hbox
    rw [hexp] at hh
    simpa [μ, productStandardGaussian] using hh
  exact hbox'

private theorem scaledMeanZeroBox_subset {d n : ℕ}
    (ψ : SmoothCompactBump) (c M r : ℝ) (theta p : ℝ≥0∞)
    (hclass : ∀ xcoef : LayerIndex d n → ℝ,
      (∀ j, |xcoef j| ≤ M) →
      (c*periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
        genericPeriodicSynthesisLinear ψ xcoef ∈ MeanZeroBesovClass p r theta) :
    coefficientBox (ι:=LayerIndex d n) M ⊆
      {xcoef | (c*periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
        genericPeriodicSynthesisLinear ψ xcoef ∈ MeanZeroBesovClass p r theta} := by
  intro xcoef hxcoef
  have hbounded : ∀ j, |xcoef j| ≤ M := by
    intro j
    have hj := hxcoef j
    exact abs_le.mpr (by simpa [Set.mem_Icc] using hj)
  change (c*periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
    genericPeriodicSynthesisLinear ψ xcoef ∈ MeanZeroBesovClass (d:=d) p r theta
  exact hclass xcoef hbounded

private theorem scaledMeanZeroBox_mass {d n : ℕ}
    (ψ : SmoothCompactBump) (c M δ r : ℝ) (theta p : ℝ≥0∞)
    (hbase : ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
      productStandardGaussian (LayerIndex d n) (coefficientBox M))
    (hclass : ∀ xcoef : LayerIndex d n → ℝ,
      (∀ j, |xcoef j| ≤ M) →
      (c*periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
        genericPeriodicSynthesisLinear ψ xcoef ∈ MeanZeroBesovClass p r theta) :
    ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
      productStandardGaussian (LayerIndex d n)
        {xcoef | (c*periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
          genericPeriodicSynthesisLinear ψ xcoef ∈ MeanZeroBesovClass p r theta} := by
  exact hbase.trans (measure_mono
    (μ:=productStandardGaussian (LayerIndex d n))
    (scaledMeanZeroBox_subset (d:=d) (n:=n) ψ c M r theta p hclass))

/-- Every positive exponential cost is realized by the actual mean-zero
coefficient-box synthesis inside the restricted Besov class. -/
theorem meanZeroBesov_box_mass_for_every_exponent
    {d : ℕ} (hd : 2 ≤ d) (ψ : SmoothCompactBump) (b : AdmissibleBump)
    (hψ : ψ.atom = b.atom) (hmean : (∫ x in (0:ℝ)..1, b.atom x) = 0)
    (r : ℝ) (theta p : ℝ≥0∞) (hr : 0 < r)
    (htop : theta ≠ ⊤) (hθ : 2 ≤ theta.toReal) (hp : 1 ≤ p) :
    ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
        ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
          productStandardGaussian (LayerIndex d n)
            {xcoef | (a*periodicSynthesisScale d n r
              (1/2-1/theta.toReal)) • genericPeriodicSynthesisLinear ψ xcoef ∈
                MeanZeroBesovClass p r theta} := by
  intro δ hδ
  obtain ⟨M,hM,hgauss⟩ := exists_gaussian_box_for_cost hδ
  have hmassBase {n : ℕ} := coefficientBox_nativeDimension_mass
    (d:=d) (n:=n) (by omega) hδ hgauss
  obtain ⟨c,hc,hclass⟩ := exists_meanZero_scaled_box_synthesis hd ψ b hψ hmean
    M r theta p hM hr htop hθ hp
  refine ⟨c,hc,0,?_⟩
  intro n hn
  exact scaledMeanZeroBox_mass (d:=d) (n:=n) ψ c M δ r theta p
    (hmassBase (n:=n)) (hclass n)

/-- Crossing-scale covering obstruction from the actual mean-zero synthesis,
its continuum confinement event, and the finite Gaussian translated-ball cap. -/
private theorem meanZero_native_crossing_cover
    {d : ℕ} (hd : 2 ≤ d) (ψ : SmoothCompactBump) (b : AdmissibleBump)
    (hψ : ψ.atom = b.atom) (K : Set (RealPeriodic d))
    (r beta aclass aconf bconf ηconf : ℝ)
    (haclasspos : 0 < aclass) (hbconf : 0 < bconf)
    (hηconf : 0 < ηconf) (hroot2 : Real.sqrt 2 * ηconf = aconf)
    (Nclass Nconf stride k₀ : ℕ) (hstride : 1 ≤ stride) (hk₀ : 2 ≤ k₀)
    (hbudgetSlope : 2 ≤ (3*bconf/8)*(stride:ℝ))
    (hclass : ∀ n : ℕ, Nclass ≤ n →
      ENNReal.ofReal (Real.exp (-(bconf/8)*nativeDimension d n)) ≤
        productStandardGaussian (LayerIndex d n)
          {xcoef | (aclass*periodicSynthesisScale d n r beta) •
            genericPeriodicSynthesisLinear ψ xcoef ∈ K})
    (hconf : ∀ n : ℕ, Nconf ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {z | ∀ x ∈ AlignmentPaperContinuumGoodRegion.cubeSet d,
          |bumpSynthesis b z x| ≤ aconf*Real.sqrt ((n:ℝ)*hyperbolicCount d n)} ≤
          Real.exp (-bconf*nativeDimension d n))
    (hgrade : ∀ k : ℕ, k₀ ≤ k →
      max Nclass (max Nconf stride) ≤
        nativeEntropyCrossing d (2*stride*k) (by omega)) :
    ∀ (k : ℕ) (hk : k₀ ≤ k),
      ((2^(k-1):ℕ):ℕ∞) < Metric.externalCoveringNumber
        ⟨(aclass*ηconf)*periodicNativeRadius d
          (nativeEntropyCrossing d (2*stride*k) (by omega)) r beta,
          (mul_pos (mul_pos haclasspos hηconf) (periodicNativeRadius_pos
            (nativeEntropyCrossing_bracket hd
              (by nlinarith [hk, hstride] : 2≤2*stride*k)).1)).le⟩ K := by
  intro k hk
  have hk2 : 2 ≤ k := hk₀.trans hk
  have hsk : 2 ≤ 2*stride*k := by nlinarith
  let q := nativeEntropyCrossing d (2*stride*k) (by omega)
  have hbr := nativeEntropyCrossing_bracket hd hsk
  have hq : 0 < q := hbr.1
  have hqmax : max Nclass (max Nconf stride) ≤ q := hgrade k hk
  have hqclass : Nclass ≤ q := (le_max_left Nclass _).trans hqmax
  have hqconf : Nconf ≤ q :=
    (le_max_left Nconf stride).trans (le_max_right Nclass (max Nconf stride)) |>.trans hqmax
  have hqstride : stride ≤ q :=
    (le_max_right Nconf stride).trans (le_max_right Nclass (max Nconf stride)) |>.trans hqmax
  let n : ℕ := 2*q
  let D : ℝ := nativeDimension d n
  have hDk : (2*(stride:ℝ))*(k:ℝ) ≤ D := by
    have hh := hbr.2.2.1
    simpa [D,n, Nat.cast_mul] using hh
  have hDs : (stride:ℝ)*(k:ℝ) ≤ D := by nlinarith [hDk]
  let Q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(bconf/2)*D))
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(bconf/8)*D))
  have hTpos : 0<T := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hgap := CameronMartinRate.dyadic_exponential_mass_lt hk2
    (by positivity : 0 < 3*bconf/8) hDs hbudgetSlope
  have hsplit : ENNReal.ofReal (Real.exp (-(3*bconf/8)*D))*T = Q := by
    dsimp [T,Q]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have hscaledGap :
      ((2^(k-1):ℕ):ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(3*bconf/8)*D)) < (3/4:ℝ≥0∞) := by
    simpa using hgap
  have hbudget : ((2^(k-1):ℕ):ℝ≥0∞)*Q < T := by
    have hTtop : T < ⊤ := by dsimp [T]; exact ENNReal.ofReal_lt_top
    have hscaled : ((2^(k-1):ℕ):ℝ≥0∞)*Q < (3/4:ℝ≥0∞)*T := by
      calc
        _ = T * (((2^(k-1):ℕ):ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-(3*bconf/8)*D))) := by rw [← hsplit]; ac_rfl
        _ < T*(3/4:ℝ≥0∞) := ENNReal.mul_lt_mul_right hTpos.ne' hTtop.ne hscaledGap
        _ = _ := by ac_rfl
    have hthree : (3/4:ℝ≥0∞)<1 := by
      apply (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
      norm_num
    calc
      _ < (3/4:ℝ≥0∞)*T := hscaled
      _ = T*(3/4:ℝ≥0∞) := by ac_rfl
      _ < T*1 := ENNReal.mul_lt_mul_right hTpos.ne' hTtop.ne hthree
      _ = T := by simp
  let A : ℝ := aclass*periodicSynthesisScale d n r beta
  let ρ : ℝ := (aclass*ηconf)*periodicNativeRadius d q r beta
  have hA : 0<A := mul_pos haclasspos (periodicSynthesisScale_pos (by omega) r beta)
  have hρ : 0<ρ := mul_pos (mul_pos haclasspos hηconf) (periodicNativeRadius_pos hq)
  have hrad : A*(ηconf*Real.sqrt ((n:ℝ)*hyperbolicCount d n)) = ρ := by
    dsimp [A,ρ,n]
    rw [periodicSynthesisScale_mul_confinement (d:=d) (q:=q) (by omega)
      aclass ηconf r beta]
  have hconfE : productStandardGaussian (LayerIndex d n)
      {z | ∀ x ∈ AlignmentPaperContinuumGoodRegion.cubeSet d,
        |bumpSynthesis b z x| ≤ aconf*Real.sqrt ((n:ℝ)*hyperbolicCount d n)} ≤
      ENNReal.ofReal (Real.exp (-(bconf*D))) := by
    have hreal := hconf n (by omega)
    have hconvert : (productStandardGaussian (LayerIndex d n)).real
        {z | ∀ x ∈ AlignmentPaperContinuumGoodRegion.cubeSet d,
          |bumpSynthesis b z x| ≤ aconf*Real.sqrt ((n:ℝ)*hyperbolicCount d n)} =
        ((productStandardGaussian (LayerIndex d n))
        {z | ∀ x ∈ AlignmentPaperContinuumGoodRegion.cubeSet d,
          |bumpSynthesis b z x| ≤ aconf*Real.sqrt ((n:ℝ)*hyperbolicCount d n)}).toReal := rfl
    have hle := ENNReal.ofReal_le_ofReal hreal
    rw [hconvert, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hle
    simpa [D] using hle
  let ρnn : ℝ≥0 := ⟨ρ,hρ.le⟩
  have hconfCap : productStandardGaussian (LayerIndex d n)
      {z | ∀ x ∈ AlignmentPaperContinuumGoodRegion.cubeSet d,
        |bumpSynthesis b z x| ≤ Real.sqrt 2*((ρnn:ℝ)/A)} ≤
          ENNReal.ofReal (Real.exp (-(bconf*D))) := by
    have hrad' : Real.sqrt 2*((ρnn:ℝ)/A) =
        aconf*Real.sqrt ((n:ℝ)*hyperbolicCount d n) := by
      have hρA : (ρnn:ℝ)/A = ηconf*Real.sqrt ((n:ℝ)*hyperbolicCount d n) := by
        change ρ/A = _
        rw [← hrad]
        field_simp
      rw [hρA, ← mul_assoc, hroot2]
    rw [hrad']
    simpa [D] using hconfE
  have hDpos : 0 < D := by
    dsimp [D]
    unfold nativeDimension
    exact mul_pos (by positivity) (hyperbolicCount_pos (by omega))
  have hball := genericPeriodicPath_scaled_translated_ball_mass_le
    (d:=d) (n:=n) ψ b hψ hA (mul_nonneg hbconf.le hDpos.le) ρnn hconfCap
  have hballQ : ∀ f : RealPeriodic d,
      productStandardGaussian (LayerIndex d n)
        {z | edist (A • genericPeriodicPath ψ z) f ≤ (ρnn:ℝ≥0∞)} ≤ Q := by
    intro f
    have hh := hball f
    have hexp : -(bconf*D)/2 = -(bconf/2)*D := by ring
    simpa [Q, hexp] using hh
  let E : Set (LayerIndex d n → ℝ) := {z | (A • genericPeriodicPath ψ z) ∈ K}
  have hqclassn : Nclass ≤ n := by dsimp [n]; omega
  have hclassMass : T ≤ productStandardGaussian (LayerIndex d n) E := by
    change ENNReal.ofReal (Real.exp (-(bconf/8)*nativeDimension d n)) ≤
      productStandardGaussian (LayerIndex d n)
        {xcoef | (aclass*periodicSynthesisScale d n r beta) •
          genericPeriodicSynthesisLinear ψ xcoef ∈ K}
    exact hclass n hqclassn
  have hmass : ((2^(k-1):ℕ):ℝ≥0∞)*Q <
      productStandardGaussian (LayerIndex d n) E := hbudget.trans_le hclassMass
  have hcover' := BrownianSharp.externalCoveringNumber_gt_of_admissible_mass
    (productStandardGaussian (LayerIndex d n))
    (fun z => A • genericPeriodicPath ψ z) E K ρnn Q
    (2^(k-1)) (by intro z hz; exact hz) hballQ hmass
  have hradFinal : (ρnn:ℝ) =
      ((aclass*ηconf)*periodicNativeRadius d q r beta) := by
    dsimp [ρnn, ρ]
    rfl
  simpa [hradFinal,ρnn,q] using hcover'

/-- The actual coordinatewise mean-zero Besov class has the sharp power-log
entropy lower bound. The proof uses the mean-zero bump synthesis, its full
continuum confinement event, and the finite Gaussian translated-ball cap. -/
theorem meanZeroBesov_entropy_rate_of_bump
    {d : ℕ} (hd : 2 ≤ d) (ψ : SmoothCompactBump) (b : AdmissibleBump)
    (hψ : ψ.atom = b.atom) (hmean : (∫ x in (0:ℝ)..1, b.atom x) = 0)
    (r : ℝ) (theta p : ℝ≥0∞) (hrhalf : 1/2 < r)
    (htop : theta ≠ ⊤) (hθ : 2 ≤ theta.toReal) (hp : 2 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+(1/2-1/theta.toReal)*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k (MeanZeroBesovClass (d:=d) p r theta) := by
  classical
  have hr : 0 < r := by linarith
  let beta : ℝ := 1/2-1/theta.toReal
  let K : Set (RealPeriodic d) := MeanZeroBesovClass (d:=d) p r theta
  obtain ⟨aconf,bconf,haconf,hbconf,Nconf,hconf⟩ :=
    AlignmentPaperGenericBumpCertified.eventually_bumpSynthesis_confinement hd b
  have hbox := meanZeroBesov_box_mass_for_every_exponent hd ψ b hψ hmean
    r theta p (by linarith) htop hθ (by exact le_trans (by norm_num) hp)
  obtain ⟨aclass,haclasspos,Nclass,hclass⟩ := hbox (bconf/8) (by positivity)
  let stride : ℕ := max 1 ⌈16/(3*bconf)⌉₊
  have hstride : 1 ≤ stride := le_max_left _ _
  have hceil : 16/(3*bconf) ≤ (stride:ℝ) := by
    dsimp [stride]
    exact (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1 ⌈16/(3*bconf)⌉₊)
  have hbudgetSlope : 2 ≤ (3*bconf/8)*(stride:ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < 3*bconf)).1 hceil
    nlinarith
  have htwo : 1 ≤ 2*stride := by omega
  obtain ⟨k₀,hk₀,hgrade⟩ := nativeEntropyCrossing_multiple_eventually_ge hd htwo
    (max Nclass (max Nconf stride))
  let ηconf : ℝ := aconf / Real.sqrt 2
  have hηconf : 0 < ηconf := div_pos haconf (Real.sqrt_pos.2 (by norm_num))
  have hroot2 : Real.sqrt 2 * ηconf = aconf := by
    dsimp [ηconf]
    field_simp
  have hclassK : ∀ n : ℕ, Nclass ≤ n →
      ENNReal.ofReal (Real.exp (-(bconf/8)*nativeDimension d n)) ≤
        productStandardGaussian (LayerIndex d n)
          {xcoef | (aclass*periodicSynthesisScale d n r beta) •
            genericPeriodicSynthesisLinear ψ xcoef ∈ K} := by
    intro n hn
    simpa only [K] using hclass n hn
  have hcover := meanZero_native_crossing_cover hd ψ b hψ K
    r beta aclass aconf bconf ηconf haclasspos hbconf hηconf hroot2
    Nclass Nconf stride k₀ hstride hk₀ hbudgetSlope hclassK hconf hgrade
  obtain ⟨c,hc,hrate⟩ := periodic_entropy_rate_of_cover_at_multiple K hd
    htwo hk₀ r beta (aclass*ηconf) hr (mul_pos haclasspos hηconf) hcover
  refine ⟨c,hc,k₀,hk₀,?_⟩
  intro k hk
  simpa only [K, beta] using hrate k hk

/-- Unconditional endpoint for the literal coordinatewise mean-zero Besov
unit ball in the manuscript range `p, theta ≥ 2`, `theta < ∞`, `r > 1/2`.
The actual admissible normalized zero-integral bump is selected internally. -/
theorem meanZeroBesov_entropy_rate
    {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (theta p : ℝ≥0∞)
    (hrhalf : 1/2 < r) (hthetaTop : theta ≠ ⊤)
    (hθ : 2 ≤ theta.toReal) (hp : 2 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+(1/2-1/theta.toReal)*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k
            (MeanZeroBesovClass (d:=d) p r theta) := by
  have hθ' : 1 ≤ theta :=
    (ENNReal.toReal_le_toReal ENNReal.one_ne_top hthetaTop).1 (by norm_num; linarith)
  obtain ⟨b,ψ,hψ,hmean,_hnonzero,_hbound,_c,_hc,_hsynth⟩ :=
    exists_meanZero_generic_smooth_bump_endpoint hd 1 r theta
      (by norm_num) (by linarith) hθ'
  have hmeanb : (∫ x in (0:ℝ)..1, b.atom x) = 0 := by
    simpa [hψ] using hmean
  exact meanZeroBesov_entropy_rate_of_bump hd ψ b hψ hmeanb r theta p
    hrhalf hthetaTop hθ hp

private theorem entropyNumber_mono_set {X : Type*} [PseudoEMetricSpace X]
    {K J : Set X} (hK : K ⊆ J) (k : ℕ) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ HaarQuarter.TheoremD.entropyNumber k J := by
  unfold HaarQuarter.TheoremD.entropyNumber
  apply le_sInf
  rintro q ⟨ρ,rfl,hcover⟩
  exact sInf_le ⟨ρ,rfl,(Metric.externalCoveringNumber_mono_set hK).trans hcover⟩

/-- The restricted class lower rate in its manuscript ambient space
`L∞(T^d)`. The only loss is the universal factor two for external centers. -/
theorem meanZeroBesov_entropy_lower_LInfinity
    {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (theta p : ℝ≥0∞)
    (hrhalf : 1/2 < r) (htop : theta ≠ ⊤)
    (hθ : 2 ≤ theta.toReal) (hp : 2 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*BrownianSharp.logarithmicIndexRate r
        ((r+1/2-1/theta.toReal)*(d-1:ℕ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (Latest.periodicLInfinityImage
            (MeanZeroBesovClass (d:=d) p r theta)) := by
  obtain ⟨c,hc,k₀,hk₀,hLower⟩ :=
    meanZeroBesov_entropy_rate hd r theta p hrhalf htop hθ hp
  refine ⟨c/2,by positivity,k₀,hk₀,?_⟩
  intro k hk
  let alpha : ℝ := (r+1/2-1/theta.toReal)*(d-1:ℕ)+1/2
  have hrate : BrownianSharp.logarithmicIndexRate r alpha k =
      (k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+(1/2-1/theta.toReal)*((d-1:ℕ):ℝ))) := by
    unfold BrownianSharp.logarithmicIndexRate
    have he : alpha =
        r*((d-1:ℕ):ℝ)+(1/2+(1/2-1/theta.toReal)*((d-1:ℕ):ℝ)) := by
      dsimp [alpha]
      push_cast
      ring
    rw [he]
  have hu : ENNReal.ofReal (c*BrownianSharp.logarithmicIndexRate r alpha k) ≤
      HaarQuarter.TheoremD.entropyNumber k
        (MeanZeroBesovClass (d:=d) p r theta) := by
    rw [hrate]
    simpa [mul_assoc] using hLower k hk
  have hLInf := AlignmentLatestPeriodicEntropy.periodic_entropy_lower_to_LInfinity
    (MeanZeroBesovClass (d:=d) p r theta) k
    (c*BrownianSharp.logarithmicIndexRate r alpha k) hu
  simpa [alpha, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hLInf

/-- Two-sided entropy asymptotics for the literal coordinatewise mean-zero
Besov class in the manuscript's `L∞` ambient space. The lower endpoint uses
mean-zero synthesis; the upper bound follows by inclusion in the full Besov ball. -/
theorem meanZeroBesov_entropy_two_sided_LInfinity
    {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (theta p : ℝ≥0∞)
    (hrhalf : 1/2 < r) (htop : theta ≠ ⊤)
    (hθ : 2 ≤ theta.toReal) (hp : 2 ≤ p) :
    AlignmentPaperPeriodic.twoSidedEntropyRate
      (Latest.periodicLInfinityImage (MeanZeroBesovClass (d:=d) p r theta))
      r ((r+1/2-1/theta.toReal)*(d-1:ℕ)+1/2) := by
  let alpha : ℝ := (r+1/2-1/theta.toReal)*(d-1:ℕ)+1/2
  obtain ⟨cLower,hcLower,kLower,hkLower,hLower⟩ :=
    meanZeroBesov_entropy_lower_LInfinity hd r theta p hrhalf htop hθ hp
  have hθenn : 2 ≤ theta :=
    (ENNReal.toReal_le_toReal (by norm_num : (2:ℝ≥0∞) ≠ ⊤) htop).1 hθ
  obtain ⟨⟨cFull,cUpper,hcFull,hcUpper,kFull,hkFull,hFull⟩,_hwidth⟩ :=
    AlignmentPaperPeriodicComplete.periodicBesov_entropy_width_equivalent
      AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff hd hp hrhalf hθenn
  let Kinf := Latest.periodicLInfinityImage
    (MeanZeroBesovClass (d:=d) p r theta)
  let Jinf := Latest.periodicLInfinityImage
    {f : RealPeriodic d | SmoothResolution.BesovUnitBall p r theta f}
  have hsub : Kinf ⊆ Jinf := by
    rintro g ⟨f,hf,rfl⟩
    exact ⟨f,hf.1,rfl⟩
  have hJfull : Jinf = Latest.periodicLInfinityImage
      {f : RealPeriodic d |
        AlignmentPeriodicCutoffClasses.BesovUnitBall
          AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff p r theta f} := by
    ext g
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact ⟨f,(AlignmentPeriodicCutoffClasses.BesovUnitBall_fixed p r theta f).2 hf,rfl⟩
    · rintro ⟨f,hf,rfl⟩
      exact ⟨f,(AlignmentPeriodicCutoffClasses.BesovUnitBall_fixed p r theta f).1 hf,rfl⟩
  have hrateNonneg : ∀ k : ℕ,
      0 ≤ BrownianSharp.logarithmicIndexRate r alpha k :=
    fun k => AlignmentWidthRates.logarithmicIndexRate_nonneg r alpha k
  refine ⟨min cLower cFull,cUpper,lt_min hcLower hcFull,hcUpper,
    max kLower kFull,hkLower.trans (le_max_left _ _),?_⟩
  intro k hk
  have hkl : kLower ≤ k := (le_max_left kLower kFull).trans hk
  have hkf : kFull ≤ k := (le_max_right kLower kFull).trans hk
  have hlow := hLower k hkl
  have hlow' : ENNReal.ofReal
      (cLower*BrownianSharp.logarithmicIndexRate r alpha k) ≤
      HaarQuarter.TheoremD.entropyNumber k Kinf := by simpa [Kinf,alpha] using hlow
  have hlowFinal := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (min_le_left cLower cFull) (hrateNonneg k))).trans hlow'
  have hup := (entropyNumber_mono_set hsub k).trans
    (by simpa [Jinf,hJfull] using (hFull k hkf).2)
  exact ⟨hlowFinal, by simpa [Kinf] using hup⟩

end BrownianSharp.AlignmentPaperMeanZeroBesovEntropy
