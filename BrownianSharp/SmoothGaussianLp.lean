import BrownianSharp.AtomicBlockVariance
import BrownianSharp.GaussianRowLp
import Mathlib.Analysis.MeanInequalitiesPow

/-! Absolute moments of the actual complex smooth-block Gaussian synthesis.
The factor two comes only from splitting a complex Gaussian row into its real
and imaginary parts. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance instSmoothGaussianLpCircleVolume :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover

private theorem complex_norm_le_abs_parts (z : ℂ) :
    ‖z‖ ≤ |z.re| + |z.im| := by
  have hn : 0 ≤ ‖z‖ := norm_nonneg _
  have hab : 0 ≤ |z.re| + |z.im| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hs : ‖z‖ ^ 2 ≤ (|z.re| + |z.im|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hr : z.re ^ 2 = |z.re| ^ 2 := by rw [sq_abs]
    have hi : z.im ^ 2 = |z.im| ^ 2 := by rw [sq_abs]
    nlinarith [hr, hi, mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)]
  nlinarith [sq_nonneg (‖z‖ - (|z.re| + |z.im|))]

private theorem real_rpow_two_sum_bound {a b p : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) := by
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow (⟨a, ha⟩) (⟨b, hb⟩) hp
  exact_mod_cast h

/-- For a finite standard-Gaussian synthesis, the actual complex Fourier block
has an arbitrary real p moment bounded by the corresponding Gaussian
absolute moment times the full coefficient energy. This is the scalar input
for Tonelli estimates of the literal smooth-resolution class energies. -/
theorem smoothBlock_gaussian_absRpow_data {ι d : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    (x : UnitAddTorus (Fin d)) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z : Fin ι → ℝ =>
        ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p)
        (productStandardGaussian (Fin ι)) ∧
      (∫ z : Fin ι → ℝ,
        ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p
          ∂productStandardGaussian (Fin ι)) ≤
        2 ^ p * (∑ i : Fin ι,
          ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ^ (p / 2) *
          gaussianAbsoluteMoment p := by
  classical
  let G : Fin ι → (Fin ι → ℝ) → ℝ := fun i z => z i
  let P : Measure (Fin ι → ℝ) := productStandardGaussian (Fin ι)
  let c : Fin ι → ℝ := fun i => (SmoothResolution.block s (atoms i) x).re
  let e : Fin ι → ℝ := fun i => (SmoothResolution.block s (atoms i) x).im
  let X : (Fin ι → ℝ) → ℝ := GaussianRows.row G c
  let Y : (Fin ι → ℝ) → ℝ := GaussianRows.row G e
  let V : ℝ := ∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2
  have hG : ∀ i, Measurable (G i) := fun i => measurable_pi_apply i
  have hLaw : ∀ i, P.map (G i) = gaussianReal 0 1 := by
    intro i
    dsimp [P, G, productStandardGaussian]
    exact productStandardGaussian_coordinate_law i
  have hIndep : iIndepFun G P := by
    dsimp [P, G, productStandardGaussian]
    exact productStandardGaussian_coordinates_independent (Fin ι)
  have hRe : ∀ z, (SmoothResolution.block s (gaussianSynthesis atoms z) x).re = X z := by
    intro z
    rw [AtomicBlockVariance.smoothBlock_gaussianSynthesis]
    simp [X, G, c, GaussianRows.row, Complex.mul_re]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hIm : ∀ z, (SmoothResolution.block s (gaussianSynthesis atoms z) x).im = Y z := by
    intro z
    rw [AtomicBlockVariance.smoothBlock_gaussianSynthesis]
    simp [Y, G, e, GaussianRows.row, Complex.mul_im]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpoint : ∀ z, ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p ≤
      2 ^ (p - 1) * (|X z| ^ p + |Y z| ^ p) := by
    intro z
    have hnorm := complex_norm_le_abs_parts
      (SmoothResolution.block s (gaussianSynthesis atoms z) x)
    have hpow := Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith : 0 ≤ p)
    have hparts := real_rpow_two_sum_bound
      (abs_nonneg ((SmoothResolution.block s (gaussianSynthesis atoms z) x).re))
      (abs_nonneg ((SmoothResolution.block s (gaussianSynthesis atoms z) x).im)) hp
    calc
      ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p ≤
          (|(SmoothResolution.block s (gaussianSynthesis atoms z) x).re| +
            |(SmoothResolution.block s (gaussianSynthesis atoms z) x).im|) ^ p :=
        hpow
      _ ≤ 2 ^ (p - 1) *
          (|(SmoothResolution.block s (gaussianSynthesis atoms z) x).re| ^ p +
            |(SmoothResolution.block s (gaussianSynthesis atoms z) x).im| ^ p) :=
        hparts
      _ = 2 ^ (p - 1) * (|X z| ^ p + |Y z| ^ p) := by rw [hRe z, hIm z]
  have hcvar : ∑ i, c i ^ 2 ≤ V := by
    dsimp [c, V]
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg ((SmoothResolution.block s (atoms i) x).im)]
  have hevar : ∑ i, e i ^ 2 ≤ V := by
    dsimp [e, V]
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg ((SmoothResolution.block s (atoms i) x).re)]
  have hV : 0 ≤ V := by
    dsimp [V]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC : 0 ≤ gaussianAbsoluteMoment p := by
    unfold gaussianAbsoluteMoment
    exact integral_nonneg fun _ => by positivity
  have hp0 : 0 < p := by linarith
  have hXm := gaussianRow_absRpow_integral G hG hLaw hIndep c hp0
  have hYm := gaussianRow_absRpow_integral G hG hLaw hIndep e hp0
  have hXle : (Real.sqrt (∑ i, c i ^ 2)) ^ p ≤ (Real.sqrt V) ^ p := by
    apply Real.rpow_le_rpow
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_le_sqrt hcvar
    · linarith
  have hYle : (Real.sqrt (∑ i, e i ^ 2)) ^ p ≤ (Real.sqrt V) ^ p := by
    apply Real.rpow_le_rpow
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_le_sqrt hevar
    · linarith
  have hXmoment : (∫ z, |X z| ^ p ∂P) ≤ (Real.sqrt V) ^ p * gaussianAbsoluteMoment p := by
    change (∫ z, |GaussianRows.row G c z| ^ p ∂P) ≤ _
    rw [hXm]
    exact mul_le_mul_of_nonneg_right hXle hC
  have hYmoment : (∫ z, |Y z| ^ p ∂P) ≤ (Real.sqrt V) ^ p * gaussianAbsoluteMoment p := by
    change (∫ z, |GaussianRows.row G e z| ^ p ∂P) ≤ _
    rw [hYm]
    exact mul_le_mul_of_nonneg_right hYle hC
  have hXint : Integrable (fun z => |X z| ^ p) P :=
    gaussianRow_absRpow_integrable G hG hLaw hIndep c hp0
  have hYint : Integrable (fun z => |Y z| ^ p) P :=
    gaussianRow_absRpow_integrable G hG hLaw hIndep e hp0
  have hdom : Integrable
      (fun z => 2 ^ (p - 1) * (|X z| ^ p + |Y z| ^ p)) P :=
    (hXint.add hYint).const_mul (2 ^ (p - 1))
  have hleftMeas : AEStronglyMeasurable
      (fun z => ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p) P := by
    have hp0le : 0 ≤ p := by linarith
    have hrowmX : Measurable X := by
      dsimp [X]
      unfold GaussianRows.row
      exact Finset.measurable_fun_sum _ (fun i hi =>
        measurable_const.mul (measurable_pi_apply i))
    have hrowmY : Measurable Y := by
      dsimp [Y]
      unfold GaussianRows.row
      exact Finset.measurable_fun_sum _ (fun i hi =>
        measurable_const.mul (measurable_pi_apply i))
    have hcomplex : (fun z => SmoothResolution.block s
        (gaussianSynthesis atoms z) x) =
        (fun z => (X z : ℂ) + (Y z : ℂ) * Complex.I) := by
      funext z
      apply Complex.ext
      · simp [hRe z, hIm z]
      · simp [hRe z, hIm z]
    have hm : Measurable (fun z =>
        ‖(X z : ℂ) + (Y z : ℂ) * Complex.I‖ ^ p) := by
      fun_prop (disch := assumption)
    exact hm.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun z =>
        congrArg (fun w : ℂ => ‖w‖ ^ p) (congrFun hcomplex z).symm)
  have hInt : Integrable (fun z => ‖SmoothResolution.block s
      (gaussianSynthesis atoms z) x‖ ^ p) P := by
    apply hdom.mono' hleftMeas
    filter_upwards with z
    change |‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p| ≤ _
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hpoint z
  have hIntegral :
      (∫ z, ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p ∂P) ≤
        2 ^ (p - 1) *
          ((∫ z, |X z| ^ p ∂P) + ∫ z, |Y z| ^ p ∂P) := by
    calc
      _ ≤ ∫ z, 2 ^ (p - 1) * (|X z| ^ p + |Y z| ^ p) ∂P :=
        integral_mono hInt hdom (fun z => hpoint z)
      _ = _ := by rw [integral_const_mul, integral_add hXint hYint]
  dsimp [P] at *
  refine ⟨hInt, ?_⟩
  calc
    (∫ z, ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p
        ∂productStandardGaussian (Fin ι))
      ≤ 2 ^ (p - 1) *
          ((∫ z, |X z| ^ p ∂productStandardGaussian (Fin ι)) +
           ∫ z, |Y z| ^ p ∂productStandardGaussian (Fin ι)) := by
        exact hIntegral
    _ ≤ 2 ^ (p - 1) *
          ((Real.sqrt V) ^ p * gaussianAbsoluteMoment p +
           (Real.sqrt V) ^ p * gaussianAbsoluteMoment p) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hXmoment hYmoment)
        positivity
    _ = 2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p := by
      have htwo : (2 : ℝ) ^ (p - 1) * 2 = 2 ^ p := by
        calc
          (2 : ℝ) ^ (p - 1) * 2 = 2 ^ ((p - 1) + 1) :=
            (Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0) (p - 1)).symm
          _ = 2 ^ p := by congr 1 <;> ring
      calc
        _ = ((2 : ℝ) ^ (p - 1) * 2) * (Real.sqrt V) ^ p *
              gaussianAbsoluteMoment p := by ring
        _ = 2 ^ p * (Real.sqrt V) ^ p * gaussianAbsoluteMoment p := by rw [htwo]
        _ = 2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p := by
          rw [Real.rpow_div_two_eq_sqrt p hV]

/-- Integrability component of the actual block moment calculation. -/
theorem smoothBlock_gaussian_absRpow_integrable {ι d : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    (x : UnitAddTorus (Fin d)) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z : Fin ι → ℝ =>
      ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p)
      (productStandardGaussian (Fin ι)) :=
  (smoothBlock_gaussian_absRpow_data s atoms x hp).1

/-- Absolute pth moment bound for the actual complex smooth Fourier block of
the finite standard-Gaussian synthesis. -/
theorem smoothBlock_gaussian_absRpow_bound {ι d : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    (x : UnitAddTorus (Fin d)) {p : ℝ} (hp : 1 ≤ p) :
    (∫ z : Fin ι → ℝ,
      ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p
        ∂productStandardGaussian (Fin ι)) ≤
      2 ^ p * (∑ i : Fin ι,
        ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ^ (p / 2) *
        gaussianAbsoluteMoment p :=
  (smoothBlock_gaussian_absRpow_data s atoms x hp).2

/-- Tonelli turns the pointwise Gaussian moment estimate into an expected
spatial p-energy bound. The only geometric input is a uniform deterministic
bound on the actual block coefficient variance. -/
theorem smoothBlock_gaussian_spatialEnergy_le {ι d : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    {p V : ℝ} (hp : 1 ≤ p) (hV : 0 ≤ V)
    (hvariance : ∀ x : UnitAddTorus (Fin d),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V) :
    (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
      ENNReal.ofReal (‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ p)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
        ∂productStandardGaussian (Fin ι)) ≤
      ENNReal.ofReal
        (2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p) := by
  classical
  let P := productStandardGaussian (Fin ι)
  let μx := (volume : Measure (UnitAddTorus (Fin d)))
  letI : IsProbabilityMeasure μx := by infer_instance
  let F : ((Fin ι → ℝ) × UnitAddTorus (Fin d)) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal
      (‖SmoothResolution.block s (gaussianSynthesis atoms y.1) y.2‖ ^ p)
  have hblock :
      (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
        SmoothResolution.block s (gaussianSynthesis atoms y.1) y.2) =
      (fun y => ∑ i : Fin ι, (y.1 i : ℂ) *
        SmoothResolution.block s (atoms i) y.2) := by
    funext y
    exact AtomicBlockVariance.smoothBlock_gaussianSynthesis s atoms y.1 y.2
  have hF : Measurable F := by
    have hFsum : F = (fun y => ENNReal.ofReal
        (‖∑ i : Fin ι, (y.1 i : ℂ) *
          SmoothResolution.block s (atoms i) y.2‖ ^ p)) := by
      funext y
      dsimp [F]
      rw [congrFun hblock y]
    rw [hFsum]
    fun_prop (disch := linarith)
  have hC : 0 ≤ gaussianAbsoluteMoment p := by
    unfold gaussianAbsoluteMoment
    exact integral_nonneg fun _ => by positivity
  have hinner (x : UnitAddTorus (Fin d)) :
      (∫⁻ z : Fin ι → ℝ,
        ENNReal.ofReal (‖SmoothResolution.block s
          (gaussianSynthesis atoms z) x‖ ^ p) ∂P) ≤
        ENNReal.ofReal (2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p) := by
    have hI := smoothBlock_gaussian_absRpow_integrable s atoms x hp
    have hnonneg : 0 ≤ᵐ[P]
        (fun z : Fin ι → ℝ => ‖SmoothResolution.block s
          (gaussianSynthesis atoms z) x‖ ^ p) :=
      Filter.Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg _) _
    rw [← ofReal_integral_eq_lintegral_ofReal hI hnonneg]
    apply ENNReal.ofReal_le_ofReal
    have hb := smoothBlock_gaussian_absRpow_bound s atoms x hp
    have hpow : (∑ i : Fin ι,
        ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ^ (p / 2) ≤ V ^ (p / 2) := by
      apply Real.rpow_le_rpow
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      · exact hvariance x
      · linarith
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) hC)
  have horder :
      (∫⁻ x : UnitAddTorus (Fin d), ∫⁻ z : Fin ι → ℝ,
        F (z, x) ∂P ∂μx) ≤
        ENNReal.ofReal (2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p) := by
    calc
      _ ≤ ∫⁻ x : UnitAddTorus (Fin d),
          ENNReal.ofReal (2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p) ∂μx :=
        lintegral_mono fun x => by
          simpa [F, P] using hinner x
      _ = ENNReal.ofReal (2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p) := by
        rw [lintegral_const]
        have hprob : μx Set.univ = 1 := by
          simp [μx]
        rw [hprob]
        simp
  have hfirst := MeasureTheory.lintegral_prod (μ := P) (ν := μx) F hF.aemeasurable
  have hsecond := MeasureTheory.lintegral_prod (μ := μx) (ν := P) (fun y => F y.swap)
    (hF.comp measurable_swap).aemeasurable
  have hswap := MeasureTheory.lintegral_prod_swap
    (μ := P) (ν := μx) F
  have hiter :
      (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
        F (z, x) ∂μx ∂P) =
      (∫⁻ x : UnitAddTorus (Fin d), ∫⁻ z : Fin ι → ℝ,
        F (z, x) ∂P ∂μx) := by
    calc
      _ = ∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), F y ∂P.prod μx :=
        hfirst.symm
      _ = ∫⁻ y : UnitAddTorus (Fin d) × (Fin ι → ℝ), F y.swap ∂μx.prod P :=
        hswap.symm
      _ = _ := hsecond
  calc
    _ = ∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
        F (z, x) ∂μx ∂P := by simp [F, P, μx]
    _ = ∫⁻ x : UnitAddTorus (Fin d), ∫⁻ z : Fin ι → ℝ,
        F (z, x) ∂P ∂μx := hiter
    _ ≤ _ := horder

end BrownianSharp
