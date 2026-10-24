import BrownianSharp.SmoothGaussianLp
import BrownianSharp.SmoothClassMeasurability
import BrownianSharp.SmoothClassEvents
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Finite-theta Besov expected energy for arbitrary finite exponents `p,theta
>= 1`. The proof uses the larger exponent `q=max(p,theta)` for a Gaussian
block moment, and probability-space Lp monotonicity or Holder-Jensen to move
between the spatial and scale-summation exponents. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
local instance instSmoothBesovGeneralMeasureSpace : MeasureSpace UnitAddCircle :=
  AddCircle.measureSpace 1
local instance instSmoothBesovCircleVolume :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover
open BrownianSharp.SmoothResolution

theorem lintegral_rpow_le_rpow_lintegral_of_probability
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ^ a ∂μ) ≤ (∫⁻ x, f x ∂μ) ^ a := by
  let q₁ : ℝ := a⁻¹
  let q₂ : ℝ := (1 - a)⁻¹
  have hconj : q₁.HolderConjugate q₂ := by
    dsimp [q₁, q₂]
    exact Real.HolderConjugate.inv_inv ha0 (by linarith) (by ring)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (f := fun x : α => f x ^ a) (g := fun _ : α => (1 : ℝ≥0∞))
    (hf.pow_const a) measurable_const.aemeasurable
  have hpow (x : α) : (f x ^ a) ^ q₁ = f x := by
    rw [← ENNReal.rpow_mul]
    rw [show a * q₁ = 1 by simp [q₁, mul_inv_cancel₀ ha0.ne'], ENNReal.rpow_one]
  have hone : (∫⁻ x : α, (1 : ℝ≥0∞) ^ q₂ ∂μ) = 1 := by simp [q₂]
  simpa [Pi.mul_apply, hpow, hone, q₁, q₂, measure_univ] using h

private theorem smoothBlock_eLpNorm_rpow_eq_spatial {d ι : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    (p : ℝ) (hp : 1 ≤ p) (z : Fin ι → ℝ) :
    (eLpNorm (fun x => SmoothResolution.block s
      (gaussianSynthesis atoms z) x) (ENNReal.ofReal p)
      (volume : Measure (UnitAddTorus (Fin d)))) ^ p =
      ∫⁻ x : UnitAddTorus (Fin d),
        ENNReal.ofReal (‖SmoothResolution.block s
          (gaussianSynthesis atoms z) x‖ ^ p)
        ∂(volume : Measure (UnitAddTorus (Fin d))) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    ((ENNReal.ofReal_pos.mpr hp_pos).ne') (by simp)
    (SmoothResolution.block s (gaussianSynthesis atoms z)).continuous.aestronglyMeasurable]
  rw [ENNReal.toReal_ofReal hp0]
  simp_rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0]
  rw [← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ hp_pos.ne', ENNReal.rpow_one]

/-- Expected literal finite-theta Besov energy for a finite Gaussian synthesis
with arbitrary finite exponents `p,theta >= 1`. The only geometric input is
the uniform deterministic variance of each actual smooth block. The remaining
summability hypothesis is explicit and uses the Gaussian moment at
`q=max(p,theta)`. -/
theorem smoothBesov_general_expected_energy_le {d ι : ℕ}
    (p theta r : ℝ) (hp : 1 ≤ p) (htheta : 1 ≤ theta)
    (atoms : Fin ι → RealPeriodic d) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    {M : ℝ≥0∞}
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal (((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ theta) *
        (ENNReal.ofReal (2 ^ max p theta * V s ^ (max p theta / 2) *
          gaussianAbsoluteMoment (max p theta)) ^ (theta / max p theta))) ≤ M) :
    (∫⁻ z : Fin ι → ℝ,
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
        (gaussianSynthesis atoms z) ∂productStandardGaussian (Fin ι)) ≤ M := by
  classical
  let μx := (volume : Measure (UnitAddTorus (Fin d)))
  letI : IsProbabilityMeasure μx := by dsimp [μx]; infer_instance
  let P := productStandardGaussian (Fin ι)
  let q : ℝ := max p theta
  let N : (Fin d → ℕ) → (Fin ι → ℝ) → ℝ≥0∞ := fun s z =>
    eLpNorm (fun x => SmoothResolution.block s
      (gaussianSynthesis atoms z) x) (ENNReal.ofReal p) μx
  let w : (Fin d → ℕ) → ℝ := fun s =>
    (2 : ℝ) ^ (r * ∑ i, (s i : ℝ))
  let T : (Fin d → ℕ) → (Fin ι → ℝ) → ℝ≥0∞ := fun s z =>
    (ENNReal.ofReal (w s) * N s z) ^ theta
  let F : (Fin ι → ℝ) → ℝ≥0∞ := fun z => ∑' s : Fin d → ℕ, T s z
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpPos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have htheta0 : 0 ≤ theta := le_trans (by norm_num) htheta
  have hq : q = max p theta := rfl
  have hq1 : 1 ≤ q := le_max_of_le_left hp
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq1
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hNmeas (s : Fin d → ℕ) : Measurable (N s) := by
    have hpenn0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hpPos).ne'
    have hpennTop : ENNReal.ofReal p ≠ ∞ := by simp
    simpa [N, μx] using smoothBlock_eLpNorm_gaussian_measurable s atoms
      (ENNReal.ofReal p) hpenn0 hpennTop
  have hTmeas (s : Fin d → ℕ) : Measurable (T s) := by
    dsimp [T]
    exact (measurable_const.mul (hNmeas s)).pow_const theta
  have hFmeas : Measurable F := Measurable.tsum hTmeas
  have hF_eq (z : Fin ι → ℝ) :
      F z = smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
        (gaussianSynthesis atoms z) := by
    simp [F, T, N, w, smoothBesovEnergy, SmoothResolution.weightedBlockNorm,
      μx, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal htheta0]
  have hseries : (∫⁻ z : Fin ι → ℝ, F z ∂P) =
      ∑' s : Fin d → ℕ, ∫⁻ z : Fin ι → ℝ, T s z ∂P :=
    MeasureTheory.lintegral_tsum (μ := P)
      (fun s => (hTmeas s).aemeasurable)
  have hterm (s : Fin d → ℕ) :
      (∫⁻ z : Fin ι → ℝ, T s z ∂P) ≤
        ENNReal.ofReal ((w s) ^ theta) *
          (ENNReal.ofReal (2 ^ q * V s ^ (q / 2) * gaussianAbsoluteMoment q) ^
            (theta / q)) := by
    have hw : 0 ≤ w s := by dsimp [w]; positivity
    have hweight : ∀ z, T s z =
        ENNReal.ofReal ((w s) ^ theta) * (N s z) ^ theta := by
      intro z
      dsimp [T]
      rw [ENNReal.mul_rpow_of_nonneg _ _ htheta0,
        ENNReal.ofReal_rpow_of_nonneg hw htheta0]
    have hmoment :
        (∫⁻ z : Fin ι → ℝ, (N s z) ^ theta ∂P) ≤
          ENNReal.ofReal (2 ^ q * V s ^ (q / 2) * gaussianAbsoluteMoment q) ^
            (theta / q) := by
      by_cases hpt : p ≤ theta
      · have hqtheta : q = theta := max_eq_right hpt
        have hmomentq := smoothBlock_gaussian_spatialEnergy_le s atoms
          (p := theta) (V := V s) htheta (hV s) (hvariance s)
        have hNle (z : Fin ι → ℝ) :
            N s z ≤ eLpNorm (fun x => SmoothResolution.block s
              (gaussianSynthesis atoms z) x) (ENNReal.ofReal theta) μx := by
          exact eLpNorm_le_eLpNorm_of_exponent_le
            (ENNReal.ofReal_le_ofReal hpt)
        have hpoint (z : Fin ι → ℝ) :
            (N s z) ^ theta ≤
              (eLpNorm (fun x => SmoothResolution.block s
                (gaussianSynthesis atoms z) x) (ENNReal.ofReal theta) μx) ^ theta :=
          ENNReal.rpow_le_rpow (hNle z) (by positivity)
        calc
          _ ≤ ∫⁻ z : Fin ι → ℝ,
              (eLpNorm (fun x => SmoothResolution.block s
                (gaussianSynthesis atoms z) x) (ENNReal.ofReal theta) μx) ^ theta ∂P :=
              lintegral_mono hpoint
          _ = ∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
                ENNReal.ofReal (‖SmoothResolution.block s
                  (gaussianSynthesis atoms z) x‖ ^ theta) ∂μx ∂P := by
              apply lintegral_congr
              intro z
              exact smoothBlock_eLpNorm_rpow_eq_spatial s atoms theta htheta z
          _ ≤ ENNReal.ofReal (2 ^ q * V s ^ (q / 2) * gaussianAbsoluteMoment q) ^
                (theta / q) := by
              rw [hqtheta]
              have hthetaPos : 0 < theta := lt_of_lt_of_le zero_lt_one htheta
              have hdiv : theta / theta = 1 := div_self hthetaPos.ne'
              simpa [μx, P, hdiv, ENNReal.rpow_one] using hmomentq
      · have hθp : theta < p := lt_of_not_ge hpt
        have hqP : q = p := max_eq_left (le_of_lt hθp)
        have hmomentp := smoothBlock_gaussian_spatialEnergy_le s atoms
          (p := p) (V := V s) hp (hV s) (hvariance s)
        have hnormMeas : AEMeasurable (N s) P := (hNmeas s).aemeasurable
        have ha : 0 < theta / p := by positivity
        have ha1 : theta / p < 1 := (div_lt_one hpPos).2 hθp
        have hNpmeas : AEMeasurable (fun z => (N s z) ^ p) P :=
          hnormMeas.pow_const p
        have hNp : (∫⁻ z : Fin ι → ℝ, (N s z) ^ p ∂P) ≤
            ENNReal.ofReal (2 ^ p * V s ^ (p / 2) * gaussianAbsoluteMoment p) := by
          calc
            _ = ∫⁻ z : Fin ι → ℝ,
                ∫⁻ x : UnitAddTorus (Fin d),
                  ENNReal.ofReal (‖SmoothResolution.block s
                    (gaussianSynthesis atoms z) x‖ ^ p) ∂μx ∂P := by
                apply lintegral_congr
                intro z
                exact smoothBlock_eLpNorm_rpow_eq_spatial s atoms p hp z
            _ ≤ _ := by simpa [μx, P] using hmomentp
        calc
          _ ≤ (∫⁻ z : Fin ι → ℝ, (N s z) ^ p ∂P) ^ (theta / p) := by
            have hJ := lintegral_rpow_le_rpow_lintegral_of_probability
              (fun z => (N s z) ^ p) ha ha1 hNpmeas
            have hpow (z : Fin ι → ℝ) : ((N s z) ^ p) ^ (theta / p) =
                (N s z) ^ theta := by
              rw [← ENNReal.rpow_mul]
              congr 1
              field_simp
            simpa only [hpow] using hJ
          _ ≤ ENNReal.ofReal (2 ^ p * V s ^ (p / 2) * gaussianAbsoluteMoment p) ^
                (theta / p) := ENNReal.rpow_le_rpow hNp (by positivity)
          _ = ENNReal.ofReal (2 ^ q * V s ^ (q / 2) * gaussianAbsoluteMoment q) ^
                (theta / q) := by rw [hqP]
    have hterm_eq : (fun z : Fin ι → ℝ => T s z) =
        (fun z => ENNReal.ofReal ((w s) ^ theta) * (N s z) ^ theta) := by
      funext z
      exact hweight z
    rw [hterm_eq, MeasureTheory.lintegral_const_mul''
      (ENNReal.ofReal ((w s) ^ theta)) ((hNmeas s).aemeasurable.pow_const theta)]
    exact mul_le_mul_of_nonneg_left hmoment (by positivity)
  have hsum :
      (∑' s : Fin d → ℕ, ∫⁻ z : Fin ι → ℝ, T s z ∂P) ≤ M :=
    (ENNReal.tsum_le_tsum hterm).trans hsummable
  calc
    (∫⁻ z : Fin ι → ℝ,
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
        (gaussianSynthesis atoms z) ∂productStandardGaussian (Fin ι))
        = ∫⁻ z : Fin ι → ℝ, F z ∂P := by simp [P, hF_eq]
    _ = ∑' s : Fin d → ℕ, ∫⁻ z : Fin ι → ℝ, T s z ∂P := hseries
    _ ≤ M := hsum

/-- Half-mass for the literal finite-theta Besov unit ball, for arbitrary
finite exponents `p,theta ≥ 1`. This is the mean-to-class bridge for the
actual finite Gaussian synthesis; its quantitative input is the explicit
variance-envelope summability bound from
`smoothBesov_general_expected_energy_le`. -/
theorem smoothBesov_general_unitBall_mass {d ι : ℕ}
    (p theta r : ℝ) (hp : 1 ≤ p) (htheta : 1 ≤ theta)
    (atoms : Fin ι → RealPeriodic d) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal (((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ theta) *
        (ENNReal.ofReal (2 ^ max p theta * V s ^ (max p theta / 2) *
          gaussianAbsoluteMoment (max p theta)) ^ (theta / max p theta))) ≤ 1 / 2) :
    (1 / 2 : ℝ≥0∞) ≤ (productStandardGaussian (Fin ι))
      {z | SmoothResolution.BesovUnitBall (ENNReal.ofReal p) r
        (ENNReal.ofReal theta) (gaussianSynthesis atoms z)} := by
  have hmean : (∫⁻ z : Fin ι → ℝ,
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
        (gaussianSynthesis atoms z) ∂productStandardGaussian (Fin ι)) ≤ 1 / 2 :=
    smoothBesov_general_expected_energy_le p theta r hp htheta atoms V hV
      hvariance hsummable
  have hmeas : Measurable (fun z : Fin ι → ℝ =>
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
        (gaussianSynthesis atoms z)) := by
    have hpenn0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le zero_lt_one hp)).ne'
    exact smoothBesovEnergy_gaussian_measurable atoms (ENNReal.ofReal p)
      hpenn0
      (by simp) r (ENNReal.ofReal theta)
  have hthetaNe : ENNReal.ofReal theta ≠ ∞ := by simp
  exact smoothBesovUnitBall_mass_of_mean_le_half
    (productStandardGaussian (Fin ι)) (ENNReal.ofReal p) r
    (θ := ENNReal.ofReal theta) hthetaNe (fun z => gaussianSynthesis atoms z)
    hmeas hmean

end BrownianSharp
