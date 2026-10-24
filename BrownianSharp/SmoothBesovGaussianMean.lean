import BrownianSharp.SmoothGaussianLp
import BrownianSharp.SmoothClassEvents

/-! Expected actual Besov energy for the diagonal finite-exponent case
`theta = p`. Here the power of each weighted block norm is exactly its spatial
`p`-moment, so the Gaussian block estimate and Tonelli apply directly. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover
open BrownianSharp.SmoothResolution

/-- Jensen's concavity bound for an arbitrary nonnegative ENNReal function
on a probability space, proved through Holder so the `∞` cases stay explicit.
-/
private theorem lintegral_rpow_le_rpow_lintegral_of_probability
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
  have hone : (∫⁻ x : α, (1 : ℝ≥0∞) ^ q₂ ∂μ) = 1 := by
    simp [q₂]
  simpa [Pi.mul_apply, hpow, hone, q₁, q₂, measure_univ] using h

/-- Expected literal Besov energy for the actual finite Gaussian smooth
synthesis when the spatial and summation exponents agree. The only geometric
input is a deterministic actual-block variance envelope; the weighted
variance-moment series is displayed as a numeric summability hypothesis. -/
theorem smoothBesov_equalExponent_expected_energy_le {d ι : ℕ}
    (p r : ℝ) (hp : 1 ≤ p) (atoms : Fin ι → RealPeriodic d)
    (V : (Fin d → ℕ) → ℝ) (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    (hmeas : ∀ s : Fin d → ℕ, Measurable (fun z : Fin ι → ℝ =>
      (SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r s
        (gaussianSynthesis atoms z)) ^ p))
    (hspatialMeas : ∀ s : Fin d → ℕ, Measurable (fun z : Fin ι → ℝ =>
      ∫⁻ x : UnitAddTorus (Fin d),
        ENNReal.ofReal (‖SmoothResolution.block s
          (gaussianSynthesis atoms z) x‖ ^ p)
        ∂(volume : Measure (UnitAddTorus (Fin d)))))
    {M : ℝ≥0∞}
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal (((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ p *
        (2 ^ p * V s ^ (p / 2) * gaussianAbsoluteMoment p))) ≤ M) :
    (∫⁻ z : Fin ι → ℝ,
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal p)
        (gaussianSynthesis atoms z) ∂productStandardGaussian (Fin ι)) ≤ M := by
  classical
  let P := productStandardGaussian (Fin ι)
  let μx := (volume : Measure (UnitAddTorus (Fin d)))
  let T : (Fin d → ℕ) → (Fin ι → ℝ) → ℝ≥0∞ := fun s z =>
    (SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r s
      (gaussianSynthesis atoms z)) ^ p
  let F : (Fin ι → ℝ) → ℝ≥0∞ := fun z => ∑' s : Fin d → ℕ, T s z
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hTmeas (s : Fin d → ℕ) : Measurable (T s) := by
    exact hmeas s
  have hFmeas : Measurable F := Measurable.tsum hTmeas
  have hF_eq (z : Fin ι → ℝ) :
      F z = smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal p)
        (gaussianSynthesis atoms z) := by
    simp [F, T, smoothBesovEnergy, ENNReal.toReal_ofReal hp0]
  have hseries :
      (∫⁻ z : Fin ι → ℝ, F z ∂P) =
        ∑' s : Fin d → ℕ, ∫⁻ z : Fin ι → ℝ, T s z ∂P := by
    rw [show (fun z : Fin ι → ℝ => F z) =
      (fun z => ∑' s : Fin d → ℕ, T s z) by rfl]
    exact MeasureTheory.lintegral_tsum
      (μ := P) (fun s => (hTmeas s).aemeasurable)
  have hterm (s : Fin d → ℕ) :
      (∫⁻ z : Fin ι → ℝ, T s z ∂P) ≤
        ENNReal.ofReal (((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ p *
          (2 ^ p * V s ^ (p / 2) * gaussianAbsoluteMoment p)) := by
    let w : ℝ := (2 : ℝ) ^ (r * ∑ i, (s i : ℝ))
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have hwpos : 0 < w := by dsimp [w]; positivity
    let b : (Fin ι → ℝ) → UnitAddTorus (Fin d) → ℂ :=
      fun z x => SmoothResolution.block s (gaussianSynthesis atoms z) x
    have hbmeasx (z : Fin ι → ℝ) : Measurable (b z) := by
      dsimp [b]
      exact (SmoothResolution.block s (gaussianSynthesis atoms z)).continuous.measurable
    have hnorm (z : Fin ι → ℝ) :
        (eLpNorm (b z) (ENNReal.ofReal p) μx) ^ p =
          ∫⁻ x : UnitAddTorus (Fin d),
            ENNReal.ofReal (‖b z x‖ ^ p) ∂μx := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        ((ENNReal.ofReal_pos.mpr hp_pos).ne') (by simp)
        (hbmeasx z).aestronglyMeasurable]
      rw [ENNReal.toReal_ofReal hp0]
      simp_rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0]
      rw [← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hp_pos.ne', ENNReal.rpow_one]
    have hT_eq (z : Fin ι → ℝ) : T s z =
        ENNReal.ofReal (w ^ p) *
          (∫⁻ x : UnitAddTorus (Fin d),
            ENNReal.ofReal (‖b z x‖ ^ p) ∂μx) := by
      dsimp [T, SmoothResolution.weightedBlockNorm, w, b]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0,
        ENNReal.ofReal_rpow_of_nonneg hw hp0]
      rw [hnorm z]
    have hweightMoment := smoothBlock_gaussian_spatialEnergy_le s atoms
      (p := p) (V := V s) hp (hV s) (hvariance s)
    have hTintegral_eq :
      (∫⁻ z : Fin ι → ℝ, T s z ∂P) =
        ENNReal.ofReal (w ^ p) *
          (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
            ENNReal.ofReal (‖SmoothResolution.block s
              (gaussianSynthesis atoms z) x‖ ^ p) ∂μx ∂P) := by
      have hfun : (fun z : Fin ι → ℝ => T s z) =
          (fun z => ENNReal.ofReal (w ^ p) *
            ∫⁻ x : UnitAddTorus (Fin d),
              ENNReal.ofReal (‖SmoothResolution.block s
                (gaussianSynthesis atoms z) x‖ ^ p) ∂μx) := by
        funext z
        exact hT_eq z
      rw [hfun, MeasureTheory.lintegral_const_mul'' _
        (hspatialMeas s).aemeasurable]
    rw [hTintegral_eq]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ w ^ p)]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    simpa [w] using hweightMoment
  have hsum :
      (∑' s : Fin d → ℕ, ∫⁻ z : Fin ι → ℝ, T s z ∂P) ≤ M :=
    (ENNReal.tsum_le_tsum hterm).trans hsummable
  calc
    (∫⁻ z : Fin ι → ℝ,
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal p)
        (gaussianSynthesis atoms z) ∂productStandardGaussian (Fin ι))
        = ∫⁻ z : Fin ι → ℝ, F z ∂P := by simp [P, hF_eq]
    _ = ∑' s : Fin d → ℕ, ∫⁻ z : Fin ι → ℝ, T s z ∂P := hseries
    _ ≤ M := hsum

/-- The diagonal finite-exponent Besov estimate gives actual Besov unit-ball
mass at least one half whenever the expected literal energy is at most one
half and the energy map is measurable. -/
theorem smoothBesov_equalExponent_unitBall_mass {d ι : ℕ}
    (p r : ℝ) (hp : 1 ≤ p) (atoms : Fin ι → RealPeriodic d)
    (V : (Fin d → ℕ) → ℝ) (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    (htermMeas : ∀ s : Fin d → ℕ, Measurable (fun z : Fin ι → ℝ =>
      (SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r s
        (gaussianSynthesis atoms z)) ^ p))
    (hspatialMeas : ∀ s : Fin d → ℕ, Measurable (fun z : Fin ι → ℝ =>
      ∫⁻ x : UnitAddTorus (Fin d),
        ENNReal.ofReal (‖SmoothResolution.block s
          (gaussianSynthesis atoms z) x‖ ^ p)
        ∂(volume : Measure (UnitAddTorus (Fin d)))))
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal (((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ p *
        (2 ^ p * V s ^ (p / 2) * gaussianAbsoluteMoment p))) ≤ 1 / 2)
    (hmeas : Measurable (fun z : Fin ι → ℝ =>
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal p)
        (gaussianSynthesis atoms z))) :
    (1 / 2 : ℝ≥0∞) ≤
      (productStandardGaussian (Fin ι))
        {z | BesovUnitBall (ENNReal.ofReal p) r (ENNReal.ofReal p)
          (gaussianSynthesis atoms z)} := by
  have hmean := smoothBesov_equalExponent_expected_energy_le
    p r hp atoms V hV hvariance htermMeas hspatialMeas hsummable
  exact smoothBesovUnitBall_mass_of_mean_le_half
    (productStandardGaussian (Fin ι)) (ENNReal.ofReal p) r
    (by simp) (fun z => gaussianSynthesis atoms z) hmeas hmean

end BrownianSharp
