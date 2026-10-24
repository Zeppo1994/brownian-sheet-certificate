import BrownianSharp.SmoothResolution
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-! Actual smooth-resolution class-energy events. These lemmas concern the
literal ENNReal Besov and Sobolev expressions, rather than a coefficient proxy.
The expectation hypotheses are deliberately left as estimates to be discharged
by pointwise Gaussian moments and Tonelli/Fubini from interpolation bounds. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp

/-- Markov's inequality in sublevel form for a nonnegative ENNReal energy on a
probability space. The energy may itself be defined by an infinite `tsum` or
`lintegral`; no conversion through `toReal` is involved. -/
theorem ennreal_energy_sublevel_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → ℝ≥0∞) (hE : Measurable E) {M : ℝ≥0∞}
    (hM0 : 0 < M) (hMtop : M ≠ ∞)
    (hmean : ∫⁻ ω, E ω ∂μ ≤ M) :
    (1 / 2 : ℝ≥0∞) ≤ μ {ω | E ω ≤ 2 * M} := by
  let bad : Set Ω := {ω | 2 * M < E ω}
  have hmark := meas_ge_le_lintegral_div (μ := μ) hE.aemeasurable
    (ε := 2 * M) (by positivity)
    (ENNReal.mul_ne_top (by norm_num) hMtop)
  have hbad : μ bad ≤ (1 / 2 : ℝ≥0∞) := by
    have hbad_le : μ bad ≤ μ {ω | 2 * M ≤ E ω} := by
      apply measure_mono
      intro ω hω
      change 2 * M < E ω at hω
      exact hω.le
    calc
      μ bad ≤ μ {ω | 2 * M ≤ E ω} := hbad_le
      _ ≤ (∫⁻ ω, E ω ∂μ) / (2 * M) := hmark
      _ ≤ M / (2 * M) := ENNReal.div_le_div_right hmean (2 * M)
      _ ≤ (1 / 2 : ℝ≥0∞) := by
        have hMne : M ≠ 0 := ne_of_gt hM0
        rw [show (2 : ℝ≥0∞) * M = M * 2 by rw [mul_comm]]
        apply (ENNReal.div_le_iff_le_mul
          (Or.inl (mul_ne_zero hMne (by norm_num)))
          (Or.inl (ENNReal.mul_ne_top hMtop (by norm_num)))).2
        have htwo : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
          rw [mul_comm]
          exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
        have heq : M = (1 / 2 : ℝ≥0∞) * (M * 2) := calc
          M = M * (2 * (1 / 2 : ℝ≥0∞)) := by rw [htwo, mul_one]
          _ = (1 / 2 : ℝ≥0∞) * (M * 2) := by ac_rfl
        exact heq.le
  have hbad_meas : MeasurableSet bad := measurableSet_lt measurable_const hE
  have hbad_ne : μ bad ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hbad (by norm_num : (1 / 2 : ℝ≥0∞) < ∞))
  have hgood : {ω | E ω ≤ 2 * M} = badᶜ := by
    ext ω
    simp [bad, not_lt]
  rw [hgood, measure_compl hbad_meas hbad_ne, measure_univ]
  have hle : μ bad ≤ 1 := hbad.trans (by norm_num)
  exact (ENNReal.le_sub_iff_add_le_right hbad_ne hle).2 (by
    calc
      (1 / 2 : ℝ≥0∞) + μ bad ≤ (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) :=
        by simpa [add_comm] using
          (add_le_add_left hbad (1 / 2 : ℝ≥0∞))
      _ = 1 := ENNReal.add_halves 1)

/-- The literal finite-θ Besov energy, written as the same infinite sum that
defines `BesovUnitBall`. -/
def smoothBesovEnergy {d : ℕ} (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞)
    (f : Torus.RealPeriodic d) : ℝ≥0∞ :=
  ∑' s : Fin d → ℕ, (SmoothResolution.weightedBlockNorm p r s f) ^ θ.toReal

/-- For finite `θ`, the actual Besov unit-ball condition is exactly the
sublevel event of the literal weighted block energy. -/
theorem smoothBesovUnitBall_iff_energy_le_one {d : ℕ} (p : ℝ≥0∞)
    (r : ℝ) {θ : ℝ≥0∞} (hθ : θ ≠ ∞) (f : Torus.RealPeriodic d) :
    SmoothResolution.BesovUnitBall p r θ f ↔ smoothBesovEnergy p r θ f ≤ 1 := by
  simp [SmoothResolution.BesovUnitBall, smoothBesovEnergy, hθ]

/-- Probability lower bound for a genuine finite-θ Besov-energy sublevel.
Once the expectation bound is obtained by the pointwise Gaussian/Fubini
calculation, this gives the actual block-norm event (not a coefficient event). -/
theorem smoothBesovEnergy_sublevel_mass {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) (r : ℝ) {θ : ℝ≥0∞} (hθ : θ ≠ ∞)
    (f : Ω → Torus.RealPeriodic d) (M : ℝ≥0∞)
    (hM0 : 0 < M) (hMtop : M ≠ ∞)
    (hmeas : Measurable (fun ω => smoothBesovEnergy p r θ (f ω)))
    (hmean : ∫⁻ ω, smoothBesovEnergy p r θ (f ω) ∂μ ≤ M) :
    (1 / 2 : ℝ≥0∞) ≤ μ {ω | smoothBesovEnergy p r θ (f ω) ≤ 2 * M} :=
  ennreal_energy_sublevel_mass μ _ hmeas hM0 hMtop hmean

/-- Probability lower bound for the exact square-function integral used by the
literal Sobolev unit ball. No finite-block or coefficient substitute appears
in the event. -/
theorem smoothSobolevEnergy_sublevel_mass {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p r : ℝ) (f : Ω → Torus.RealPeriodic d) (M : ℝ≥0∞)
    (hM0 : 0 < M) (hMtop : M ≠ ∞)
    (hmeas : Measurable (fun ω =>
      ∫⁻ x, (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))))
    (hmean : ∫⁻ ω,
      ∫⁻ x, (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d))) ∂μ ≤ M) :
    (1 / 2 : ℝ≥0∞) ≤ μ {ω |
      ∫⁻ x, (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d))) ≤ 2 * M} :=
  ennreal_energy_sublevel_mass μ _ hmeas hM0 hMtop hmean

/-- If the expected literal finite-θ Besov energy is at most one half, then
the actual Besov unit ball has at least one half of the Gaussian mass. -/
theorem smoothBesovUnitBall_mass_of_mean_le_half {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) (r : ℝ) {θ : ℝ≥0∞} (hθ : θ ≠ ∞)
    (f : Ω → Torus.RealPeriodic d)
    (hmeas : Measurable (fun ω => smoothBesovEnergy p r θ (f ω)))
    (hmean : ∫⁻ ω, smoothBesovEnergy p r θ (f ω) ∂μ ≤ 1 / 2) :
    (1 / 2 : ℝ≥0∞) ≤ μ {ω | SmoothResolution.BesovUnitBall p r θ (f ω)} := by
  have hcut := ennreal_energy_sublevel_mass μ
    (fun ω => smoothBesovEnergy p r θ (f ω)) hmeas
    (by norm_num : (0 : ℝ≥0∞) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) hmean
  have hset : {ω | smoothBesovEnergy p r θ (f ω) ≤ 1} =
      {ω | SmoothResolution.BesovUnitBall p r θ (f ω)} := by
    ext ω
    exact (smoothBesovUnitBall_iff_energy_le_one p r hθ (f ω)).symm
  have hcut' : (1 / 2 : ℝ≥0∞) ≤
      μ {ω | smoothBesovEnergy p r θ (f ω) ≤ 1} := by
    have htwo : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    rw [htwo] at hcut
    exact hcut
  rw [← hset]
  exact hcut'

/-- If the expected exact square-function integral is at most one half, the
literal Sobolev unit ball has at least one half of the mass. -/
theorem smoothSobolevUnitBall_mass_of_mean_le_half {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p r : ℝ) (f : Ω → Torus.RealPeriodic d)
    (hmeas : Measurable (fun ω =>
      ∫⁻ x, (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))))
    (hmean : ∫⁻ ω,
      ∫⁻ x, (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d))) ∂μ ≤ 1 / 2) :
    (1 / 2 : ℝ≥0∞) ≤ μ {ω | SmoothResolution.SobolevUnitBall p r (f ω)} := by
  have hcut := ennreal_energy_sublevel_mass μ
    (fun ω => ∫⁻ x,
      (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))) hmeas
    (by norm_num : (0 : ℝ≥0∞) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) hmean
  have hset : {ω | ∫⁻ x,
      (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d))) ≤ 1} =
      {ω | SmoothResolution.SobolevUnitBall p r (f ω)} := by
    ext ω
    rfl
  have hcut' : (1 / 2 : ℝ≥0∞) ≤ μ {ω |
      ∫⁻ x, (SmoothResolution.squareFunctionSquared r (f ω) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d))) ≤ 1} := by
    have htwo : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    rw [htwo] at hcut
    exact hcut
  rw [← hset]
  exact hcut'

end BrownianSharp
