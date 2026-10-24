import BrownianSharp.AlignmentEndpointCoefficientBox
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! A fixed one-coordinate Gaussian box has positive mass. This supplies the
scalar probability needed by the proved finite product-box estimate.
-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology
open scoped ENNReal NNReal

namespace BrownianSharp

private noncomputable def centralGaussianDensity : ℝ → ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1

private noncomputable def centralGaussianBoxIntegral : ℝ :=
  ∫ x in Set.Icc (-1 : ℝ) 1, centralGaussianDensity x

private theorem centralGaussianBoxIntegral_pos :
    0 < centralGaussianBoxIntegral := by
  rw [centralGaussianBoxIntegral]
  let μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)
  have hnonneg : 0 ≤ centralGaussianDensity := by
    intro x
    exact ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x
  have hint : Integrable centralGaussianDensity μ := by
    exact (ProbabilityTheory.integrable_gaussianPDFReal 0 1).restrict
  have hsupport : Function.support centralGaussianDensity = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true, ne_eq]
    exact (ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)).ne'
  have hμ : 0 < μ (Function.support centralGaussianDensity) := by
    rw [hsupport]
    change 0 < (volume.restrict (Set.Icc (-1 : ℝ) 1)) Set.univ
    rw [Measure.restrict_apply_univ]
    norm_num
  exact (integral_pos_iff_support_of_nonneg hnonneg hint).2 hμ

/-- A fixed symmetric interval around zero retains enough standard Gaussian
mass for an exponential-in-dimension coefficient box. The exponent is
chosen from the proved scalar mass. -/
theorem exists_standardGaussian_box_exponent :
    ∃ b : ℝ, 0 < b ∧
      ENNReal.ofReal (Real.exp (-b/4)) ≤
        ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-1 : ℝ) 1) := by
  let q := centralGaussianBoxIntegral
  have hqpos : 0 < q := centralGaussianBoxIntegral_pos
  have hqnonneg : 0 ≤ q := hqpos.le
  have hmeasure : ProbabilityTheory.gaussianReal 0 1
      (Set.Icc (-1 : ℝ) 1) = ENNReal.ofReal q := by
    dsimp [q, centralGaussianBoxIntegral]
    exact ProbabilityTheory.gaussianReal_apply_eq_integral 0
      (one_ne_zero : (1 : ℝ≥0) ≠ 0) (Set.Icc (-1 : ℝ) 1)
  have hqle : q ≤ 1 := by
    have hle : ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-1 : ℝ) 1) ≤ 1 := by
      calc
        _ ≤ ProbabilityTheory.gaussianReal 0 1 Set.univ := measure_mono
          (Set.subset_univ _)
        _ = 1 := measure_univ
    have htop : ProbabilityTheory.gaussianReal 0 1
        (Set.Icc (-1 : ℝ) 1) ≠ ∞ := measure_ne_top _ _
    have hle' := ENNReal.toReal_mono ENNReal.one_ne_top hle
    rw [hmeasure, ENNReal.toReal_ofReal hqnonneg, ENNReal.toReal_one] at hle'
    exact hle'
  let b : ℝ := 4 * (1 + Real.log q⁻¹)
  have hqinv : 1 ≤ q⁻¹ := by
    exact (one_le_inv₀ hqpos).2 hqle
  have hlog : 0 ≤ Real.log q⁻¹ := Real.log_nonneg hqinv
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨b, hb, ?_⟩
  rw [hmeasure]
  apply ENNReal.ofReal_le_ofReal
  have hexp : Real.exp (-b/4) = Real.exp (-1) * q := by
    rw [show -b/4 = -(1 + Real.log q⁻¹) by dsimp [b]; ring,
      Real.exp_neg, Real.exp_add, Real.exp_log (inv_pos.mpr hqpos)]
    simp [mul_inv, Real.exp_neg]
    ring
  rw [hexp]
  have he : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  calc
    Real.exp (-1) * q ≤ 1 * q := mul_le_mul_of_nonneg_right he hqnonneg
    _ = q := one_mul q

/-- The standard Gaussian coefficient box has the advertised mass in the
full coefficient dimension. -/
theorem standardGaussian_coefficientBox_mass_lower
    {ι : Type*} [Fintype ι] :
    ∃ b : ℝ, 0 < b ∧
      ENNReal.ofReal (Real.exp (-b * (Fintype.card ι : ℝ) / 4)) ≤
        (Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))
          (coefficientBox (ι := ι) 1) := by
  obtain ⟨b, hb, hscalar⟩ := exists_standardGaussian_box_exponent
  refine ⟨b, hb, ?_⟩
  exact productMeasure_coefficientBox_exp_lower
    (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
    (by intro i; infer_instance) 1 b hb (by intro i; exact hscalar)

/-- For every prescribed positive entropy cost, a sufficiently large fixed
coordinate box has scalar Gaussian mass at least the required amount. -/
theorem exists_standardGaussian_box_for_exponent {b : ℝ} (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧
      ENNReal.ofReal (Real.exp (-b/4)) ≤
        ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-M) M) := by
  let μ : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let S : ℕ → Set ℝ := fun n => Set.Icc (-(n : ℝ)) (n : ℝ)
  have hUnion : (⋃ n, S n) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    refine ⟨n, ?_⟩
    have hn' : |x| ≤ (n : ℝ) := by exact_mod_cast hn.le
    exact abs_le.mp hn'
  have hmono : Monotone S := by
    intro m n hmn
    apply Set.Icc_subset_Icc
    · exact neg_le_neg (by exact_mod_cast hmn)
    · exact_mod_cast hmn
  have hlim' : Tendsto (fun n => μ (S n)) atTop
      (𝓝 (μ (⋃ n, S n))) := by
    change Tendsto (μ ∘ S) atTop (𝓝 (μ (⋃ n, S n)))
    exact tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hlim : Tendsto (fun n => μ (S n)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa [hUnion, μ] using hlim'
  have htarget : ENNReal.ofReal (Real.exp (-b/4)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    apply Real.exp_lt_one_iff.mpr
    linarith
  have heventually : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-b/4)) < μ (S n) :=
    hlim.eventually (Ioi_mem_nhds htarget)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 heventually)
  refine ⟨(N + 1 : ℕ), by positivity, ?_⟩
  have hN' := hN (N + 1) (by omega)
  change ENNReal.ofReal (Real.exp (-b/4)) ≤
    ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-((N+1:ℕ):ℝ)) ((N+1:ℕ):ℝ))
  exact hN'.le

/-- Arbitrary prescribed `b` in the actual product Gaussian coefficient
box event, with its threshold quantified concretely. -/
theorem standardGaussian_coefficientBox_mass_for_exponent
    {ι : Type*} [Fintype ι] {b : ℝ} (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧
      ENNReal.ofReal (Real.exp (-b * (Fintype.card ι : ℝ) / 4)) ≤
        (Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))
          (coefficientBox M) := by
  obtain ⟨M, hM, hscalar⟩ := exists_standardGaussian_box_for_exponent hb
  refine ⟨M, hM, ?_⟩
  exact productMeasure_coefficientBox_exp_lower
    (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
    (by intro i; infer_instance) M b hb (by intro i; exact hscalar)

end BrownianSharp
