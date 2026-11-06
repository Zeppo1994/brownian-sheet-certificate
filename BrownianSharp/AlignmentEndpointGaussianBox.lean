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

end BrownianSharp
