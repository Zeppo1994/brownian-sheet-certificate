import BrownianSharp.NativeUniformConfinement
import BrownianSharp.ExponentialGlobalization

/-! A nonzero finite Gaussian linear field has confinement probability
strictly below one at every finite threshold. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

/-- No nonzero finite linear field is almost surely confined to a finite cube. -/
theorem gaussian_uniform_event_mass_lt_one {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : ι → κ → ℝ) (hnonzero : ∃ i k, A i k ≠ 0) (ε : ℝ) :
    (productStandardGaussian κ).real {x | ∀ i, |∑ k, A i k*x k| ≤ ε} < 1 := by
  classical
  let E : Set (κ → ℝ) := {x | ∀ i, |∑ k, A i k*x k| ≤ ε}
  have hE : IsClosed E := by
    simp only [E, Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)
  obtain ⟨i, k, hik⟩ := hnonzero
  let x : κ → ℝ := Pi.single k ((|ε|+1)/(A i k))
  have hsum : (∑ j, A i j*x j) = |ε|+1 := by
    simp only [x, Pi.single_apply]
    rw [Finset.sum_eq_single k]
    · simp only [ite_true]
      field_simp
    · intro j hj hjk
      simp [hjk]
    · simp
  have hx : x ∉ E := by
    intro h
    have hi := h i
    rw [hsum, abs_of_pos (by positivity)] at hi
    linarith [le_abs_self ε]
  have hpos := GaussianDensity.standardGaussian_open_pos hE.isOpen_compl ⟨x, hx⟩
  have hreal : 0 < (productStandardGaussian κ).real Eᶜ :=
    ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _)
  have htotal := measureReal_add_measureReal_compl (μ := productStandardGaussian κ) hE.measurableSet
  simp only [probReal_univ] at htotal
  change (productStandardGaussian κ).real E < 1
  linarith

end BrownianSharp
