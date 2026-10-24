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

theorem nativeGoodUniformEvent_mass_lt_one {d n : ℕ} (hd : 0 < d) (ε : ℝ) :
    (productStandardGaussian (LayerIndex d n)).real (nativeGoodUniformEvent d n ε) < 1 := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  have hnz : ∃ q : NativeGoodGrid d n, ∃ a, nativeLayerRowCoefficient q.val a ≠ 0 := by
    by_contra hn
    push_neg at hn
    let q : NativeGoodGrid d n := Classical.choice inferInstance
    have hv := nativeGoodGrid_variance_pos hd q
    simp only [nativeLayerRowVariance, hn q, zero_pow (by norm_num : (2:ℕ)≠0), Finset.sum_const_zero] at hv
    exact (lt_irrefl 0 hv)
  exact gaussian_uniform_event_mass_lt_one _ hnz ε

/-- The native field has an actual exponential confinement estimate at every
positive grade after the finite initial scales are absorbed into the constant. -/
theorem nativeGoodUniform_confinement_all_grades_of_ehrhard
    (hEhrhard : ProductGaussianEhrhard) {d : ℕ} (hd : 2 ≤ d) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 0 < n →
      (productStandardGaussian (LayerIndex d n)).real
        (nativeGoodUniformEvent d n
          (sharpRadius d (nativeRadiusConstant d (1/2) (nativeMomentSlope d)) n)) ≤
      Real.exp (-b * nativeDimension d n) := by
  obtain ⟨N, hN, hbound⟩ := nativeGoodUniform_confinement_of_ehrhard hEhrhard hd
  obtain ⟨b, hb, hall⟩ := eventual_exponential_bound_global
    (fun n => (productStandardGaussian (LayerIndex d n)).real
      (nativeGoodUniformEvent d n
        (sharpRadius d (nativeRadiusConstant d (1/2) (nativeMomentSlope d)) n)))
    (nativeDimension d) 1 N
    (fun n hn => (by positivity : (0:ℝ)<2^n).trans_le
      (nativeDimension_ge_dyadic d n (by omega)))
    (fun n hn => nativeGoodUniformEvent_mass_lt_one (by omega) _) (nativeConfinementExponent_pos d) hbound
  exact ⟨b, hb, fun n hn => hall n (by omega)⟩

end BrownianSharp
