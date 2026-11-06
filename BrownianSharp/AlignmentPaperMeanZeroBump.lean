import BrownianSharp.AlignmentPaperGenericBumpCertified
import BrownianSharp.PeriodicAtomDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The optional coordinatewise mean-zero atom choice in manuscript Remark
3.3. A normalized derivative of the concrete smooth plateau gives a genuine
nonzero admissible smooth bump of zero integral. -/
noncomputable section
open MeasureTheory
namespace BrownianSharp.AlignmentPaperMeanZeroBump

open BrownianSharp.AlignmentPaperContinuumGenericBump

private theorem smoothAtom_deriv_nonzero : ∃ x : ℝ, deriv smoothAtom x ≠ 0 := by
  by_contra hn
  push Not at hn
  have hFTC : (∫ x in (0:ℝ)..(1/2:ℝ), deriv smoothAtom x) =
      smoothAtom (1/2) - smoothAtom 0 := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro x hx
      exact (smoothAtom_contDiff.differentiable (by simp)).differentiableAt
    · exact (smoothAtom_contDiff.continuous_deriv (by simp)).intervalIntegrable _ _
  have hzero := smoothAtom_support 0 (Or.inl le_rfl)
  have hone := smoothAtom_plateau (1/2) (by constructor <;> norm_num)
  rw [hone, hzero] at hFTC
  simp [hn] at hFTC

/-- The mean-zero bump required by the paper exists within the exact
admissible class used by the continuum confinement theorem. -/
theorem exists_meanZero_smooth_admissibleBump :
    ∃ ψ : AdmissibleBump,
      ContDiff ℝ (⊤ : ℕ∞) ψ.atom ∧
      tsupport ψ.atom ⊆ Set.Icc (1/8:ℝ) (7/8:ℝ) ∧
      (∫ x in (0:ℝ)..1, ψ.atom x) = 0 := by
  obtain ⟨C,hC,hbound⟩ := exists_smoothAtom_iteratedDeriv_bound 1
  have hderSmooth : ContDiff ℝ (⊤ : ℕ∞) (deriv smoothAtom) := by
    simpa using ContDiff.iterate_deriv 1 smoothAtom_contDiff
  let ψ : AdmissibleBump := {
    atom := fun x => C⁻¹ * deriv smoothAtom x
    continuous := continuous_const.mul hderSmooth.continuous
    support_subset := by
      intro x hx
      have hnonzero : C⁻¹ * deriv smoothAtom x ≠ 0 := hx
      constructor
      · by_contra hx0
        have hd : deriv smoothAtom x = 0 := by
          simpa using iteratedDeriv_smoothAtom_eq_zero_of_nonpos 1 (not_lt.mp hx0)
        exact hnonzero (by rw [hd, mul_zero])
      · by_contra hx1
        have hd : deriv smoothAtom x = 0 := by
          simpa using iteratedDeriv_smoothAtom_eq_zero_of_one_le 1 (not_lt.mp hx1)
        exact hnonzero (by rw [hd, mul_zero])
    abs_le_one := by
      intro x
      rw [abs_mul, abs_inv, abs_of_pos hC]
      apply (inv_mul_le_iff₀ hC).2
      simpa using hbound x
    nonzero := by
      obtain ⟨x,hx⟩ := smoothAtom_deriv_nonzero
      exact ⟨x,mul_ne_zero (inv_ne_zero hC.ne') hx⟩ }
  have hsupp : tsupport smoothAtom ⊆ Set.Icc (1/8:ℝ) (7/8:ℝ) := by
    apply closure_minimal ?_ isClosed_Icc
    intro x hx
    change smoothAtom x ≠ 0 at hx
    constructor
    · by_contra h
      exact hx (smoothAtom_support_inner x (Or.inl (not_le.mp h).le))
    · by_contra h
      exact hx (smoothAtom_support_inner x (Or.inr (not_le.mp h).le))
  have hψsupp : tsupport ψ.atom ⊆ Set.Icc (1/8:ℝ) (7/8:ℝ) := by
    apply (closure_minimal (s := Function.support ψ.atom) (t := tsupport smoothAtom)
      ?_ isClosed_closure).trans hsupp
    intro x hx
    apply support_deriv_subset
    have hne : C⁻¹ * deriv smoothAtom x ≠ 0 := hx
    exact (mul_ne_zero_iff.mp hne).2
  refine ⟨ψ,contDiff_const.mul hderSmooth,hψsupp,?_⟩
  change (∫ x in (0:ℝ)..1, C⁻¹ * deriv smoothAtom x) = 0
  rw [intervalIntegral.integral_const_mul]
  have hFTC : (∫ x in (0:ℝ)..1, deriv smoothAtom x) =
      smoothAtom 1 - smoothAtom 0 := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro x hx
      exact (smoothAtom_contDiff.differentiable (by simp)).differentiableAt
    · exact hderSmooth.continuous.intervalIntegrable _ _
  rw [hFTC, smoothAtom_support 1 (Or.inr le_rfl),
    smoothAtom_support 0 (Or.inl le_rfl)]
  ring

/-- Extending the integration interval beyond the support does not change
the bump's integral. -/
theorem integral_eq_unit_of_admissible (ψ : AdmissibleBump)
    {a b : ℝ} (ha : a ≤ 0) (hb : 1 ≤ b) :
    (∫ x in a..b, ψ.atom x) = ∫ x in (0:ℝ)..1, ψ.atom x := by
  have hi : ∀ a b : ℝ, IntervalIntegrable ψ.atom volume a b :=
    fun a b => ψ.continuous.intervalIntegrable a b
  have hl : (∫ x in a..0, ψ.atom x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with x hx
    have hx0 : x ≤ 0 := by simpa [max_eq_right ha] using hx.2
    exact ψ.eq_zero_of_outside (Or.inl hx0)
  have hr : (∫ x in (1:ℝ)..b, ψ.atom x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with x hx
    have hx1 : 1 ≤ x := by
      have hstrict : 1 < x := by simpa [min_eq_left hb] using hx.1
      exact hstrict.le
    exact ψ.eq_zero_of_outside (Or.inr hx1)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a 0) (hi 0 b),
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 b), hl, hr]
  ring

/-- Every dyadic rescaling of a mean-zero bump has zero integral on the
unit interval, exactly as used for coordinatewise mean-zero atoms. -/
theorem dyadic_bump_integral_zero (ψ : AdmissibleBump)
    (hmean : (∫ x in (0:ℝ)..1, ψ.atom x) = 0)
    (s m : ℕ) (hm : m < 2^s) :
    (∫ x in (0:ℝ)..1, ψ.atom ((2:ℝ)^s*x-m)) = 0 := by
  have hleft : -(m:ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
  have hright : 1 ≤ (2:ℝ)^s-(m:ℝ) := by
    have hm' : m+1 ≤ 2^s := Nat.succ_le_of_lt hm
    have hcast : (m:ℝ)+1 ≤ (2:ℝ)^s := by exact_mod_cast hm'
    linarith
  rw [intervalIntegral.integral_comp_mul_sub ψ.atom
    (by positivity : (2:ℝ)^s ≠ 0) (m:ℝ)]
  simp only [mul_zero, zero_sub, mul_one]
  rw [integral_eq_unit_of_admissible ψ hleft hright, hmean, smul_zero]

end BrownianSharp.AlignmentPaperMeanZeroBump
