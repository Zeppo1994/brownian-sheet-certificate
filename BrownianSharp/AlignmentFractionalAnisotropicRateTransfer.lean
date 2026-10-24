import BrownianSharp.AlignmentFractionalApproximationReduction
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.ExtendedStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Transfer a sharp isotropic approximation-number lower rate to the actual
anisotropic RL operator through the minimum-order coordinate reduction. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentFractionalAnisotropicRateTransfer

open BrownianSharp.AlignmentFractionalApproximationReduction
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp

/-- Any eventual isotropic lower approximation-number rate transfers to the
actual anisotropic tensor operator with the same rate and a changed constant,
whenever the isotropic order is attained on at least `ν` coordinates. -/
theorem anisotropic_approximation_lower_of_isotropic_rate
    {d ν : ℕ} (hd : 2 ≤ d) (hν : 2 ≤ ν)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i) (r : ℝ) (hr : 1/2 < r)
    (hm : Latest.minimumMultiplicity a r ν)
    (hiso : ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate (r-1/2)
          (r*((ν-1:ℕ):ℝ)) k) ≤
          approximationNumber (fractionalTensorRL (fun _ : Fin ν => r)
            (fun _ => hr)) k) :
    ∃ cA : ℝ, 0 < cA ∧ ∃ k₁ : ℕ, 2 ≤ k₁ ∧
      ∀ k : ℕ, k₁ ≤ k →
        ENNReal.ofReal (cA * logarithmicIndexRate (r-1/2)
          (r*((ν-1:ℕ):ℝ)) k) ≤ approximationNumber (fractionalTensorRL a ha) k := by
  obtain ⟨C,hC,hred⟩ :=
    general_minimum_approximationNumber_reduction a ha r hr hm
  obtain ⟨c,hc,k₀,hk₀,hlower⟩ := hiso
  refine ⟨c/C,div_pos hc hC,max 2 k₀,le_max_left _ _,?_⟩
  intro k hk
  have hk2 : 2 ≤ k := (le_max_left 2 k₀).trans hk
  have hk0 : k₀ ≤ k := (le_max_right 2 k₀).trans hk
  have hIso := hlower k hk0
  have hredk := hred k (by omega)
  have hprod : ENNReal.ofReal
      (c*logarithmicIndexRate (r-1/2)
        (r*((ν-1:ℕ):ℝ)) k) ≤
      ENNReal.ofReal C * approximationNumber (fractionalTensorRL a ha) k :=
    hIso.trans hredk
  have hrate_nonneg : 0 ≤ logarithmicIndexRate (r-1/2)
      (r*((ν-1:ℕ):ℝ)) k := by
    unfold logarithmicIndexRate
    apply mul_nonneg
    · exact Real.rpow_nonneg (by exact_mod_cast (show 0≤k by omega)) _
    · apply Real.rpow_nonneg
      exact le_of_lt (Real.log_pos (by exact_mod_cast (show 1<k by omega)))
  have hreal : (c/C)*logarithmicIndexRate (r-1/2)
      (r*((ν-1:ℕ):ℝ)) k =
      (c*logarithmicIndexRate (r-1/2)
        (r*((ν-1:ℕ):ℝ)) k)/C := by field_simp
  rw [hreal, ENNReal.ofReal_div_of_pos hC]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hC)
    ENNReal.ofReal_ne_top).mpr
  simpa [ENNReal.ofReal_mul hrate_nonneg, mul_comm] using hprod

end BrownianSharp.AlignmentFractionalAnisotropicRateTransfer
