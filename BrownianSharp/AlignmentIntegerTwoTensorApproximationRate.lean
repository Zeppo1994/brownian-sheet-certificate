import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalL2
import BrownianSharp.AlignmentIntegerTensorLowerRate
import Mathlib.Tactic

/-! All-index conversion for the actual continuous-output tensor product of
integer-order-two Riemann--Liouville operators. The remaining input is an
explicit layerwise trace lower bound.
-/

noncomputable section
open scoped ENNReal
open HaarQuarter

namespace BrownianSharp.AlignmentIntegerTwoTensorApproximationRate

open BrownianSharp.AlignmentIntegerTensorLowerRate
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalL2

/-- The actual tensor order-two Riemann--Liouville operator with continuous
function output. The approximation-number lower is for this C-valued map;
the L² tensor map is used internally to establish trace energy. -/
def integerTwoTensorRL {d : ℕ} :
    BrownianSharp.CameronMartin.UnitCubeL2 d →L[ℝ]
      C(HaarQuarter.BrownianCubeAnchor d, ℝ) :=
  fractionalTensorRL (fun _ : Fin d => 2) (by intro i; norm_num)

/-- Approximation numbers of the actual continuous-output tensor R₂ map. -/
def integerTwoTensorApproximationNumber (d : ℕ) (k : ℕ) : ℝ≥0∞ :=
  approximationNumber (integerTwoTensorRL (d:=d)) k

/-- Normalize the selected-block product floor to the dyadic form consumed by
the all-index crossing lemma. -/
theorem integerTwo_layer_sigma_normalize (d N : ℕ) :
    (((25 * Real.pi^2 : ℝ)^d) * (2:ℝ)^(2*N))⁻¹ =
      (25 * Real.pi^2 : ℝ)^(-(d:ℝ)) * (2:ℝ)^(-2*(N:ℝ)) := by
  rw [mul_inv, ← Real.rpow_natCast (25 * Real.pi^2 : ℝ) d,
    ← Real.rpow_natCast (2:ℝ) (2*N)]
  rw [← Real.rpow_neg (by positivity : 0 ≤ (25 * Real.pi^2 : ℝ)),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1 <;> push_cast <;> ring

/-- Convert the sharp tensor layer lower bound to the all-index order-two
approximation-number rate. The layer hypothesis is the only source-specific
input; the numerical conversion is unconditional. -/
theorem integerTwo_tensor_all_index_lower_of_layer_bound
    {d : ℕ} (hd : 2 ≤ d) (N₀ : ℕ)
    (hlayer : ∀ N k : ℕ, N₀ ≤ N → 1 ≤ k →
      k ≤ Fintype.card (BrownianSharp.LayerIndex d N) →
      ENNReal.ofReal (((25 * Real.pi^2 : ℝ)^(-(d:ℝ))) *
        (2:ℝ)^(-2*(N:ℝ)) *
        Real.sqrt (((Fintype.card (BrownianSharp.LayerIndex d N) - (k-1):ℕ):ℝ))) ≤
        integerTwoTensorApproximationNumber d k) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c₁ * (k:ℝ)^((-2 : ℝ) + (2:ℝ)⁻¹) *
          (Real.log (k:ℝ))^(2*((d-1:ℕ):ℝ))) ≤
          integerTwoTensorApproximationNumber d k := by
  let c : ℝ := (25 * Real.pi^2)^(-(d:ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have h := all_index_lower_of_layer_bound (d:=d) hd 2 c (by norm_num) hc N₀
    (integerTwoTensorApproximationNumber d) (by
      intro N k hN hk hkD
      simpa [integerTwoTensorApproximationNumber, integerTwoTensorRL, c] using
        hlayer N k hN hk hkD)
  simpa [integerTwoTensorApproximationNumber] using h

end BrownianSharp.AlignmentIntegerTwoTensorApproximationRate
