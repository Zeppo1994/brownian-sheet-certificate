import BrownianSharp.AlignmentFractionalIntegerSemigroup
import BrownianSharp.AlignmentSigmaFiniteL2Tensor
import Mathlib.Tactic

/-! Actual tensor-product factorization for isotropic RL maps returned to cube
L². -/

noncomputable section
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalTensorL2Product

open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalIntegerSemigroup
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentSigmaFiniteL2Tensor

/-- The actual isotropic tensor RL map on a product source vector factors into
the scalar L² RL maps, for every order above one half. -/
theorem fractionalTensorRLToL2_product {d : ℕ} (β : ℝ) (hβ : 1/2 < β)
    (v : Fin d → UnitL2) :
    tensorRLOnL2 (d:=d) β hβ (productToCube d (productVector v)) =
      productToCube d (productVector (fun i => scalarRLOnL2 β hβ (v i))) := by
  let a : Fin d → ℝ := fun _ => β
  let F : Fin d → C(UnitInterval,ℝ) := fun i => fractionalRL β hβ (v i)
  have hprof : fractionalTensorRL a (fun _ => hβ)
      (productToCube d (productVector v)) = cubeProductProfile F := by
    ext t
    change fractionalTensorRL a (fun _ => hβ)
      (productToCube d (productVector v)) t = _
    calc
      fractionalTensorRL a (fun _ => hβ)
          (productToCube d (productVector v)) t =
          ∏ i, fractionalRL (a i) (by simpa [a] using hβ)
            (v i) (cubeCoordinate i t) :=
        fractionalTensorRL_product a (fun _ => hβ) v t
      _ = cubeProductProfile F t := by simp [cubeProductProfile, F, a]
  change cubeProfileToL2 (fractionalTensorRL (fun _ : Fin d => β)
    (fun _ => hβ) (productToCube d (productVector v))) = _
  rw [hprof, cubeProfileToL2_cubeProduct]
  rfl


end BrownianSharp.AlignmentFractionalTensorL2Product
