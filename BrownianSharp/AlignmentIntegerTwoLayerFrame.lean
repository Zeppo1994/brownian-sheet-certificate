import BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame
import BrownianSharp.AlignmentIntegerTwoTensorEnergy

/-! Address the scalar selected dyadic frames by the native `LayerIndex`.
This gives an orthonormal family indexed by the full tensor frequency layer,
with pairwise orthogonal actual order-two RL images. -/

noncomputable section
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentIntegerTwoLayerFrame

open BrownianSharp
open BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame
open BrownianSharp.AlignmentIntegerTwoTensorEnergy
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentSigmaFiniteL2Tensor

/-- The scalar universal-frame address in coordinate `i` of a tensor layer. -/
def layerAxisIndex {d N : ℕ} (a : LayerIndex d N) (i : Fin d) :
    SelectedIndex :=
  ⟨layerIndexDepth a i, a.2 i⟩

/-- The tensor source indexed by the native hyperbolic layer. -/
def layerSource {d N : ℕ} (a : LayerIndex d N) :
    CameronMartin.UnitCubeL2 d :=
  productToCube d (productVector (fun i => selectedSource (layerAxisIndex a i)))

/-- Public name matching the native integer-two layer construction. -/
abbrev integerTwoLayerSource {d N : ℕ} (a : LayerIndex d N) :
    CameronMartin.UnitCubeL2 d := layerSource a

/-- Distinct layer indices differ in at least one coordinate address. -/
theorem exists_layerAxisIndex_ne {d N : ℕ} {a b : LayerIndex d N}
    (hab : a ≠ b) : ∃ i : Fin d, layerAxisIndex a i ≠ layerAxisIndex b i := by
  classical
  by_contra h
  push_neg at h
  apply hab
  rcases a with ⟨ra, aa⟩
  rcases b with ⟨rb, ab⟩
  have hprofile : ra.1 = rb.1 :=
    Finsupp.ext (fun i => congrArg Sigma.fst (h i))
  have hra : ra = rb := Subtype.ext hprofile
  subst rb
  have haddr : aa = ab := by
    funext i
    apply Fin.ext
    exact congrArg (fun z : SelectedIndex => z.2.val) (h i)
  subst ab
  rfl

/-- The native tensor layer source family is orthonormal. -/
theorem layerSource_orthonormal {d N : ℕ} :
    Orthonormal ℝ (layerSource (d:=d) (N:=N)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  change inner ℝ
    (productToCube d (productVector (fun i => selectedSource (layerAxisIndex a i))))
    (productToCube d (productVector (fun i => selectedSource (layerAxisIndex b i)))) = _
  rw [productToCube_inner_product]
  simp_rw [orthonormal_iff_ite.mp selectedSource_orthonormal]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := exists_layerAxisIndex_ne hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Actual order-two tensor RL images of distinct layer sources are
orthogonal in the target L² space. -/
theorem layerImage_pairwise_orthogonal {d N : ℕ} :
    ∀ a b : LayerIndex d N, a ≠ b →
      inner ℝ (integerTwoTensorL2 (layerSource a))
        (integerTwoTensorL2 (layerSource b)) = 0 := by
  intro a b hab
  obtain ⟨i, hi⟩ := exists_layerAxisIndex_ne hab
  change inner ℝ
    (integerTwoTensorL2 (productToCube d (productVector
      (fun i => selectedSource (layerAxisIndex a i)))))
    (integerTwoTensorL2 (productToCube d (productVector
      (fun i => selectedSource (layerAxisIndex b i))))) = 0
  rw [integerTwoTensorL2_product, integerTwoTensorL2_product,
    productToCube_inner_product]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    exact selectedImage_pairwise_orthogonal _ _ hi)

/-- Every tensor layer source has the fixed-profile singular-value lower
bound, with total profile grade exactly `N`. -/
theorem layerImage_norm_lower {d N : ℕ} (a : LayerIndex d N) :
    ((25 * Real.pi^2)^d * (2 : ℝ)^(2*N))⁻¹ ≤
      ‖integerTwoTensorL2 (layerSource a)‖ := by
  change ((25 * Real.pi^2)^d * (2 : ℝ)^(2*N))⁻¹ ≤
    ‖integerTwoTensorL2
      (integerTwoFixedProfileSource (layerIndexDepth a) a.2)‖
  apply integerTwoFixedProfile_image_norm_lower
  have h := layerIndexDepth_grade a
  simpa [layerIndexDepth, Finsupp.sum_fintype] using h

end BrownianSharp.AlignmentIntegerTwoLayerFrame
