import BrownianSharp.AlignmentIntegerTwoLayerFrame
import Mathlib.Tactic

/-! Generic tensorization of a globally orthonormal scalar multiscale frame.
The only operator-specific input is its exact factorization on product vectors. -/

noncomputable section
open scoped RealInnerProductSpace BigOperators

namespace BrownianSharp.AlignmentGenericSelectedLayerFrame

open BrownianSharp
open BrownianSharp.AlignmentIntegerTwoLayerFrame
open BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame
open BrownianSharp.AlignmentIntegerTwoTensorEnergy
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentSigmaFiniteL2Tensor

/-- Tensor source indexed by the native grade-`N` layer, assembled from any
global scalar frame indexed by the dyadic selected addresses. -/
def selectedLayerSource {d N : ℕ} (F : SelectedIndex → UnitL2)
    (a : LayerIndex d N) : CameronMartin.UnitCubeL2 d :=
  productToCube d (productVector (fun i => F (layerAxisIndex a i)))

/-- Product-vector norms factor across coordinates in the unit cube L² space. -/
theorem productToCube_norm_sq {d : ℕ} (v : Fin d → UnitL2) :
    ‖productToCube d (productVector v)‖^2 = ∏ i : Fin d, ‖v i‖^2 := by
  rw [← real_inner_self_eq_norm_sq, productToCube_inner_product]
  simp_rw [← real_inner_self_eq_norm_sq]

/-- A globally orthonormal scalar family induces an orthonormal family on
each tensor `LayerIndex`. -/
theorem selectedLayerSource_orthonormal {d N : ℕ}
    (F : SelectedIndex → UnitL2) (hF : Orthonormal ℝ F) :
    Orthonormal ℝ (selectedLayerSource (d:=d) (N:=N) F) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  change inner ℝ
    (productToCube d (productVector (fun i => F (layerAxisIndex a i))))
    (productToCube d (productVector (fun i => F (layerAxisIndex b i)))) = _
  rw [productToCube_inner_product]
  simp_rw [orthonormal_iff_ite.mp hF]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := exists_layerAxisIndex_ne hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The factorized tensor map sends distinct tensor-layer sources to
orthogonal target vectors, provided the scalar frame images are globally
orthogonal. -/
theorem selectedLayerImage_pairwise_orthogonal {d N : ℕ}
    (F : SelectedIndex → UnitL2) (A : UnitL2 →L[ℝ] UnitL2)
    (T : CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d)
    (hfactor : ∀ v : Fin d → UnitL2,
      T (productToCube d (productVector v)) =
        productToCube d (productVector (fun i => A (v i))))
    (himage : ∀ x y : SelectedIndex, x ≠ y →
      inner ℝ (A (F x)) (A (F y)) = 0) :
    ∀ a b : LayerIndex d N, a ≠ b →
      inner ℝ (T (selectedLayerSource (d:=d) (N:=N) F a))
        (T (selectedLayerSource (d:=d) (N:=N) F b)) = 0 := by
  intro a b hab
  obtain ⟨i, hi⟩ := exists_layerAxisIndex_ne hab
  change inner ℝ
    (T (productToCube d (productVector (fun i => F (layerAxisIndex a i)))))
    (T (productToCube d (productVector (fun i => F (layerAxisIndex b i))))) = 0
  rw [hfactor, hfactor, productToCube_inner_product]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (himage _ _ hi)

/-- Factorized target norms are the product of the coordinate norms. -/
theorem selectedLayerImage_norm_sq {d N : ℕ}
    (F : SelectedIndex → UnitL2) (A : UnitL2 →L[ℝ] UnitL2)
    (T : CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d)
    (hfactor : ∀ v : Fin d → UnitL2,
      T (productToCube d (productVector v)) =
        productToCube d (productVector (fun i => A (v i))))
    (a : LayerIndex d N) :
    ‖T (selectedLayerSource (d:=d) (N:=N) F a)‖^2 =
      ∏ i : Fin d, ‖A (F (layerAxisIndex a i))‖^2 := by
  change ‖T (productToCube d (productVector
    (fun i => F (layerAxisIndex a i))))‖^2 = _
  rw [hfactor, productToCube_norm_sq]

/-- If every scalar image has lower norm `c * ρ^s`, the tensor layer image
has lower norm `c^d * ρ^N`. This form specializes to `ρ=2^{-r}`. -/
theorem selectedLayerImage_norm_lower {d N : ℕ}
    (F : SelectedIndex → UnitL2) (A : UnitL2 →L[ℝ] UnitL2)
    (T : CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d)
    (hfactor : ∀ v : Fin d → UnitL2,
      T (productToCube d (productVector v)) =
        productToCube d (productVector (fun i => A (v i))))
    (c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hlower : ∀ s : ℕ, ∀ j : Fin (2^s),
      c * ρ^s ≤ ‖A (F ⟨s,j⟩)‖)
    (a : LayerIndex d N) :
    c^d * ρ^N ≤ ‖T (selectedLayerSource (d:=d) (N:=N) F a)‖ := by
  have hprod :
      ∏ i : Fin d, (c * ρ^(layerIndexDepth a i))^2 ≤
        ∏ i : Fin d, ‖A (F (layerAxisIndex a i))‖^2 := by
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).2
      exact hlower (layerIndexDepth a i) (a.2 i)
  have hbase :
      ∏ i : Fin d, (c * ρ^(layerIndexDepth a i))^2 =
        (c^d * ρ^N)^2 := by
    rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_pow_eq_pow_sum]
    rw [show (∑ i : Fin d, layerIndexDepth a i) = N by
      have h := layerIndexDepth_grade a
      simpa [layerIndexDepth, Finsupp.sum_fintype] using h]
    simp [pow_mul, mul_pow]
  have hnormsq := selectedLayerImage_norm_sq F A T hfactor a
  have hsq : (c^d * ρ^N)^2 ≤
      ‖T (selectedLayerSource (d:=d) (N:=N) F a)‖^2 := by
    calc
      (c^d * ρ^N)^2 = ∏ i : Fin d, (c * ρ^(layerIndexDepth a i))^2 := hbase.symm
      _ ≤ ∏ i : Fin d, ‖A (F (layerAxisIndex a i))‖^2 := hprod
      _ = ‖T (selectedLayerSource (d:=d) (N:=N) F a)‖^2 := hnormsq.symm
  have htarget : 0 ≤ ‖T (selectedLayerSource (d:=d) (N:=N) F a)‖ := norm_nonneg _
  have hbase_nonneg : 0 ≤ c^d * ρ^N := by positivity
  exact (sq_le_sq₀ hbase_nonneg htarget).1 hsq

end BrownianSharp.AlignmentGenericSelectedLayerFrame
