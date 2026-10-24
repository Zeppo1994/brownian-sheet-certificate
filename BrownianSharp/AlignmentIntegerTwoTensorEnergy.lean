import BrownianSharp.AlignmentIntegerFractionalApproximationLower
import BrownianSharp.AlignmentFractionalTensorL2Semigroup
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentSigmaFiniteL2Tensor
import BrownianSharp.AlignmentHilbertOrthogonalEnergy
import BrownianSharp.LayerIndex
import BrownianSharp.AlignmentIntegerTwoSelectedBlock
import Mathlib.Tactic

/-! Tensor products of the selected scalar order-two RL singular vectors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentIntegerTwoTensorEnergy

open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentSigmaFiniteL2Tensor
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentIntegerTwoSelectedBlock
open BrownianSharp

theorem productToCube_inner_product {d : ℕ} (v w : Fin d → UnitL2) :
    inner ℝ (productToCube d (productVector v)) (productToCube d (productVector w)) =
      ∏ i : Fin d, inner ℝ (v i) (w i) := by
  rw [L2.inner_def]
  simp_rw [Real.inner_apply]
  change (∫ x, productToCube d (productVector v) x *
      productToCube d (productVector w) x ∂
      ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d))) = _
  have hv := productToCube_ae (productVector v)
  have hw := productToCube_ae (productVector w)
  calc
    _ = ∫ x, productVector v x * productVector w x ∂
        ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet d)) := by
      apply integral_congr_ae
      filter_upwards [hv,hw] with x hx hy
      rw [hx,hy]
    _ = inner ℝ (productVector v) (productVector w) := by
      rw [AlignmentFractionalTensor.unitCube_measure_eq_pi]
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp [Real.inner_apply, mul_comm]
    _ = ∏ i : Fin d, inner ℝ (v i) (w i) := by
      exact productVector_inner v w

def integerTwoTensorL2 {d : ℕ} :
    CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d :=
  (cubeProfileToL2 (d:=d)).comp
    (fractionalTensorRL (fun _ : Fin d => 2) (by intro i; norm_num))

theorem integerTwoTensorL2_product {d : ℕ} (v : Fin d → UnitL2) :
    integerTwoTensorL2 (d:=d) (productToCube d (productVector v)) =
      productToCube d (productVector (fun i => integerTwoL2Operator (v i))) := by
  let a : Fin d → ℝ := fun _ => 2
  have hprof : fractionalTensorRL a (by intro i; norm_num)
      (productToCube d (productVector v)) =
        cubeProductProfile (fun i => integerTwoOperator (v i)) := by
    ext t
    change fractionalTensorRL a (by intro i; norm_num)
      (productToCube d (productVector v)) t = _
    calc
      fractionalTensorRL a (by intro i; norm_num)
          (productToCube d (productVector v)) t =
          ∏ i, fractionalRL (a i) (by norm_num) (v i) (cubeCoordinate i t) :=
        fractionalTensorRL_product a (by intro i; norm_num) v t
      _ = cubeProductProfile (fun i => integerTwoOperator (v i)) t := by
        simp [cubeProductProfile, integerTwoOperator, a]
  change cubeProfileToL2 (fractionalTensorRL (fun _ : Fin d => 2)
    (by intro i; norm_num) (productToCube d (productVector v))) = _
  rw [hprof, cubeProfileToL2_cubeProduct]
  rfl

theorem product_frame_orthonormal {d : ℕ} {ι : Fin d → Type*}
    (e : ∀ i, ι i → UnitL2)
    (he : ∀ i, Orthonormal ℝ (e i)) :
    Orthonormal ℝ (fun a : ∀ i, ι i =>
      productToCube d (productVector (fun i => e i (a i)))) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [productToCube_inner_product]
  simp_rw [orthonormal_iff_ite.mp (he _)]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    have hne : ∃ i : Fin d, a i ≠ b i := by
      by_contra hn
      push_neg at hn
      apply hab
      funext i
      exact hn i
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem product_image_orthogonal {d : ℕ} {ι : Fin d → Type*}
    (e : ∀ i, ι i → UnitL2)
    (horth : ∀ i a b, a ≠ b →
      inner ℝ (integerTwoL2Operator (e i a)) (integerTwoL2Operator (e i b)) = 0) :
    ∀ a b : ∀ i, ι i, a ≠ b →
      inner ℝ
        (integerTwoTensorL2 (d:=d)
          (productToCube d (productVector (fun i => e i (a i)))))
        (integerTwoTensorL2 (d:=d)
          (productToCube d (productVector (fun i => e i (b i))))) = 0 := by
  intro a b hab
  rw [integerTwoTensorL2_product, integerTwoTensorL2_product,
    productToCube_inner_product]
  have hne : ∃ i : Fin d, a i ≠ b i := by
    by_contra hn
    push_neg at hn
    apply hab
    funext i
    exact hn i
  obtain ⟨i, hi⟩ := hne
  exact Finset.prod_eq_zero (Finset.mem_univ i) (horth i (a i) (b i) hi)

theorem product_image_norm_sq {d : ℕ} (v : Fin d → UnitL2) :
    ‖integerTwoTensorL2 (d:=d) (productToCube d (productVector v))‖^2 =
      ∏ i : Fin d, ‖integerTwoL2Operator (v i)‖^2 := by
  rw [integerTwoTensorL2_product, ← real_inner_self_eq_norm_sq,
    productToCube_inner_product]
  simp_rw [← real_inner_self_eq_norm_sq]

/-- A tensor product of the selected order-two scalar frames at a fixed
coordinate depth profile. -/
def integerTwoFixedProfileSource {d : ℕ} (s : Fin d → ℕ)
    (a : ∀ i : Fin d, Fin (2 ^ s i)) : CameronMartin.UnitCubeL2 d :=
  productToCube d (productVector (fun i => selectedBlockFrame (s i) (a i)))

theorem integerTwoFixedProfile_orthonormal {d : ℕ} (s : Fin d → ℕ) :
    Orthonormal ℝ (integerTwoFixedProfileSource s) := by
  exact product_frame_orthonormal (fun i => selectedBlockFrame (s i))
    (fun i => selectedBlockFrame_orthonormal (s i))

theorem integerTwoFixedProfile_image_pairwise {d : ℕ} (s : Fin d → ℕ) :
    ∀ a b : ∀ i : Fin d, Fin (2 ^ s i), a ≠ b →
      inner ℝ (integerTwoTensorL2 (integerTwoFixedProfileSource s a))
        (integerTwoTensorL2 (integerTwoFixedProfileSource s b)) = 0 := by
  intro a b hab
  exact product_image_orthogonal (fun i => selectedBlockFrame (s i))
    (fun i a b hab => by
      simpa [integerTwoL2Operator] using
        selectedBlockFrame_image_pairwise (s i) a b hab) a b hab

theorem integerTwoFixedProfile_image_norm_sq {d : ℕ} (s : Fin d → ℕ)
    (a : ∀ i : Fin d, Fin (2 ^ s i)) :
    ‖integerTwoTensorL2 (integerTwoFixedProfileSource s a)‖^2 =
      ∏ i : Fin d, ‖integerTwoL2Operator (selectedBlockFrame (s i) (a i))‖^2 := by
  exact product_image_norm_sq (fun i => selectedBlockFrame (s i) (a i))

theorem integerTwoFixedProfile_image_norm_lower {d N : ℕ} (s : Fin d → ℕ)
    (a : ∀ i : Fin d, Fin (2 ^ s i))
    (hs : ∑ i : Fin d, s i = N) :
    ((25 * Real.pi^2)^d * (2 : ℝ)^(2*N))⁻¹ ≤
      ‖integerTwoTensorL2 (integerTwoFixedProfileSource s a)‖ := by
  have hscalar : ∀ i : Fin d,
      (25 * Real.pi^2 * (2 : ℝ)^(2*s i))⁻¹ ≤
        ‖integerTwoL2Operator (selectedBlockFrame (s i) (a i))‖ := by
    intro i
    change _ ≤ ‖profileToL2 (integerTwoOperator (selectedBlockFrame (s i) (a i)))‖
    exact le_trans (integerTwo_dyadic_block_sigma_lower (s i))
      (selectedBlockFrame_image_norm_lower (s i) (a i))
  have hprod :
      ∏ i : Fin d, ((25 * Real.pi^2 * (2 : ℝ)^(2*s i))⁻¹)^2 ≤
      ∏ i : Fin d, ‖integerTwoL2Operator (selectedBlockFrame (s i) (a i))‖^2 := by
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 (hscalar i)
  have hbase :
      ∏ i : Fin d, (25 * Real.pi^2 * (2 : ℝ)^(2*s i)) =
        (25 * Real.pi^2)^d * (2 : ℝ)^(2*N) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
    rw [← Finset.mul_sum, hs]
    simp
  have hconst :
      ((25 * Real.pi^2)^d * (2 : ℝ)^(2*N))⁻¹^2 =
        ∏ i : Fin d, ((25 * Real.pi^2 * (2 : ℝ)^(2*s i))⁻¹)^2 := by
    calc
      _ = (∏ i : Fin d, (25 * Real.pi^2 * (2 : ℝ)^(2*s i))⁻¹)^2 := by
        rw [Finset.prod_inv_distrib, hbase]
      _ = _ := by rw [Finset.prod_pow]
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).1
  rw [integerTwoFixedProfile_image_norm_sq]
  rw [hconst]
  exact hprod

end BrownianSharp.AlignmentIntegerTwoTensorEnergy
