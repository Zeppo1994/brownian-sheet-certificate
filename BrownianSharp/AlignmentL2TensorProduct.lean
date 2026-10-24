import BrownianSharp.AlignmentFractionalTensor
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentL2TensorProduct
open AlignmentFractionalTensor
variable {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ} [∀ i, IsFiniteMeasure (μ i)]

def productVector (v : ∀ i, Lp ℝ 2 (μ i)) : Lp ℝ 2 (Measure.pi μ) :=
  piProductLp (fun i x => v i x) (fun i => Lp.memLp (v i))

theorem productVector_ae (v : ∀ i, Lp ℝ 2 (μ i)) :
    productVector v =ᵐ[Measure.pi μ] (fun u => ∏ i, v i (u i)) :=
  (memLp_pi_product _ (fun i => Lp.memLp (v i))).coeFn_toLp

theorem productVector_norm (v : ∀ i, Lp ℝ 2 (μ i)) :
    ‖productVector v‖ = ∏ i, ‖v i‖ := by
  have h := piProductLp_norm_sq (fun i x => v i x) (fun i => Lp.memLp (v i))
  have heq : ∀ i, (Lp.memLp (v i)).toLp (fun x => v i x) = v i := by
    intro i
    apply Lp.ext
    exact (Lp.memLp (v i)).coeFn_toLp
  simp_rw [heq, Finset.prod_pow] at h
  have hp : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun i hi => norm_nonneg _
  change ‖productVector v‖^2 = (∏ i, ‖v i‖)^2 at h
  nlinarith [norm_nonneg (productVector v)]

theorem product_update_eval [DecidableEq ι] (v : ∀ i, Lp ℝ 2 (μ i))
    (i : ι) (x : Lp ℝ 2 (μ i)) (u : ι → ℝ) :
    (∏ j, (Function.update v i x j) (u j)) =
      x (u i) * ∏ j ∈ Finset.univ \ {i}, v j (u j) := by
  have heq : (fun j => (Function.update v i x j) (u j)) =
      Function.update (fun j => v j (u j)) i (x (u i)) := by
    funext j
    by_cases h : j=i
    · subst j
      simp
    · simp [Function.update, h]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i)]

def tensorMultilinear [DecidableEq ι] :
    MultilinearMap ℝ (fun i => Lp ℝ 2 (μ i)) (Lp ℝ 2 (Measure.pi μ)) where
  toFun := productVector
  map_update_add' v i x y := by
    apply Lp.ext
    have hxy : ∀ᵐ u ∂Measure.pi μ, (x+y) (u i) = x (u i)+y (u i) :=
      Measure.tendsto_eval_ae_ae.eventually (Lp.coeFn_add x y)
    filter_upwards [productVector_ae (Function.update v i (x+y)),
      Lp.coeFn_add (productVector (Function.update v i x))
        (productVector (Function.update v i y)),
      productVector_ae (Function.update v i x),
      productVector_ae (Function.update v i y), hxy] with u h0 ha h1 h2 hxy
    rw [h0, ha]
    simp only [Pi.add_apply]
    rw [h1, h2, product_update_eval, product_update_eval, product_update_eval, hxy]
    ring
  map_update_smul' v i c x := by
    apply Lp.ext
    have hcx : ∀ᵐ u ∂Measure.pi μ, (c • x) (u i) = c • x (u i) :=
      Measure.tendsto_eval_ae_ae.eventually (Lp.coeFn_smul c x)
    filter_upwards [productVector_ae (Function.update v i (c • x)),
      Lp.coeFn_smul c (productVector (Function.update v i x)),
      productVector_ae (Function.update v i x), hcx] with u h0 ha h1 hcx
    rw [h0, ha]
    simp only [Pi.smul_apply]
    rw [h1, product_update_eval, product_update_eval, hcx]
    simp only [smul_eq_mul]
    ring

/-- The elementary tensor map has norm one (or less in degenerate cases),
with no extra dimension constant. -/
def tensorContinuous [DecidableEq ι] :
    ContinuousMultilinearMap ℝ (fun i => Lp ℝ 2 (μ i)) (Lp ℝ 2 (Measure.pi μ)) :=
  tensorMultilinear.mkContinuous 1 (fun v => by simpa [tensorMultilinear] using
    (le_of_eq (productVector_norm v)))

theorem tensorContinuous_apply [DecidableEq ι] (v : ∀ i, Lp ℝ 2 (μ i)) :
    tensorContinuous v = productVector v := rfl

end BrownianSharp.AlignmentL2TensorProduct
