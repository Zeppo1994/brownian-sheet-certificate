import BrownianSharp.AlignmentFractionalL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Elementary L² tensors on arbitrary sigma-finite real source measures.
This includes the whole-line Mandelbrot--van Ness source. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentSigmaFiniteL2Tensor

theorem memLp_pi_product {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun u : ι → ℝ => ∏ i, f i (u i)) 2 (Measure.pi μ) := by
  have hmeas : AEStronglyMeasurable (fun u : ι → ℝ => ∏ i, f i (u i)) (Measure.pi μ) := by
    exact Finset.aestronglyMeasurable_fun_prod Finset.univ (fun i hi =>
      (hf i).aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval μ i))
  have hsq : ∀ i, Integrable (fun x => (f i x)^2) (μ i) := fun i =>
    (memLp_two_iff_integrable_sq (hf i).aestronglyMeasurable).mp (hf i)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  simpa only [Finset.prod_pow] using Integrable.fintype_prod hsq

theorem realLp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : Lp ℝ 2 μ) : ‖g‖^2 = ∫ u, (g u)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext u
  simp [pow_two]

def piProductLp {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    Lp ℝ 2 (Measure.pi μ) :=
  (memLp_pi_product f hf).toLp (fun u => ∏ i, f i (u i))

theorem piProductLp_norm_sq {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    ‖piProductLp f hf‖^2 = ∏ i, ‖(hf i).toLp (f i)‖^2 := by
  rw [realLp_norm_sq]
  have hae := (memLp_pi_product f hf).coeFn_toLp
  change ∫ u, ((memLp_pi_product f hf).toLp (fun u => ∏ i, f i (u i)) u)^2
      ∂Measure.pi μ = _
  rw [integral_congr_ae (hae.mono (fun u hu => congrArg (fun x : ℝ => x^2) hu))]
  simp_rw [← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (fun i x => (f i x)^2)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [realLp_norm_sq]
  exact integral_congr_ae ((hf i).coeFn_toLp.mono (fun u hu =>
    congrArg (fun x : ℝ => x^2) hu.symm))

variable {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ} [∀ i, SigmaFinite (μ i)]

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

theorem productVector_inner (v w : ∀ i, Lp ℝ 2 (μ i)) :
    ⟪productVector v, productVector w⟫ = ∏ i, ⟪v i, w i⟫ := by
  rw [L2.inner_def]
  calc
    _ = ∫ u, ∏ i, (v i (u i) * w i (u i)) ∂Measure.pi μ := by
      apply integral_congr_ae
      filter_upwards [productVector_ae v, productVector_ae w] with u hv hw
      simp only [Real.inner_apply, hv, hw, Finset.prod_mul_distrib]
    _ = ∏ i, ∫ x, v i x * w i x ∂μ i :=
      integral_fintype_prod_eq_prod (fun i x => v i x * w i x)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with u
      simp [Real.inner_apply, mul_comm]

theorem productVector_orthonormal {κ : ι → Type*}
    (e : ∀ i, κ i → Lp ℝ 2 (μ i)) (he : ∀ i, Orthonormal ℝ (e i)) :
    Orthonormal ℝ (fun a : ∀ i, κ i => productVector (fun i => e i (a i))) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [productVector_inner]
  simp_rw [fun i => (orthonormal_iff_ite.mp (he i)) (a i) (b i)]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    have hne : ∃ i, a i ≠ b i := by
      by_contra hn
      push_neg at hn
      exact hab (funext hn)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end BrownianSharp.AlignmentSigmaFiniteL2Tensor
