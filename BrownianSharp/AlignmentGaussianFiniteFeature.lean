import BrownianSharp.AlignmentGaussianChainingRate
import BrownianSharp.GaussianRows

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators NNReal
namespace BrownianSharp.AlignmentGaussianFiniteFeature
open AlignmentGaussianChaining AlignmentGaussianChainingRate

def finiteGaussianFeaturePath {α ι : Type*} [TopologicalSpace α] [CompactSpace α]
    [Fintype ι] (v : ι→C(α,ℝ)) (z : ι→ℝ) : C(α,ℝ) := ∑i,z i • v i

theorem finiteGaussianFeaturePath_apply {α ι : Type*}
    [TopologicalSpace α] [CompactSpace α] [Fintype ι]
    (v : ι→C(α,ℝ)) (z : ι→ℝ) (x : α) :
    finiteGaussianFeaturePath v z x=∑i,z i*v i x := by
  simp [finiteGaussianFeaturePath]

theorem finiteGaussianFeaturePath_continuous {α ι : Type*}
    [TopologicalSpace α] [CompactSpace α] [Fintype ι]
    (v : ι→C(α,ℝ)) : Continuous (finiteGaussianFeaturePath v) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).smul continuous_const

private theorem productCoordinates_independent (ι : Type*) [Fintype ι] :
    iIndepFun (fun i : ι=>fun z : ι→ℝ=>z i) (productStandardGaussian ι) := by
  exact iIndepFun_pi (fun _=>aemeasurable_id)

theorem finiteGaussianFeaturePath_eval_hasLaw {α ι : Type*}
    [TopologicalSpace α] [CompactSpace α] [Fintype ι]
    (v : ι→C(α,ℝ)) (x : α) :
    HasLaw (fun z=>finiteGaussianFeaturePath v z x)
      (gaussianReal 0 (∑i,(v i x)^2).toNNReal) (productStandardGaussian ι) := by
  have heq : (fun z=>finiteGaussianFeaturePath v z x)=
      GaussianRows.row (fun i : ι=>fun z : ι→ℝ=>z i) (fun i=>v i x) := by
    funext z
    simp only [finiteGaussianFeaturePath_apply,GaussianRows.row]
    exact Finset.sum_congr rfl (fun i _=>mul_comm _ _)
  rw [heq]
  exact ⟨by apply Measurable.aemeasurable; unfold GaussianRows.row; fun_prop,
    GaussianRows.row_law _ (fun i=>measurable_pi_apply i)
      (fun i=>productStandardGaussian_coordinate_law i)
      (productCoordinates_independent ι) _⟩

theorem finiteGaussianFeaturePath_increment_hasLaw {α ι : Type*}
    [TopologicalSpace α] [CompactSpace α] [Fintype ι]
    (v : ι→C(α,ℝ)) (x y : α) :
    HasLaw (fun z=>finiteGaussianFeaturePath v z x-finiteGaussianFeaturePath v z y)
      (gaussianReal 0 (∑i,(v i x-v i y)^2).toNNReal) (productStandardGaussian ι) := by
  have heq : (fun z=>finiteGaussianFeaturePath v z x-finiteGaussianFeaturePath v z y)=
      GaussianRows.row (fun i : ι=>fun z : ι→ℝ=>z i) (fun i=>v i x-v i y) := by
    funext z
    simp only [finiteGaussianFeaturePath_apply,GaussianRows.row,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  exact ⟨by apply Measurable.aemeasurable; unfold GaussianRows.row; fun_prop,
    GaussianRows.row_law _ (fun i=>measurable_pi_apply i)
      (fun i=>productStandardGaussian_coordinate_law i)
      (productCoordinates_independent ι) _⟩

/-- Expected continuum norm of an actual finite Gaussian feature field.
Both hypotheses concern its explicit deterministic feature coefficients. -/
theorem finiteGaussianFeaturePath_expected_norm
    {d : ℕ} {ι : Type*} [Fintype ι]
    (v : ι→C(BrownianCubeAnchor d,ℝ)) (σ R : ℝ) (hσ : 0≤σ) (hR : 0≤R)
    (hvar : ∀x,∑i,(v i x)^2≤σ^2)
    (hincrement : ∀x y,∑i,(v i x-v i y)^2≤R*dist x y) (n₀ : ℕ) :
    Integrable (fun z=>‖finiteGaussianFeaturePath v z‖) (productStandardGaussian ι) ∧
      (∫z,‖finiteGaussianFeaturePath v z‖ ∂productStandardGaussian ι)≤
        chainingConstant d*Real.sqrt ((n₀:ℝ)+1)*
          (σ+Real.sqrt (2*R)*(2:ℝ)^(-((n₀:ℝ)/2))) := by
  let vp : BrownianCubeAnchor d→ℝ≥0 := fun x=>(∑i,(v i x)^2).toNNReal
  let vi : (N : ℕ)→CubeNearPairs d N→ℝ≥0 := fun _ p=>
    (∑i,(v i (cubeDyadicAnchor p.val.2)-v i (cubeDyadicAnchor p.val.1))^2).toNNReal
  apply gaussian_chaining_expected_norm (productStandardGaussian ι)
    (finiteGaussianFeaturePath v) (finiteGaussianFeaturePath_continuous v).measurable
    vp vi (finiteGaussianFeaturePath_eval_hasLaw v)
    (fun _ p=>finiteGaussianFeaturePath_increment_hasLaw v _ _) σ (Real.sqrt (2*R)) hσ
    (Real.sqrt_nonneg _)
  · intro x
    simpa only [vp,Real.coe_toNNReal _ (Finset.sum_nonneg (fun _ _=>sq_nonneg _))] using hvar x
  · intro N p
    have h := nearPair_variance_bound R hR
      (fun x y=>∑i,(v i x-v i y)^2) hincrement p
    simpa only [vi,Real.coe_toNNReal _ (Finset.sum_nonneg (fun _ _=>sq_nonneg _))] using h

end BrownianSharp.AlignmentGaussianFiniteFeature
