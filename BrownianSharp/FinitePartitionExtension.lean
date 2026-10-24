import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! Positive finite sampling extensions with operator norm at most one. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp

variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [Fintype ι]

/-- A partition of unity gives a linear extension of finite sampled values. -/
def finitePartitionExtension (ρ : PartitionOfUnity ι X) :
    (ι → ℝ) →ₗ[ℝ] C(X,ℝ) where
  toFun a := ∑ i, a i • ρ i
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum,smul_smul]

@[simp] theorem finitePartitionExtension_apply (ρ : PartitionOfUnity ι X)
    (a : ι → ℝ) (x : X) : finitePartitionExtension ρ a x = ∑ i,a i*ρ i x := by
  simp [finitePartitionExtension,smul_eq_mul]

theorem partition_sum_one (ρ : PartitionOfUnity ι X) (x : X) :
    (∑ i,ρ i x) = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)

/-- Positivity makes the extension a contraction in the uniform norm. -/
theorem finitePartitionExtension_norm_le (ρ : PartitionOfUnity ι X) (a : ι → ℝ) :
    ‖finitePartitionExtension ρ a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  rw [finitePartitionExtension_apply,Real.norm_eq_abs]
  calc
    _ ≤ ∑ i,|a i * ρ i x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i,|a i| * ρ i x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul,abs_of_nonneg (ρ.nonneg i x)]
    _ ≤ ∑ i,‖a‖ * ρ i x := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm a i) (ρ.nonneg i x)
    _ = ‖a‖ := by rw [← Finset.mul_sum,partition_sum_one, mul_one]

/-- Local oscillation on the supports bounds the actual interpolation error. -/
theorem finitePartitionExtension_approx (ρ : PartitionOfUnity ι X)
    (p : ι → X) (f : C(X,ℝ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hlocal : ∀ i x, ρ i x ≠ 0 → |f x-f (p i)| ≤ ε) :
    ‖f-finitePartitionExtension ρ (fun i => f (p i))‖ ≤ ε := by
  apply (ContinuousMap.norm_le _ hε).2
  intro x
  have heq : f x-finitePartitionExtension ρ (fun i => f (p i)) x =
      ∑ i,ρ i x*(f x-f (p i)) := by
    simp only [finitePartitionExtension,LinearMap.coe_mk,AddHom.coe_mk,
      ContinuousMap.coe_sum,ContinuousMap.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,partition_sum_one]
    simp only [one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change |f x-finitePartitionExtension ρ (fun i => f (p i)) x| ≤ ε
  rw [heq]
  calc
    _ ≤ ∑ i,|ρ i x*(f x-f (p i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,ρ i x*ε := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (ρ.nonneg i x)]
      by_cases hz : ρ i x=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hlocal i x hz) (ρ.nonneg i x)
    _ = ε := by rw [← Finset.sum_mul,partition_sum_one,one_mul]

end BrownianSharp
