import BrownianSharp.AlignmentFractionalTensorOperator
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BrownianSharp.AlignmentCompactFeatureBall
variable {α H : Type*} [MetricSpace α] [CompactSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def featurePath (K : C(α,H)) (g : H) : C(α,ℝ) :=
  ⟨fun x => ⟪g,K x⟫, continuous_const.inner K.continuous⟩

def featureBall (K : C(α,H)) : Set C(α,ℝ) :=
  {f | ∃ g : H, ‖g‖≤1 ∧ featurePath K g=f}

def dualPath (K : C(α,H)) (φ : WeakDual ℝ H) : C(α,ℝ) :=
  ⟨fun x => φ (K x), φ.toStrongDual.continuous.comp K.continuous⟩

def dualBall : Set (WeakDual ℝ H) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1

theorem featureBall_eq_dual_image (K : C(α,H)) :
    featureBall K = dualPath K '' dualBall := by
  ext f
  constructor
  · rintro ⟨g,hg,rfl⟩
    let φ : WeakDual ℝ H := (InnerProductSpace.toDualMap ℝ H g).toWeakDual
    refine ⟨φ,?_,?_⟩
    · simpa [φ,dualBall,Metric.mem_closedBall,dist_eq_norm] using hg
    · ext x
      change (InnerProductSpace.toDualMap ℝ H g) (K x) = ⟪g,K x⟫
      rw [InnerProductSpace.toDualMap_apply_apply]
  · rintro ⟨φ,hφ,rfl⟩
    let g : H := (InnerProductSpace.toDual ℝ H).symm φ.toStrongDual
    have hg : ‖g‖≤1 := by
      have hφ' : ‖φ.toStrongDual‖≤1 := by
        simpa [dualBall,Metric.mem_closedBall,dist_eq_norm] using hφ
      simpa [g] using hφ'
    refine ⟨g,hg,?_⟩
    ext x
    change ⟪g,K x⟫ = φ (K x)
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

/-- Every continuous Hilbert feature family on a compact parameter space has
a compact uniform-norm image of the Hilbert unit ball. -/
theorem featureBall_isCompact (K : C(α,H)) : IsCompact (featureBall K) := by
  rw [featureBall_eq_dual_image]
  let B : Set (WeakDual ℝ H) := dualBall
  let S := dualPath K '' B
  have hB : IsCompact B := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) 1
  have hEval : Continuous (fun φ : WeakDual ℝ H => fun x : α => φ (K x)) := by
    apply continuous_pi
    intro x
    exact WeakDual.eval_continuous _
  have hpoint : IsCompact (ContinuousMap.toFun '' S) := by
    have himage : ContinuousMap.toFun '' S =
        (fun φ : WeakDual ℝ H => fun x : α => φ (K x)) '' B := by
      ext f
      constructor
      · rintro ⟨u,⟨φ,hφ,rfl⟩,rfl⟩
        exact ⟨φ,hφ,rfl⟩
      · rintro ⟨φ,hφ,rfl⟩
        exact ⟨dualPath K φ,⟨φ,hφ,rfl⟩,rfl⟩
    rw [himage]
    exact hB.image hEval
  have huniform : UniformContinuousOn K Set.univ :=
    isCompact_univ.uniformContinuousOn_of_continuous (continuousOn_univ.mpr K.continuous)
  have hS : Equicontinuous ((↑) : S → α → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hclose⟩ := (Metric.uniformContinuousOn_iff.mp huniform) ε hε
    refine ⟨δ,hδ,?_⟩
    intro y hy f
    rcases f.property with ⟨φ,hφ,hpath⟩
    have hnorm : ‖φ.toStrongDual‖≤1 := by
      simpa [B,dualBall,Metric.mem_closedBall,dist_eq_norm] using hφ
    have hmap : φ (K x)-φ (K y) = φ.toStrongDual (K x-K y) := by simp
    calc
      dist (f.val x) (f.val y) = ‖φ (K x)-φ (K y)‖ := by rw [← hpath]; rfl
      _ = ‖φ.toStrongDual (K x-K y)‖ := by rw [hmap]
      _ ≤ ‖φ.toStrongDual‖*‖K x-K y‖ := φ.toStrongDual.le_opNorm _
      _ ≤ ‖K x-K y‖ := by nlinarith [norm_nonneg (K x-K y)]
      _ = dist (K x) (K y) := (dist_eq_norm _ _).symm
      _ < ε := hclose x (by simp) y (by simp) (by simpa [dist_comm] using hy)
  exact ArzelaAscoli.isCompact_of_equicontinuous S hpoint hS

end BrownianSharp.AlignmentCompactFeatureBall

namespace BrownianSharp.AlignmentFractionalCompactness
open AlignmentFractionalTensorOperator AlignmentCompactFeatureBall

theorem fractionalTensorRL_eq_featurePath {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) (g : CameronMartin.UnitCubeL2 d) :
    fractionalTensorRL a ha g = featurePath (tensorKernelFamily a ha) g := by
  ext t
  change inner ℝ (tensorKernelFamily a ha t) g = inner ℝ g (tensorKernelFamily a ha t)
  exact real_inner_comm _ _

theorem fractionalIntegrationBall_eq_featureBall {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) :
    Latest.fractionalIntegrationBall a = featureBall (tensorKernelFamily a ha) := by
  rw [fractionalIntegrationBall_eq_operator_image a ha]
  ext f
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨g,hg,(fractionalTensorRL_eq_featurePath a ha g).symm⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨g,hg,fractionalTensorRL_eq_featurePath a ha g⟩

/-- The actual tensor RL image unit ball is compact in the uniform norm for
all coordinate orders above one half. -/
theorem fractionalIntegrationBall_isCompact {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) : IsCompact (Latest.fractionalIntegrationBall a) := by
  rw [fractionalIntegrationBall_eq_featureBall a ha]
  exact featureBall_isCompact _

end BrownianSharp.AlignmentFractionalCompactness
