import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.NNReal.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators NNReal

namespace BrownianSharp.AlignmentPaperJointGradeCoverConcatenation

/-- Concatenate the low-grade slots `0,…,N` and the high-grade slots
`N+1,…,N+W` in one `Fin (N+1+W)` family. -/
def concatGradeFamily {N W : ℕ} {α : Type*}
    (low : Fin (N+1) → α) (high : Fin W → α) : Fin (N+1+W) → α :=
  Fin.addCases low high

/-- Concatenate a low/high family of target radii. -/
def concatGradeRadius {N W : ℕ}
    (low : Fin (N+1) → ℝ≥0) (high : Fin W → ℝ≥0) : Fin (N+1+W) → ℝ≥0 :=
  concatGradeFamily low high

/-- Concatenate a low/high family of integer bit budgets. -/
def concatGradeBits {N W : ℕ}
    (low : Fin (N+1) → ℕ) (high : Fin W → ℕ) : Fin (N+1+W) → ℕ :=
  concatGradeFamily low high

@[simp] theorem concatGradeFamily_castAdd {N W : ℕ} {α : Type*}
    (low : Fin (N+1) → α) (high : Fin W → α) (i : Fin (N+1)) :
    concatGradeFamily low high (Fin.castAdd W i) = low i := by
  simp [concatGradeFamily]

@[simp] theorem concatGradeFamily_natAdd {N W : ℕ} {α : Type*}
    (low : Fin (N+1) → α) (high : Fin W → α) (j : Fin W) :
    concatGradeFamily low high (Fin.natAdd (N+1) j) = high j := by
  simp [concatGradeFamily]

@[simp] theorem concatGradeIndex_castAdd {N W : ℕ} (i : Fin (N+1)) :
    (Fin.castAdd W i).val = i.val := by simp

@[simp] theorem concatGradeIndex_natAdd {N W : ℕ} (j : Fin W) :
    (Fin.natAdd (N+1) j).val = N+1+j.val := by simp

/-- Cover the grade indexed by every slot after concatenating the two windows. -/
theorem concatGradeFamily_isCover {N W : ℕ} {X : Type*} [PseudoMetricSpace X]
    (source : ℕ → Set X)
    (low : Fin (N+1) → Set X) (high : Fin W → Set X)
    (lowR : Fin (N+1) → ℝ≥0) (highR : Fin W → ℝ≥0)
    (hlow : ∀ i, Metric.IsCover (lowR i) (source i.val) (low i))
    (hhigh : ∀ j, Metric.IsCover (highR j)
      (source (N+1+j.val)) (high j)) :
    ∀ k : Fin (N+1+W),
      Metric.IsCover (concatGradeRadius lowR highR k)
        (source k.val) (concatGradeFamily low high k) := by
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simpa [concatGradeRadius, concatGradeFamily] using hlow i
  · intro j
    simpa [concatGradeRadius, concatGradeFamily] using hhigh j

/-- Finiteness is preserved slotwise by concatenation. -/
theorem concatGradeFamily_finite {N W : ℕ} {α : Type*}
    (low : Fin (N+1) → Set α) (high : Fin W → Set α)
    (hlow : ∀ i, (low i).Finite) (hhigh : ∀ j, (high j).Finite) :
    ∀ k : Fin (N+1+W), (concatGradeFamily low high k).Finite := by
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simpa [concatGradeFamily] using hlow i
  · intro j
    simpa [concatGradeFamily] using hhigh j

/-- Exact radius-sum identity for the combined finite grade window. -/
theorem concatGradeRadius_sum {N W : ℕ}
    (low : Fin (N+1) → ℝ≥0) (high : Fin W → ℝ≥0) :
    (∑ k : Fin (N+1+W), concatGradeRadius low high k) =
      (∑ i : Fin (N+1), low i) + ∑ j : Fin W, high j := by
  simp [concatGradeRadius, concatGradeFamily, Fin.sum_univ_add]

/-- Exact bit-budget sum identity for the combined finite grade window. -/
theorem concatGradeBits_sum {N W : ℕ}
    (low : Fin (N+1) → ℕ) (high : Fin W → ℕ) :
    (∑ k : Fin (N+1+W), concatGradeBits low high k) =
      (∑ i : Fin (N+1), low i) + ∑ j : Fin W, high j := by
  simp [concatGradeBits, concatGradeFamily, Fin.sum_univ_add]

end BrownianSharp.AlignmentPaperJointGradeCoverConcatenation
