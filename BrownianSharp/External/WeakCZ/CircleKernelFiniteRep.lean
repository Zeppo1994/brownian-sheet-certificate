import BrownianSharp.AlignmentPaperSignedKernelOperator
import BrownianSharp.AlignmentPaperKernelHörmander
import Mathlib.Tactic

/-! Reindex the actual finite signed resolution kernel by a finite set of natural
frequency indices, for the integrated Hörmander estimate. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.External.WeakCZ

open BrownianSharp.AlignmentPaperSignedKernelOperator
open BrownianSharp.AlignmentPaperKernelHörmander
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff

def signedKernelNaturalCoefficients (N : ℕ) (ε : Fin (N+1) → ℝ) : ℕ → ℝ :=
  fun n => if hn : n < N+1 then ε ⟨n, hn⟩ else 0

theorem signedKernelNaturalCoefficients_bound (N : ℕ) (ε : Fin (N+1) → ℝ)
    (hε : ∀ s, |ε s| ≤ 1) :
    ∀ n ∈ Finset.range (N+1), |signedKernelNaturalCoefficients N ε n| ≤ 1 := by
  intro n hn
  have hn' : n < N+1 := Finset.mem_range.mp hn
  simp [signedKernelNaturalCoefficients, hn', hε ⟨n, hn'⟩]

theorem circleSignedKernelDifference_eq_actual (N : ℕ) (ε : Fin (N+1) → ℝ)
    (h : ℝ) (x : UnitAddCircle) :
    circleSignedKernelDifference (Finset.range (N+1))
      (signedKernelNaturalCoefficients N ε) h x =
      circleSignedKernel N ε (x + (h:UnitAddCircle)) - circleSignedKernel N ε x := by
  classical
  have hblock (z : UnitAddCircle) :
      circleSignedKernel N ε z =
        ∑ n ∈ Finset.range (N+1),
          (signedKernelNaturalCoefficients N ε n : ℂ) *
            scalarBlockKernel smoothResolutionCutoff n z := by
    rw [circleSignedKernel]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
    calc
      (∑ s : Fin (N+1), (ε s : ℂ) *
          scalarBlockKernel smoothResolutionCutoff s.val z) =
        ∑ s : Fin (N+1), (signedKernelNaturalCoefficients N ε s.val : ℂ) *
          scalarBlockKernel smoothResolutionCutoff s.val z := by
            apply Finset.sum_congr rfl
            intro s hs
            have hval : s.val < N+1 := s.isLt
            simp [signedKernelNaturalCoefficients, hval]
      _ = ∑ n ∈ Finset.range (N+1),
          (signedKernelNaturalCoefficients N ε n : ℂ) *
            scalarBlockKernel smoothResolutionCutoff n z :=
        Fin.sum_univ_eq_sum_range
          (fun n : ℕ => (signedKernelNaturalCoefficients N ε n : ℂ) *
            scalarBlockKernel smoothResolutionCutoff n z) (N+1)
  rw [circleSignedKernelDifference]
  calc
    (∑ n ∈ Finset.range (N+1),
        (signedKernelNaturalCoefficients N ε n : ℂ) *
          (scalarBlockKernel smoothResolutionCutoff n (x + (h:UnitAddCircle)) -
            scalarBlockKernel smoothResolutionCutoff n x))
        = (∑ n ∈ Finset.range (N+1),
            (signedKernelNaturalCoefficients N ε n : ℂ) *
              scalarBlockKernel smoothResolutionCutoff n (x + (h:UnitAddCircle))) -
          (∑ n ∈ Finset.range (N+1),
            (signedKernelNaturalCoefficients N ε n : ℂ) *
              scalarBlockKernel smoothResolutionCutoff n x) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
    _ = circleSignedKernel N ε (x + (h:UnitAddCircle)) - circleSignedKernel N ε x := by
          rw [← hblock (x + (h:UnitAddCircle)), ← hblock x]

end BrownianSharp.External.WeakCZ
