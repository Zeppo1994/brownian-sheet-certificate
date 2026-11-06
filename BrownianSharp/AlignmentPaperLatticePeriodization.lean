import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

noncomputable section
namespace BrownianSharp.AlignmentPaperLatticePeriodization

def latticeSum (f : ℝ → ℝ) (ξ : ℝ) : ℝ := ∑' k : ℤ, f ((k : ℝ) - ξ)

theorem latticeSum_add_int (f : ℝ → ℝ) (ξ : ℝ) (n : ℤ) :
    latticeSum f (ξ + n) = latticeSum f ξ := by
  unfold latticeSum
  calc
    (∑' k : ℤ, f ((k : ℝ) - (ξ + n))) =
        ∑' k : ℤ, f (((k+n : ℤ) : ℝ) - (ξ+n)) :=
      ((Equiv.addRight n).tsum_eq (fun k : ℤ => f ((k : ℝ) - (ξ+n)))).symm
    _ = ∑' k : ℤ, f ((k : ℝ) - ξ) := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring

theorem latticeSum_eq_fractional_part (f : ℝ → ℝ) (ξ : ℝ) :
    latticeSum f ξ = latticeSum f (Int.fract ξ) := by
  have hξ : ξ = Int.fract ξ + (⌊ξ⌋ : ℤ) := by
    rw [Int.fract]
    ring
  calc
    latticeSum f ξ = latticeSum f (Int.fract ξ + (⌊ξ⌋ : ℤ)) :=
      congrArg (latticeSum f) hξ
    _ = _ := latticeSum_add_int f (Int.fract ξ) ⌊ξ⌋

theorem latticeSum_uniform_bound (f : ℝ → ℝ) (C : ℝ)
    (hC : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, latticeSum f ξ ≤ C) :
    ∀ ξ : ℝ, latticeSum f ξ ≤ C := by
  intro ξ
  rw [latticeSum_eq_fractional_part]
  exact hC (Int.fract ξ) ⟨Int.fract_nonneg ξ, (Int.fract_lt_one ξ).le⟩

theorem lattice_summable_add_int (f : ℝ → ℝ) (ξ : ℝ) (n : ℤ)
    (h : Summable (fun k : ℤ => f ((k : ℝ) - ξ))) :
    Summable (fun k : ℤ => f ((k : ℝ) - (ξ + n))) := by
  apply (Equiv.addRight n).summable_iff.mp
  change Summable (fun k : ℤ => f (((k+n : ℤ) : ℝ) - (ξ+n)))
  have heq : (fun k : ℤ => f (((k+n : ℤ) : ℝ) - (ξ+n))) =
      (fun k : ℤ => f ((k : ℝ)-ξ)) := by
    funext k
    congr 1
    push_cast
    ring
  rw [heq]
  exact h

theorem lattice_summable_of_fundamental (f : ℝ → ℝ)
    (h : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, Summable (fun k : ℤ => f ((k : ℝ) - ξ))) :
    ∀ ξ : ℝ, Summable (fun k : ℤ => f ((k : ℝ) - ξ)) := by
  intro ξ
  have hξ : ξ = Int.fract ξ + (⌊ξ⌋ : ℤ) := by
    rw [Int.fract]
    ring
  rw [hξ]
  exact lattice_summable_add_int f _ _ (h (Int.fract ξ)
    ⟨Int.fract_nonneg ξ, (Int.fract_lt_one ξ).le⟩)

end BrownianSharp.AlignmentPaperLatticePeriodization
