import BrownianSharp.SmoothAtom
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Compact support and strictly positive spatial energy of the actual atom. -/
open MeasureTheory
namespace BrownianSharp

theorem smoothAtom_hasCompactSupport : HasCompactSupport smoothAtom := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  have houtside : x ≤ 0 ∨ 1 ≤ x := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl hx.le
    · exact Or.inr hx.le
  exact smoothAtom_support x houtside

end BrownianSharp
