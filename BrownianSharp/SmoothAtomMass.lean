import BrownianSharp.SmoothAtom
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Compact support and strictly positive spatial energy of the actual atom. -/
open MeasureTheory
namespace BrownianSharp

/-- The support is compactly contained in the open interval, as required
by the manuscript's C∞_c(0,1) atom convention. -/
theorem smoothAtom_tsupport_subset_inner :
    tsupport smoothAtom ⊆ Set.Icc (1 / 8 : ℝ) (7 / 8) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hn : smoothAtom x ≠ 0 := hx
  constructor
  · by_contra h
    exact hn (smoothAtom_support_inner x (Or.inl (le_of_not_ge h)))
  · by_contra h
    exact hn (smoothAtom_support_inner x (Or.inr (le_of_not_ge h)))

theorem smoothAtom_tsupport_subset_unit_open : tsupport smoothAtom ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  have h := smoothAtom_tsupport_subset_inner hx
  constructor <;> linarith [h.1, h.2]

theorem smoothAtom_hasCompactSupport : HasCompactSupport smoothAtom := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  have houtside : x ≤ 0 ∨ 1 ≤ x := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl hx.le
    · exact Or.inr hx.le
  exact smoothAtom_support x houtside

theorem smoothAtom_sq_integrable : Integrable (fun x : ℝ => smoothAtom x ^ 2) :=
  (smoothAtom_contDiff.continuous.pow 2).integrable_of_hasCompactSupport
    (by simpa [pow_two] using
      (smoothAtom_hasCompactSupport.mul_right : HasCompactSupport (smoothAtom * smoothAtom)))

theorem smoothAtom_sq_integral_pos : 0 < ∫ x : ℝ, smoothAtom x ^ 2 := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (smoothAtom_contDiff.continuous.pow 2) smoothAtom_sq_integrable
    (fun x => sq_nonneg _) (x := (1 / 2 : ℝ))
  exact pow_ne_zero 2 smoothAtom_nonzero

theorem smoothAtom_sq_integral_cube_pos :
    0 < ∫ x : ℝ in Set.Icc (0 : ℝ) 1, smoothAtom x ^ 2 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact smoothAtom_sq_integral_pos
  · intro x hx
    have houtside : x ≤ 0 ∨ 1 ≤ x := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · exact Or.inl hx.le
      · exact Or.inr hx.le
    rw [smoothAtom_support x houtside]
    norm_num

end BrownianSharp
