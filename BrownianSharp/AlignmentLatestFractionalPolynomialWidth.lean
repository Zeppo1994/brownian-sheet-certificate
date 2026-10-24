import BrownianSharp.AlignmentFractionalGradedPolynomialWidth
import BrownianSharp.AlignmentFractionalIsotropicRates
import Mathlib.Tactic

/-! The sharp anisotropic polynomial-frame width bound discharges the literal
latest fractional entropy/width statement. -/
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentLatestFractionalPolynomialWidth

open BrownianSharp.Latest
open BrownianSharp.AlignmentFractionalGradedPolynomialWidth
open BrownianSharp.AlignmentFractionalIsotropicRates
open HaarQuarter.TheoremD.Width

/-- The actual anisotropic RL dyadic width theorem supplies the input needed
by the general entropy and width extraction, for every literal latest tuple. -/
theorem latest_fractional_entropy_width : Latest.FractionalEntropyWidthStatement := by
  apply latest_fractional_entropy_width_of_dyadic_upper
  intro d hd a ha r ν hν hm
  have hcount : 0 < (Finset.univ.filter (fun i : Fin d => a i = r)).card := by
    rw [hm.2]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcount
  have hieq : a i = r := (Finset.mem_filter.mp hi).2
  have hr : 1/2 < r := by rw [← hieq]; exact ha i
  have hνd : ν ≤ d := by
    calc
      ν = (Finset.univ.filter (fun i : Fin d => a i = r)).card := hm.2.symm
      _ ≤ Fintype.card (Fin d) := Finset.card_le_univ _
      _ = d := by simp
  obtain ⟨e,heq⟩ : ∃ e : ℕ, ν+e=d := ⟨d-ν, by omega⟩
  subst d
  exact polynomial_fractional_tensor_RL_dyadic_width hν hr a ha hm

end BrownianSharp.AlignmentLatestFractionalPolynomialWidth
