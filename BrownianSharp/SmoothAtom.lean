import BrownianSharp.SmoothResolution

/-!
A concrete atom for the manuscript's smooth-layer construction. It is smooth,
unit bounded, zero outside (0,1), and exactly one on [1/4,3/4]. Thus both
nonvanishing and a fixed positive spatial L2 mass are constructive facts.
-/
noncomputable section
namespace BrownianSharp

/-- Smooth plateau atom inside the unit interval. -/
def smoothAtom (x : ℝ) : ℝ :=
  1 - Real.smoothTransition (((4 * x - 2) ^ 2 - 1) / (5 / 4))

theorem smoothAtom_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothAtom := by
  unfold smoothAtom
  fun_prop

theorem smoothAtom_bounds (x : ℝ) : 0 ≤ smoothAtom x ∧ smoothAtom x ≤ 1 := by
  constructor <;> dsimp [smoothAtom] <;>
    linarith [Real.smoothTransition.nonneg (((4 * x - 2) ^ 2 - 1) / (5 / 4)),
      Real.smoothTransition.le_one (((4 * x - 2) ^ 2 - 1) / (5 / 4))]

theorem smoothAtom_abs_le_one (x : ℝ) : |smoothAtom x| ≤ 1 := by
  rw [abs_of_nonneg (smoothAtom_bounds x).1]
  exact (smoothAtom_bounds x).2

theorem smoothAtom_support_inner (x : ℝ) (hx : x ≤ 1 / 8 ∨ 7 / 8 ≤ x) :
    smoothAtom x = 0 := by
  have hs : (3 / 2 : ℝ) ≤ |4 * x - 2| := by
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith : 4 * x - 2 ≤ 0)]
      linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ 4 * x - 2)]
      linarith
  have hs2 : 9 / 4 ≤ (4 * x - 2) ^ 2 := by
    nlinarith [sq_abs (4 * x - 2)]
  simp [smoothAtom, Real.smoothTransition.one_of_one_le
    (by linarith : 1 ≤ ((4 * x - 2) ^ 2 - 1) / (5 / 4))]

theorem smoothAtom_support (x : ℝ) (hx : x ≤ 0 ∨ 1 ≤ x) : smoothAtom x = 0 := by
  apply smoothAtom_support_inner
  rcases hx with hx | hx
  · left; linarith
  · right; linarith

theorem smoothAtom_plateau (x : ℝ) (hx : x ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)) :
    smoothAtom x = 1 := by
  have hs : (4 * x - 2) ^ 2 ≤ 1 := by
    nlinarith [hx.1, hx.2]
  simp [smoothAtom, Real.smoothTransition.zero_of_nonpos
    (by linarith : ((4 * x - 2) ^ 2 - 1) / (5 / 4) ≤ 0)]

theorem smoothAtom_nonzero : smoothAtom (1 / 2) ≠ 0 := by
  rw [smoothAtom_plateau (1 / 2) (by constructor <;> norm_num)]
  norm_num

end BrownianSharp
