import BrownianSharp.ShellVariance
import BrownianSharp.ShapeGrowth

open scoped BigOperators

namespace BrownianSharp

/-- Weak-composition overlap caps obey the shell exponential condition for
all excess grades once the even moment order is at most a small multiple of
the grid depth. -/
theorem shapeOverlapCap_shell_decay_condition {d n h p : ℕ}
    (hd : 2 ≤ d) (hn : 0 < n) {L κ : ℝ} (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 /
      (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1)) :
    2 * (p : ℝ) * shapeOverlapCap d n h L ≤
      (Real.log 2 / 2) * (h + 1 : ℝ) := by
  let F : ℝ := (Nat.factorial (d - 1) : ℝ)
  let x : ℝ := ((h : ℝ) + 1) / ((n : ℝ) + 1)
  have hRlin : shapeOverlapCap d n h L ≤ L * F * x := by
    simpa [F, x] using shapeOverlapCap_le_linear hd n h hL.le
  have hden : 0 < 4 * L * F := by positivity
  have hκmul : κ * (4 * L * F) ≤ Real.log 2 :=
    (le_div_iff₀ hden).mp (by simpa [F] using hκ)
  have hcoef : 2 * κ * L * F ≤ Real.log 2 / 2 := by nlinarith [hκmul]
  have hpr : 2 * (p : ℝ) ≤ 2 * κ * ((n : ℝ) + 1) := by nlinarith [hp]
  have hleft := mul_le_mul_of_nonneg_left hRlin (by positivity : 0 ≤ 2 * (p : ℝ))
  have hright := mul_le_mul_of_nonneg_right hpr (by positivity : 0 ≤ L * F * x)
  have hcancel : ((n : ℝ) + 1) * x = (h : ℝ) + 1 := by
    dsimp [x]
    field_simp
  calc
    2 * (p : ℝ) * shapeOverlapCap d n h L ≤
        2 * (p : ℝ) * (L * F * x) := hleft
    _ ≤ (2 * κ * ((n : ℝ) + 1)) * (L * F * x) := hright
    _ = (2 * κ * L * F) * (h + 1 : ℝ) := by rw [← hcancel]; ring
    _ ≤ (Real.log 2 / 2) * (h + 1 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

end BrownianSharp
