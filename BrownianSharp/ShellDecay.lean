import BrownianSharp.ShellVariance
import BrownianSharp.ShapeGrowth

open scoped BigOperators

namespace BrownianSharp

/-- A shell whose correlation cap is small compared with its excess grade
has the required geometric damping.  The hypothesis is stated on the actual
cap `R`; this keeps the analytic smallness condition explicit instead of
burying it in an asymptotic constant. -/
theorem highPowerPairKernel_shell_sum_mul_pow_le_of_decay {d n h : ℕ}
    (hd : 0 < d) (p : ℕ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hvar : ∀ q : MidpointGridIndex d n, v₀ ≤ nativeLayerRowVariance q)
    (hdecay : 2 * (p : ℝ) *
        ((1 / (2 : ℝ) ^ (n + 2 * d)) *
          (Nat.min (Nat.choose (n + d - 1) (d - 1))
            (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀) ≤
        (Real.log 2 / 2) * (h + 1 : ℝ)) :
    (∑ x : midpointPairShell (d := d) (n := n) (n + h),
      highPowerPairKernel p
        (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2))) *
        (2 ^ (n + h) : ℝ) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          (4 * (p : ℝ) ^ 2 *
            ((1 / (2 : ℝ) ^ (n + 2 * d)) *
              (Nat.min (Nat.choose (n + d - 1) (d - 1))
                (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀) ^ 2 *
            Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) := by
  let R : ℝ := (1 / (2 : ℝ) ^ (n + 2 * d)) *
    (Nat.min (Nat.choose (n + d - 1) (d - 1))
      (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hExp : Real.exp (2 * (p : ℝ) * R) ≤
      Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) :=
    Real.exp_le_exp.mpr (by simpa [R] using hdecay)
  have hbase := highPowerPairKernel_shell_sum_mul_pow_le_of_cap
    (d := d) (n := n) (h := h) hd p hv₀ hvar
  have hRhs :
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          (4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R)) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          (4 * (p : ℝ) ^ 2 * R ^ 2 *
            Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) := by
    have hfactor : 0 ≤
        (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
          (Fintype.card (MidpointPairGrid d n) : ℝ) *
            (4 * (p : ℝ) ^ 2 * R ^ 2) := by positivity
    calc
      _ = ((Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
          (Fintype.card (MidpointPairGrid d n) : ℝ) *
            (4 * (p : ℝ) ^ 2 * R ^ 2)) * Real.exp (2 * (p : ℝ) * R) := by ring
      _ ≤ ((Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
          (Fintype.card (MidpointPairGrid d n) : ℝ) *
            (4 * (p : ℝ) ^ 2 * R ^ 2)) *
              Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hExp hfactor
      _ = _ := by ring
  calc
    _ ≤ (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          (4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R)) := by
      simpa [R] using hbase
    _ ≤ _ := hRhs

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
