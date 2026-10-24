import BrownianSharp.HaarGradePartition
import BrownianSharp.FiniteHaarGradeEnergy
import BrownianSharp.ShapeGrowth

/-! The sharp dictionary row radius for each actual mixed-Haar grade. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter CameronMartin

def haarGradeRowRadius (d k : ℕ) : ℝ :=
  Real.sqrt (hyperbolicCount d k/(2:ℝ)^k)

theorem haarGradeRowRadius_nonneg (d k : ℕ) : 0≤haarGradeRowRadius d k :=
  Real.sqrt_nonneg _

theorem haarHighGradeRow_norm_le {d N n₀ : ℕ} (hd : 1≤d)
    (j : HaarHighGradeIndex d N n₀) (g : CubeDyadicGrid d N) :
    ‖coordinateLayerMask (haarLowHighGrade n₀) (some j) (haarGridRows d N g)‖≤
      haarGradeRowRadius d (n₀+j.val) := by
  have henergy := finiteHaarGrade_grid_energy_le (d:=d) (N:=N) (n:=n₀+j.val)
    (by omega) (cubeDyadicAnchor g).val (cubeDyadicAnchor g).property
  have hsq : ‖coordinateLayerMask (haarLowHighGrade n₀) (some j) (haarGridRows d N g)‖^2≤
      hyperbolicCount d (n₀+j.val)/(2:ℝ)^(n₀+j.val) := by
    rw [haarHighGradeRow_norm_sq]
    exact henergy
  have h := Real.sqrt_le_sqrt hsq
  simpa [haarGradeRowRadius,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] using h

end BrownianSharp
