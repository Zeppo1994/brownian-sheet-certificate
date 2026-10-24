import BrownianSharp.CameronMartin
import Mathlib.Algebra.Order.Floor.Ring

/-! An exact endpoint grid for the cube and its quantitative covering radius. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter

abbrev CubeDyadicGrid (d N : ℕ) := Fin d → Fin (2^N+1)

def cubeDyadicAnchor {d N : ℕ} (j : CubeDyadicGrid d N) : BrownianCubeAnchor d :=
  ⟨fun i => (j i : ℝ)/(2:ℝ)^N, fun i => ⟨by positivity, by
    apply (div_le_one (by positivity : (0:ℝ)<2^N)).2
    exact_mod_cast (by have := (j i).isLt; omega : (j i).val ≤ 2^N)⟩⟩

theorem cubeDyadicGrid_card (d N : ℕ) :
    Fintype.card (CubeDyadicGrid d N) = (2^N+1)^d := by
  simp [CubeDyadicGrid, Fintype.card_pi_const]

theorem exists_cubeDyadicAnchor_near {d : ℕ} (N : ℕ) (x : BrownianCubeAnchor d) :
    ∃ j : CubeDyadicGrid d N, ∀ i : Fin d,
      |x.val i - (cubeDyadicAnchor j).val i| < ((2:ℝ)^N)⁻¹ := by
  let j : CubeDyadicGrid d N := fun i =>
    ⟨⌊(2:ℝ)^N*x.val i⌋₊, by
      have hx : (2:ℝ)^N*x.val i ≤ (2:ℝ)^N := by
        nlinarith [(x.property i).2, (show (0:ℝ)<2^N by positivity)]
      have hfloor : (⌊(2:ℝ)^N*x.val i⌋₊:ℝ) ≤ (2:ℝ)^N :=
        (Nat.floor_le (mul_nonneg (by positivity) (x.property i).1)).trans hx
      have hnat : ⌊(2:ℝ)^N*x.val i⌋₊ ≤ 2^N := by exact_mod_cast hfloor
      omega⟩
  refine ⟨j,?_⟩
  intro i
  have hx0 := (x.property i).1
  have hscale : 0 < (2:ℝ)^N := by positivity
  have hlo := Nat.floor_le (show 0 ≤ (2:ℝ)^N*x.val i by positivity)
  have hhi := Nat.lt_floor_add_one ((2:ℝ)^N*x.val i)
  change |x.val i - (⌊(2:ℝ)^N*x.val i⌋₊:ℝ)/(2:ℝ)^N| < _
  have hdiff : 0 ≤ x.val i - (⌊(2:ℝ)^N*x.val i⌋₊:ℝ)/(2:ℝ)^N := by
    have h := (div_le_iff₀ hscale).2 (by nlinarith : (⌊(2:ℝ)^N*x.val i⌋₊:ℝ) ≤ x.val i*(2:ℝ)^N)
    nlinarith
  rw [abs_of_nonneg hdiff]
  have htop : (2:ℝ)^N * (x.val i - (⌊(2:ℝ)^N*x.val i⌋₊:ℝ)/(2:ℝ)^N) < 1 := by
    have hcancel : (2:ℝ)^N*((⌊(2:ℝ)^N*x.val i⌋₊:ℝ)/(2:ℝ)^N) =
        (⌊(2:ℝ)^N*x.val i⌋₊:ℝ) := by field_simp
    nlinarith
  rw [← one_div]
  exact (lt_div_iff₀ hscale).2 (by nlinarith)

end BrownianSharp
