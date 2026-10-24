import BrownianSharp.CameronMartinDyadicWidth
import BrownianSharp.CubeGridLogBudget
import BrownianSharp.DKLLLayerError

/-! Evaluation of the square-summed dictionary approximation error at the
actual grid size and actual half-base rank allocation. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter DKLLRankAllocation DKLLFiniteLayerRate DKLLLayerError

def dyadicHaarDictionaryRateConstant (C : ℝ) (d : ℕ) : ℝ :=
  1+16*C^2*((d:ℝ)+2)*(Nat.factorial (d-1):ℝ)*layerBudget (d-1)

theorem dyadicHaarDictionaryRateConstant_pos (C : ℝ) (d : ℕ) :
    0<dyadicHaarDictionaryRateConstant C d := by
  unfold dyadicHaarDictionaryRateConstant
  have h := layerBudget_nonneg (d-1)
  positivity

theorem dyadicHaarDictionaryErrorSum_le {d n : ℕ} (hd : 2≤d) (hn : 2≤n) (C : ℝ) (hC : 0≤C) :
    dyadicHaarDictionaryErrorSum C d n≤
      dyadicHaarDictionaryRateConstant C d*((n:ℝ)+1)*(((2:ℝ)^n)⁻¹)^2 := by
  let Ln := Real.log (2*(Fintype.card (CubeDyadicGrid d (2*n)):ℝ)+2)
  let Q := 16*C^2*((d:ℝ)+2)*(Nat.factorial (d-1):ℝ)
  let b := ((n:ℝ)+1)*(((2:ℝ)^n)⁻¹)^2
  let e : ℕ → ℝ := fun j => C*haarGradeRowRadius d (n+j)*Real.sqrt
    (Ln/((allocatedRank (Fintype.card (LayerIndex d n)/2) j:ℝ)+1))
  have hLn : 0≤Ln := by
    apply Real.log_nonneg
    have hM : (0:ℝ)≤(Fintype.card (CubeDyadicGrid d (2*n)):ℝ) := Nat.cast_nonneg _
    linarith
  have hLog := cubeDyadicGrid_doubleDepth_log_bound d n
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hper : ∀ j ∈ Finset.range (d*(2*n)+1-n),
      (e j)^2≤(Q*b)*(((j+1:ℕ):ℝ)^(d-1)*layerRatio^j) := by
    intro j hj
    have h := native_haar_allocated_layer_error_squared_le hd hn (j:=j) C Ln hC hLn hLog
    simpa [e,Ln,Q,b,haarGradeRowRadius,dyadicSquare,mul_assoc] using h
  have hsum := sum_squared_layer_errors_le (d-1) (d*(2*n)+1-n)
    (Q*b) (mul_nonneg hQ hb) e hper
  have heq : dyadicHaarDictionaryErrorSum C d n=
      ∑ j ∈ Finset.range (d*(2*n)+1-n),(e j)^2 := by
    unfold dyadicHaarDictionaryErrorSum
    exact Fin.sum_univ_eq_sum_range (fun j => (e j)^2) _
  rw [heq]
  calc
    _≤Q*b*layerBudget (d-1) := hsum
    _≤dyadicHaarDictionaryRateConstant C d*((n:ℝ)+1)*(((2:ℝ)^n)⁻¹)^2 := by
      unfold dyadicHaarDictionaryRateConstant
      dsimp [Q,b] at *
      nlinarith

end BrownianSharp
