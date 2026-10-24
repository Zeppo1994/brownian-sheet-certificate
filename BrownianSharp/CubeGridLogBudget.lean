import BrownianSharp.CubeDyadicGrid
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The logarithm of the finite endpoint grid has only linear growth in the
dyadic depth. This is the logarithmic cost in the finite dictionary theorem. -/
noncomputable section
namespace BrownianSharp

 theorem cubeDyadicGrid_log_bound (d N : ℕ) :
    Real.log (2*(Fintype.card (CubeDyadicGrid d N):ℝ)+2)≤
      ((d:ℝ)+2)*((N:ℝ)+1) := by
  rw [cubeDyadicGrid_card]
  push_cast
  have hp : (1:ℝ)≤2^N := one_le_pow₀ (by norm_num)
  have hbase : (2:ℝ)^N+1≤2^(N+1) := by rw [pow_succ]; linarith
  have hM1 : (1:ℝ)≤((2:ℝ)^N+1)^d := one_le_pow₀ (by linarith)
  have hM : ((2:ℝ)^N+1)^d≤((2:ℝ)^(N+1))^d :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<2*((2:ℝ)^N+1)^d+2)
    (show 2*((2:ℝ)^N+1)^d+2≤4*((2:ℝ)^(N+1))^d by nlinarith)
  have hlog2 : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlog2pos : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have heq : Real.log (4*((2:ℝ)^(N+1))^d)=
      (2+(d:ℝ)*((N:ℝ)+1))*Real.log 2 := by
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (by positivity),Real.log_pow,Real.log_pow]
    have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    rw [h4]
    push_cast
    ring
  rw [heq] at hlog
  have hcoef : 0≤2+(d:ℝ)*((N:ℝ)+1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog2 hcoef
  have hN : 0≤(N:ℝ) := Nat.cast_nonneg _
  nlinarith

 theorem cubeDyadicGrid_doubleDepth_log_bound (d n : ℕ) :
    Real.log (2*(Fintype.card (CubeDyadicGrid d (2*n)):ℝ)+2)≤
      (2*((d:ℝ)+2))*((n:ℝ)+1) := by
  have h := cubeDyadicGrid_log_bound d (2*n)
  push_cast at h
  nlinarith [show (0:ℝ)≤(d:ℝ) from Nat.cast_nonneg d]

end BrownianSharp
