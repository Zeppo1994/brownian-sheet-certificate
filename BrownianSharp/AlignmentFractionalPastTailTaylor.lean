import BrownianSharp.AlignmentFractionalPastTail
import BrownianSharp.AlignmentFractionalPolynomialApproximation

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentFractionalPastTailTaylor

open BrownianSharp.AlignmentFractionalPastTail
open BrownianSharp.AlignmentFractionalPolynomialApproximation

/-- The order-`m` one-sided Taylor approximant to the MvN past-tail profile,
expanded about the upper endpoint `b`. -/
def pastTailTaylorApprox (p : ℝ) (m : ℕ) (b t x : ℝ) : ℝ :=
  taylorWithinEval (fun z : ℝ => z^p) (m-1) (Set.uIcc (x+b) (x+t)) (x+b) (x+t) - x^p

/-- Pointwise remainder for the actual past-tail power difference. This is
the one-sided form used on a subinterval `[a,b]` with `b-t ≤ a/2`. -/
theorem pastTailTaylor_pointwise_error {p : ℝ} {m : ℕ} {a b t x : ℝ}
    (hm : 0 < m) (hpm : p < m) (ha : 0 < a) (hab : a ≤ b)
    (htlo : a ≤ t) (hthi : t ≤ b) (hx : 0 ≤ x) :
    |pastTailPower p t x - pastTailTaylorApprox p m b t x| ≤
      (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (b-t)^m * (x+t)^(p-m) := by
  have hxt : 0 < x+t := by linarith
  have hxxb : x+t ≤ x+b := by linarith
  have hrem := power_taylor_remainder_bound (p:=p) hm hpm hxt hxxb
  simpa [pastTailPower, pastTailTaylorApprox] using hrem

/-- On a short interval where `b-a ≤ a/2`, the Taylor remainder has a
uniform decaying power envelope in the source coordinate. -/
theorem pastTailTaylor_pointwise_error_uniform {p : ℝ} {m : ℕ} {a b t x : ℝ}
    (hm : 0 < m) (hpm : p < m) (ha : 0 < a) (hab : a ≤ b)
    (hwidth : b-a ≤ a/2) (htlo : a ≤ t) (hthi : t ≤ b) (hx : 0 ≤ x) :
    |pastTailPower p t x - pastTailTaylorApprox p m b t x| ≤
      (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (a/2)^m * (x+a)^(p-m) := by
  have hpoint := pastTailTaylor_pointwise_error hm hpm ha hab htlo hthi hx
  have hwidth' : b-t ≤ a/2 := by linarith
  have hbase : 0 < x+a := by linarith
  have hmono : (x+t)^(p-m) ≤ (x+a)^(p-m) :=
    Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by norm_cast; linarith)
  have hcoeff : 0 ≤ |(descPochhammer ℝ m).eval p| / (m.factorial:ℝ) := by positivity
  have hpow : (b-t)^m ≤ (a/2)^m := by
    exact pow_le_pow_left₀ (by positivity) hwidth' m
  calc
    _ ≤ (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (b-t)^m * (x+t)^(p-m) := hpoint
    _ ≤ (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (b-t)^m * (x+a)^(p-m) := by
      apply mul_le_mul_of_nonneg_left hmono (mul_nonneg hcoeff (by positivity))
    _ ≤ (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (a/2)^m * (x+a)^(p-m) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hbase.le _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

end BrownianSharp.AlignmentFractionalPastTailTaylor
