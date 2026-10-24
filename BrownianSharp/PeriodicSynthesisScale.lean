import BrownianSharp.NativeScaleCover

/-! Exact Gaussian synthesis normalizations for the three periodic classes. -/
noncomputable section
namespace BrownianSharp

/-- One formula covers Sobolev (beta=0), finite-theta Besov
(beta=1/2-1/theta), and Nikolsky (beta=1/2) normalizations. -/
def periodicSynthesisScale (d n : ℕ) (r β : ℝ) : ℝ :=
  (2:ℝ)^(-r*(n:ℝ)) * (hyperbolicCount d n)^(β-1/2)

theorem periodicSynthesisScale_pos {d n : ℕ} (hd : 1 ≤ d) (r β : ℝ) :
    0 < periodicSynthesisScale d n r β := by
  unfold periodicSynthesisScale
  exact mul_pos (by positivity) (Real.rpow_pos_of_pos (hyperbolicCount_pos hd) _)

/-- Multiplying the class scale by the actual good-grid confinement radius
gives exactly the sharp entropy radius. -/
theorem periodicSynthesisScale_mul_confinement {d q : ℕ} (hd : 1 ≤ d)
    (a η r β : ℝ) :
    (a*periodicSynthesisScale d (2*q) r β) *
      (η*Real.sqrt (((2*q:ℕ):ℝ)*hyperbolicCount d (2*q))) =
      (a*η)*periodicNativeRadius d q r β := by
  have hS := hyperbolicCount_pos (n:=2*q) hd
  have hq : (0:ℝ) ≤ ((2*q:ℕ):ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_mul hq]
  unfold periodicSynthesisScale periodicNativeRadius
  rw [Real.sqrt_eq_rpow (hyperbolicCount d (2*q))]
  have hpower : hyperbolicCount d (2*q)^(β-1/2) *
      hyperbolicCount d (2*q)^(1/2:ℝ) = hyperbolicCount d (2*q)^β := by
    rw [← Real.rpow_add hS]
    congr 1
    ring
  have hexp : -r*((2*q:ℕ):ℝ) = -2*r*(q:ℝ) := by push_cast; ring
  rw [hexp]
  have hcast : ((2*q:ℕ):ℝ) = 2*(q:ℝ) := by push_cast; ring
  rw [hcast]
  calc
    _ = (a*η)*((2:ℝ)^(-2*r*(q:ℝ))*Real.sqrt (2*(q:ℝ)))*
      (hyperbolicCount d (2*q)^(β-1/2)*hyperbolicCount d (2*q)^(1/2:ℝ)) := by ring
    _ = _ := by rw [hpower]; ring

end BrownianSharp
