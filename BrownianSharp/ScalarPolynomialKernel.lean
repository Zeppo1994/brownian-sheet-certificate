import BrownianSharp.ScalarProfileKernel
import BrownianSharp.ScalarAtomVariance

/-! Fourier coefficient identification for the actual finite scalar kernels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.ScalarKernelL1
open AddCircle BrownianSharp.SmoothResolution BrownianSharp.ScalarAtomVariance

def polynomialKernel (S : Finset ℤ) (c : ℤ → ℂ) : C(UnitAddCircle, ℂ) :=
  ∑ n ∈ S, c n • fourier n

theorem polynomialKernel_coefficient (S : Finset ℤ) (c : ℤ → ℂ) (k : ℤ) :
    fourierCoeff (polynomialKernel S c) k = if k ∈ S then c k else 0 := by
  classical
  have heq : (polynomialKernel S c : UnitAddCircle → ℂ) =
      ∑ n ∈ S, (fun x => c n * fourier n x) := by
    funext x
    simp [polynomialKernel, smul_eq_mul]
  have hi (n : ℤ) : Integrable (fun x : UnitAddCircle => c n * fourier n x)
      AddCircle.haarAddCircle :=
    ((fourier n).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [heq, fourierCoeff.sum _ _ (fun n hn => hi n)]
  simp only [Finset.sum_apply]
  simp_rw [fourierCoeff.const_mul]
  have hc (n : ℤ) : fourierCoeff (fourier (T := (1:ℝ)) n) k = if k=n then 1 else 0 := by
    simpa only [Pi.single_apply] using congrFun (fourierCoeff_fourier (T := (1:ℝ)) n) k
  simp_rw [hc]
  simp [Finset.sum_ite_eq', mul_ite]

theorem polynomialKernel_coefficient_of_support (S : Finset ℤ) (c : ℤ → ℂ)
    (hc : ∀ k, k ∉ S → c k=0) (k : ℤ) :
    fourierCoeff (polynomialKernel S c) k = c k := by
  rw [polynomialKernel_coefficient]
  split_ifs with hk
  · rfl
  · exact (hc k hk).symm

/-- The literal scalar-block convolution kernel. -/
def scalarBlockKernel (t : ℕ) : C(UnitAddCircle, ℂ) :=
  polynomialKernel (scalarFrequencyBox t) (fun k => (scalarBlock t (k:ℝ) : ℂ))

theorem scalarBlock_eq_zero_of_two_pow_le_abs (t : ℕ) {ξ : ℝ}
    (hξ : (2:ℝ)^(t+1) ≤ |ξ|) : scalarBlock t ξ = 0 := by
  have hupper : cutoff (ξ / (2:ℝ)^t) = 0 := by
    apply cutoff_eq_zero
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<2^t)]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2^t)).2
    simpa [pow_succ, mul_comm] using hξ
  by_cases ht : t=0
  · subst t
    simpa [scalarBlock] using hupper
  · have hpow : (2:ℝ)^(t-1) ≤ (2:ℝ)^t :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hlower : cutoff (ξ / (2:ℝ)^(t-1)) = 0 := by
      apply cutoff_eq_zero
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<2^(t-1))]
      apply (le_div_iff₀ (by positivity : (0:ℝ)<2^(t-1))).2
      have hξ' : 2*(2:ℝ)^t ≤ |ξ| := by simpa [pow_succ, mul_comm] using hξ
      nlinarith
    simp [scalarBlock, ht, hupper, hlower]

theorem scalarBlockKernel_coefficient (t : ℕ) (k : ℤ) :
    fourierCoeff (scalarBlockKernel t) k = (scalarBlock t (k:ℝ) : ℂ) := by
  apply polynomialKernel_coefficient_of_support
  intro k hk
  have hout : (2:ℝ)^(t+1) ≤ |(k:ℝ)| := by
    simp only [scalarFrequencyBox, Finset.mem_Icc, not_and_or, not_le] at hk
    rcases hk with hk | hk
    · have hcast : (k:ℝ) < -((2:ℝ)^(t+1)) := by exact_mod_cast hk
      exact le_trans (by linarith) (neg_le_abs _)
    · have hcast : (2:ℝ)^(t+1) < (k:ℝ) := by exact_mod_cast hk
      exact hcast.le.trans (le_abs_self _)
  exact_mod_cast scalarBlock_eq_zero_of_two_pow_le_abs t hout

end BrownianSharp.ScalarKernelL1
