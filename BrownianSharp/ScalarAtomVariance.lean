import BrownianSharp.ScalarBlockBessel
import BrownianSharp.AtomicBlockKernelL2

/-! Concrete one-dimensional variance bound at a dyadic smooth Fourier scale.

The orthogonality and atom-size inputs remain explicit here.  In particular,
this module does not pretend that a scalar cell estimate is already a
fixed-depth tensor-product estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.ScalarAtomVariance

open BrownianSharp.ScalarBlockBessel
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.SmoothResolution
open AddCircle

def scalarFrequencyBox (t : ℕ) : Finset ℤ :=
  Finset.Icc (-((2 : ℤ) ^ (t + 1))) ((2 : ℤ) ^ (t + 1))

theorem scalarFrequencyBox_card_le (t : ℕ) :
    (scalarFrequencyBox t).card ≤ (2 : ℕ) ^ (t + 2) + 1 := by
  have hc : ((scalarFrequencyBox t).card : ℤ) ≤ (2 : ℤ) ^ (t + 2) + 1 := by
    rw [scalarFrequencyBox, Int.card_Icc_of_le (a := -((2 : ℤ) ^ (t + 1)))
      (b := (2 : ℤ) ^ (t + 1)) (by
        have hp : (0 : ℤ) ≤ (2 : ℤ) ^ (t + 1) := by positivity
        omega)]
    have hpow : (2 : ℤ) ^ (t + 2) = 2 * (2 : ℤ) ^ (t + 1) := by
      rw [pow_succ]
      ring_nf
    rw [hpow]
    push_cast
    exact le_of_eq (by ring_nf)
  exact_mod_cast hc

/-- The scalar smooth-block outputs of any orthogonal atom family obey the
frequency-count variance bound.  The hypotheses state exactly the scalar
cell orthogonality and L² size still needed from the concrete atoms. -/
theorem scalarBlock_atoms_sum_sq_le {ι : ℕ} (t : ℕ)
    (atoms : Fin ι → C(UnitAddCircle, ℂ)) (x : UnitAddCircle)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (horth : ∀ i j, i ≠ j → inner ℂ (continuousLp1 (atoms i))
      (continuousLp1 (atoms j)) = 0)
    (hnorm : ∀ i, ‖continuousLp1 (atoms i)‖ ^ 2 ≤ ρ) :
    (∑ i : Fin ι,
      ‖∑ n ∈ scalarFrequencyBox t,
        (scalarBlock t (n : ℝ) : ℂ) * fourierCoeff (atoms i) n * fourier n x‖ ^ 2)
      ≤ ρ * ((2 : ℝ) ^ (t + 2) + 1) := by
  have hB := polynomial_atoms_sum_sq_le (scalarFrequencyBox t)
    (fun n => (scalarBlock t (n : ℝ) : ℂ)) atoms x hρ horth hnorm
  have henergy : ‖kernelLp (scalarFrequencyBox t)
      (fun n => (scalarBlock t (n : ℝ) : ℂ)) x‖ ^ 2 ≤
      ((2 : ℝ) ^ (t + 2) + 1) := by
    rw [BrownianSharp.ScalarBlockBessel.kernelLp_norm_sq]
    calc
      (∑ n ∈ scalarFrequencyBox t,
          ‖(scalarBlock t (n : ℝ) : ℂ)‖ ^ 2) ≤
        ∑ _n ∈ scalarFrequencyBox t, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have habs := scalarBlock_abs_le_one t (n : ℝ)
          have hnorm' : ‖(scalarBlock t (n : ℝ) : ℂ)‖ ≤ 1 := by
            simpa only [Complex.norm_real, Real.norm_eq_abs] using habs
          have hsq := mul_le_mul_of_nonneg_right hnorm' (norm_nonneg (↑(scalarBlock t (n : ℝ)) : ℂ))
          nlinarith
      _ = (scalarFrequencyBox t).card := by simp
      _ ≤ (2 : ℝ) ^ (t + 2) + 1 := by
          have hc := scalarFrequencyBox_card_le t
          exact_mod_cast hc
  calc
    _ ≤ ρ * ‖kernelLp (scalarFrequencyBox t)
        (fun n => (scalarBlock t (n : ℝ) : ℂ)) x‖ ^ 2 := hB
    _ ≤ ρ * ((2 : ℝ) ^ (t + 2) + 1) :=
      mul_le_mul_of_nonneg_left henergy hρ

end BrownianSharp.ScalarAtomVariance
