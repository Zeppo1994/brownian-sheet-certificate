import BrownianSharp.ScalarAtomVariance
import BrownianSharp.PeriodicAtomDerivatives

/-! High-frequency reduction to a derivative atom family.  The multiplier is
factored through the exact Fourier derivative identity; the remaining kernel
energy is kept as a finite sum so the scalar frequency-tail estimate can be
audited separately. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.ScalarHighFrequency

open BrownianSharp.ScalarAtomVariance
open BrownianSharp.ScalarBlockBessel
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.SmoothResolution
open AddCircle

def inverseMultiplier (t K : ℕ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else
    (scalarBlock t (n : ℝ) : ℂ) /
      ((2 * Real.pi * Complex.I * (n : ℂ)) ^ K)

/-- A frequency separated from zero has the expected inverse-derivative
multiplier bound.  The annular-support premise is isolated so the cutoff
support argument can be checked independently. -/
theorem inverseMultiplier_norm_le {t K : ℕ} {n : ℤ} (hn : n ≠ 0)
    (haway : (2 : ℝ) ^ (t - 1) ≤ |(n : ℝ)|) :
    ‖inverseMultiplier t K n‖ ≤
      ((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹ := by
  have hA : ‖(2 * Real.pi * Complex.I * (n : ℂ))‖ =
      2 * Real.pi * |(n : ℝ)| := by
    simp [norm_mul, abs_of_pos Real.pi_pos, Complex.norm_intCast]
  have hbase : 0 < 2 * Real.pi * (2 : ℝ) ^ (t - 1) := by positivity
  have hscale : 2 * Real.pi * (2 : ℝ) ^ (t - 1) ≤
      2 * Real.pi * |(n : ℝ)| := by
    exact mul_le_mul_of_nonneg_left haway
      (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
  have hdenReal : ‖(2 * Real.pi * Complex.I * (n : ℂ)) ^ K‖ =
      (2 * Real.pi * |(n : ℝ)|) ^ K := by rw [norm_pow, hA]
  have hpow : (2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K ≤
      (2 * Real.pi * |(n : ℝ)|) ^ K := by
    exact pow_le_pow_left₀ (le_of_lt hbase) hscale K
  have hdenpos : 0 < (2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K := by
    positivity
  have hnum : ‖(scalarBlock t (n : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using scalarBlock_abs_le_one t (n : ℝ)
  have hdiv : ‖(scalarBlock t (n : ℝ) : ℂ) /
        ((2 * Real.pi * Complex.I * (n : ℂ)) ^ K)‖ ≤
      ((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹ := by
    rw [norm_div, hdenReal]
    calc
      ‖(scalarBlock t (n : ℝ) : ℂ)‖ /
          (2 * Real.pi * |(n : ℝ)|) ^ K ≤
        1 / (2 * Real.pi * |(n : ℝ)|) ^ K := by
          apply div_le_div_of_nonneg_right hnum
          positivity
      _ ≤ ((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le hdenpos hpow
  simpa [inverseMultiplier, if_neg hn] using hdiv

/-- At a positive dyadic scale the scalar smooth multiplier annihilates the
zero Fourier mode. -/
theorem scalarBlock_zero (t : ℕ) (ht : 0 < t) : scalarBlock t 0 = 0 := by
  unfold scalarBlock
  rw [if_neg (Nat.ne_of_gt ht)]
  have h₁ : cutoff (0 / (2 : ℝ) ^ t) = 1 := by
    apply cutoff_eq_one
    simp
  have h₂ : cutoff (0 / (2 : ℝ) ^ (t - 1)) = 1 := by
    apply cutoff_eq_one
    simp
  rw [h₁, h₂]
  ring

/-- The scalar dyadic multiplier vanishes on the closed low-frequency band. -/
theorem scalarBlock_eq_zero_of_abs_le_lower (t : ℕ) (ht : 0 < t)
    {ξ : ℝ} (hξ : |ξ| ≤ (2 : ℝ) ^ (t - 1)) :
    scalarBlock t ξ = 0 := by
  unfold scalarBlock
  rw [if_neg (Nat.ne_of_gt ht)]
  have htEq : t = (t - 1) + 1 := by omega
  have hpow : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
    calc
      (2 : ℝ) ^ t = (2 : ℝ) ^ ((t - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ t)]
      _ = (2 : ℝ) ^ (t - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (t - 1) := by ring
  have hbase : 0 < (2 : ℝ) ^ (t - 1) := by positivity
  have hlow : |ξ| / (2 : ℝ) ^ (t - 1) ≤ 1 := by
    exact (div_le_one₀ hbase).2 hξ
  have hlowCut : |ξ / (2 : ℝ) ^ (t - 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos hbase]
    exact hlow
  have hhigh : |ξ / (2 : ℝ) ^ t| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ t), hpow]
    have hden : (2 : ℝ) ^ (t - 1) ≤ 2 * (2 : ℝ) ^ (t - 1) := by nlinarith
    have hquot : |ξ| / (2 * (2 : ℝ) ^ (t - 1)) ≤
        |ξ| / (2 : ℝ) ^ (t - 1) :=
      div_le_div_of_nonneg_left (abs_nonneg ξ) hbase hden
    exact le_trans hquot hlow
  rw [cutoff_eq_one hhigh, cutoff_eq_one hlowCut]
  ring

/-- The nonzero frequencies of the actual smooth dyadic block lie outside
the lower edge of its frequency annulus. -/
theorem scalarBlock_annular_support (t : ℕ) (ht : 0 < t) {ξ : ℝ}
    (hξ : scalarBlock t ξ ≠ 0) :
    (2 : ℝ) ^ (t - 1) ≤ |ξ| := by
  by_contra hnot
  have hsmall : |ξ| ≤ (2 : ℝ) ^ (t - 1) := le_of_not_ge hnot
  exact hξ (scalarBlock_eq_zero_of_abs_le_lower t ht hsmall)

/-- Uniform coefficient control turns Parseval's exact identity into a finite
kernel energy estimate. -/
theorem inverse_kernel_energy_le_card_mul (S : Finset ℤ) (c : ℤ → ℂ)
    (x : UnitAddCircle) {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ n ∈ S, ‖c n‖ ≤ η) :
    ‖kernelLp S c x‖ ^ 2 ≤ (S.card : ℝ) * η ^ 2 := by
  rw [BrownianSharp.ScalarBlockBessel.kernelLp_norm_sq]
  calc
    (∑ n ∈ S, ‖c n‖ ^ 2) ≤ ∑ _n ∈ S, η ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := hcoeff n hn
      have hsq := mul_le_mul_of_nonneg_right hn' (norm_nonneg (c n))
      nlinarith
    _ = (S.card : ℝ) * η ^ 2 := by simp [mul_comm]

/-- If the nonzero support of a finite coefficient set lies outside the
dyadic low-frequency interval, its inverse-derivative kernel has the expected
finite-sum energy bound. -/
theorem inverse_kernel_energy_le_of_annular_support (S : Finset ℤ)
    (t K : ℕ) (x : UnitAddCircle)
    (haway : ∀ n ∈ S, inverseMultiplier t K n ≠ 0 →
      (2 : ℝ) ^ (t - 1) ≤ |(n : ℝ)|) :
    ‖kernelLp S (inverseMultiplier t K) x‖ ^ 2 ≤
      (S.card : ℝ) * (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2 := by
  apply inverse_kernel_energy_le_card_mul S (inverseMultiplier t K) x
    (η := ((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹)
  · exact inv_nonneg.mpr (pow_nonneg
      (by positivity : 0 ≤ 2 * Real.pi * (2 : ℝ) ^ (t - 1)) K)
  · intro n hn
    by_cases hn0 : n = 0
    · have hη : 0 ≤ ((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹ :=
        inv_nonneg.mpr (pow_nonneg
          (by positivity : 0 ≤ 2 * Real.pi * (2 : ℝ) ^ (t - 1)) K)
      simpa [inverseMultiplier, hn0] using hη
    · by_cases hzero : inverseMultiplier t K n = 0
      · have hη : 0 ≤ ((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹ :=
          inv_nonneg.mpr (pow_nonneg
            (by positivity : 0 ≤ 2 * Real.pi * (2 : ℝ) ^ (t - 1)) K)
        simpa [hzero] using hη
      · exact inverseMultiplier_norm_le hn0 (haway n hn hzero)

/-- The actual scalar smooth cutoff has precisely the annular support needed
by the inverse-derivative kernel estimate. -/
theorem scalarBlock_inverse_kernel_energy_le (S : Finset ℤ)
    (t K : ℕ) (ht : 0 < t) (x : UnitAddCircle) :
    ‖kernelLp S (inverseMultiplier t K) x‖ ^ 2 ≤
      (S.card : ℝ) * (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2 := by
  apply inverse_kernel_energy_le_of_annular_support S t K x
  intro n hn hInv
  by_cases hn0 : n = 0
  · subst n
    simp [inverseMultiplier] at hInv
  · have hmult : scalarBlock t (n : ℝ) ≠ 0 := by
      intro hz
      have hzero : inverseMultiplier t K n = 0 := by
        simp [inverseMultiplier, hn0, hz]
      exact hInv hzero
    exact scalarBlock_annular_support t ht hmult

/-- For a finite scalar block, its output on an atom family equals the output
on the Kth derivative family with the inverse derivative multiplier.  The
coefficient relation is exactly the iterated AddCircle Fourier identity from
`PeriodicAtomDerivatives`; no smoothness or atom synthesis claim is hidden. -/
theorem block_eq_derivative_block {ι : ℕ} (t K : ℕ) (ht : 0 < t)
    (f g : Fin ι → C(UnitAddCircle, ℂ))
    (hderiv : ∀ i n, n ≠ 0 →
      fourierCoeff (g i) n =
        (2 * Real.pi * Complex.I * (n : ℂ)) ^ K * fourierCoeff (f i) n)
    (i : Fin ι) (x : UnitAddCircle) :
    (∑ n ∈ scalarFrequencyBox t,
      (scalarBlock t (n : ℝ) : ℂ) * fourierCoeff (f i) n * fourier n x) =
    (∑ n ∈ scalarFrequencyBox t,
      inverseMultiplier t K n * fourierCoeff (g i) n * fourier n x) := by
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [inverseMultiplier, scalarBlock_zero t ht]
  · have hden : (2 * Real.pi * Complex.I * (n : ℂ)) ^ K ≠ 0 := by
      apply pow_ne_zero
      have hncast : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn0
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (by norm_num) hpi
        · exact Complex.I_ne_zero
      · exact hncast
    simp only [inverseMultiplier, if_neg hn0]
    rw [hderiv i n hn0]
    field_simp
    <;> ring

/-- Bessel's inequality now uses derivative atoms.  In particular, this is the
high-frequency variance bridge once orthogonality and the derivative L² cap
are supplied by the cell-support lemmas. -/
theorem scalarBlock_derivative_atoms_sum_sq_le {ι : ℕ} (t K : ℕ)
    (ht : 0 < t) (f g : Fin ι → C(UnitAddCircle, ℂ))
    (hderiv : ∀ i n, n ≠ 0 →
      fourierCoeff (g i) n =
        (2 * Real.pi * Complex.I * (n : ℂ)) ^ K * fourierCoeff (f i) n)
    (x : UnitAddCircle) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (horth : ∀ i j, i ≠ j → inner ℂ (continuousLp1 (g i))
      (continuousLp1 (g j)) = 0)
    (hnorm : ∀ i, ‖continuousLp1 (g i)‖ ^ 2 ≤ ρ) :
    (∑ i : Fin ι,
      ‖∑ n ∈ scalarFrequencyBox t,
        (scalarBlock t (n : ℝ) : ℂ) * fourierCoeff (f i) n * fourier n x‖ ^ 2) ≤
      ρ * ‖kernelLp (scalarFrequencyBox t) (inverseMultiplier t K) x‖ ^ 2 := by
  have hB := polynomial_atoms_sum_sq_le (scalarFrequencyBox t)
    (inverseMultiplier t K) g x hρ horth hnorm
  calc
    _ = ∑ i : Fin ι,
        ‖∑ n ∈ scalarFrequencyBox t,
          inverseMultiplier t K n * fourierCoeff (g i) n * fourier n x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [block_eq_derivative_block t K ht f g hderiv i x]
    _ ≤ ρ * ‖kernelLp (scalarFrequencyBox t)
        (inverseMultiplier t K) x‖ ^ 2 := hB

end BrownianSharp.ScalarHighFrequency
