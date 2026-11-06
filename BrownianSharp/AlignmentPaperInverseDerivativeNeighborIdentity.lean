import BrownianSharp.AlignmentPaperInverseDerivativeNeighbor
import BrownianSharp.AlignmentPeriodicAdmissibleCutoff
import BrownianSharp.InverseDerivativeProfileIdentity
import BrownianSharp.SmoothResolution
import BrownianSharp.ScalarHighFrequency
import BrownianSharp.AlignmentPaperSignedKernelSquareLp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

/-! Exact partition identities for the neighboring inverse blocks. The
cutoff partition is proved from the actual admissible cutoff, including the
two low levels where the neighbor set is truncated. -/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperInverseDerivativeNeighborIdentity

open BrownianSharp.AlignmentPaperInverseDerivativeNeighbor
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.SmoothResolution
open BrownianSharp.ScalarHighFrequency
open BrownianSharp.AlignmentPaperSignedKernelSquareLp
open BrownianSharp.ScalarKernelL1

private abbrev abBlock := BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock

private lemma neighborScales_explicit (s : ℕ) :
    neighborScales s = {s-1, s, s+1} := by
  ext j
  simp only [neighborScales, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  omega

private theorem scalarBlock_lower_support (φ : AdmissibleCutoff) {s : ℕ}
    (hs : 2 ≤ s) {ξ : ℝ} (hξ : abBlock φ s ξ ≠ 0) :
    (2:ℝ)^(s-1) < |ξ| := by
  by_contra h
  have hlow : |ξ| ≤ (2:ℝ)^(s-1) := le_of_not_gt h
  have hp1 : (2:ℝ)^(s-1) ≤ (2:ℝ)^s := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hp2 : (2:ℝ)^(s-1) ≤ (2:ℝ)^(s-1) := le_rfl
  have hx1 : |ξ/(2:ℝ)^s| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<(2:ℝ)^s)]
    exact (div_le_one (by positivity : (0:ℝ)<(2:ℝ)^s)).2 (hlow.trans hp1)
  have hx2 : |ξ/(2:ℝ)^(s-1)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<(2:ℝ)^(s-1))]
    exact (div_le_one (by positivity : (0:ℝ)<(2:ℝ)^(s-1))).2 (hlow.trans hp2)
  have hz : abBlock φ s ξ = 0 := by
    change BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock φ s ξ = 0
    rw [BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock,
      if_neg (by omega : s ≠ 0)]
    rw [φ.one_of_abs_le_one _ hx1, φ.one_of_abs_le_one _ hx2]
    ring
  exact hξ hz

/-- The neighboring scalar cutoff profiles sum to one on the support of the
target block, at every level including the low levels zero and one. -/
theorem neighbor_scalarBlock_sum_eq_one_of_ne_zero
    (φ : AdmissibleCutoff) (s : ℕ) {ξ : ℝ}
    (hξ : abBlock φ s ξ ≠ 0) :
    (∑ j ∈ neighborScales s, abBlock φ j ξ) = 1 := by
  rw [neighborScales_explicit]
  change (∑ j ∈ ({s-1, s, s+1} : Finset ℕ), abBlock φ j ξ) = 1
  by_cases hs0 : s = 0
  · subst s
    have hcutne : φ.value ξ ≠ 0 := by
      simpa [abBlock, BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock] using hξ
    have habs : |ξ| < 2 := by
      by_contra h
      have h' : 2 ≤ |ξ| := le_of_not_gt h
      exact hcutne (φ.zero_of_two_le_abs ξ h')
    have hsmall : |ξ / 2| ≤ 1 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact (div_le_one (by norm_num : (0:ℝ)<2)).2 habs.le
    have hsum : (∑ j ∈ ({0-1, 0, 0+1} : Finset ℕ), abBlock φ j ξ) =
        φ.value (ξ/2) := by
      norm_num [abBlock, BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock]
    rw [hsum, φ.one_of_abs_le_one _ hsmall]
  · by_cases hs1 : s = 1
    · subst s
      have hcutneq :
          φ.value (ξ/2) - φ.value ξ ≠ 0 := by
        simpa [abBlock, BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock] using hξ
      have habs : |ξ| < 4 := by
        by_contra h
        have h' : 4 ≤ |ξ| := le_of_not_gt h
        have h1 : φ.value (ξ/2) = 0 := by
          apply φ.zero_of_two_le_abs
          rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
          exact (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2 (by nlinarith)
        have h2 : φ.value ξ = 0 := φ.zero_of_two_le_abs ξ (by linarith)
        exact hcutneq (by rw [h1, h2]; ring)
      have hsmall : |ξ/4| ≤ 1 := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<4)]
        exact (div_le_one (by norm_num : (0:ℝ)<4)).2 habs.le
      have hsum : (∑ j ∈ ({1-1, 1, 1+1} : Finset ℕ), abBlock φ j ξ) =
          φ.value (ξ/4) := by
        norm_num [abBlock, BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock]
      rw [hsum, φ.one_of_abs_le_one _ hsmall]
    · have hsge : 2 ≤ s := by omega
      have hupper : |ξ| < (2:ℝ)^(s+1) := by
        by_contra h
        have h' : (2:ℝ)^(s+1) ≤ |ξ| := le_of_not_gt h
        exact hξ (scalarBlock_eq_zero_of_two_pow_le_abs φ s h')
      have hlower := scalarBlock_lower_support φ hsge hξ
      have hsmall : |ξ/(2:ℝ)^(s+1)| ≤ 1 := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<(2:ℝ)^(s+1))]
        exact (div_le_one (by positivity : (0:ℝ)<(2:ℝ)^(s+1))).2 hupper.le
      have hlarge : 2 ≤ |ξ/(2:ℝ)^(s-2)| := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<(2:ℝ)^(s-2))]
        apply (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^(s-2))).2
        have hpow : (2:ℝ)^(s-1) = 2*(2:ℝ)^(s-2) := by
          have hn : s-1 = (s-2)+1 := by omega
          rw [hn, pow_succ]
          ring
        rw [← hpow]
        exact le_of_lt hlower
      have hfirst : φ.value (ξ/(2:ℝ)^(s+1)) = 1 :=
        φ.one_of_abs_le_one _ hsmall
      have hlast : φ.value (ξ/(2:ℝ)^(s-2)) = 0 :=
        φ.zero_of_two_le_abs _ hlarge
      have hsumcut :
          (∑ j ∈ ({s-1, s, s+1} : Finset ℕ), abBlock φ j ξ) =
            φ.value (ξ/(2:ℝ)^(s+1)) - φ.value (ξ/(2:ℝ)^(s-2)) := by
        have hsmul : s-1 ≠ 0 := by omega
        have hsmul2 : s ≠ 0 := by omega
        have hsmul3 : s+1 ≠ 0 := by omega
        rw [show ({s-1, s, s+1} : Finset ℕ) =
          insert (s-1) (insert s {s+1}) by ext j; simp]
        rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
        simp [abBlock, BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock,
          hsmul, hsmul2]
        rw [show s-1-1 = s-2 by omega]
      rw [hsumcut, hfirst, hlast]
      ring

/-- The generic admissible-cutoff partition specializes to the smooth
resolution used by the inverse multipliers. -/
theorem smoothResolution_neighbor_scalarBlock_sum_eq_one_of_ne_zero
    (s : ℕ) {ξ : ℝ}
    (hξ : BrownianSharp.SmoothResolution.scalarBlock s ξ ≠ 0) :
    (∑ j ∈ neighborScales s,
      BrownianSharp.SmoothResolution.scalarBlock j ξ) = 1 := by
  apply neighbor_scalarBlock_sum_eq_one_of_ne_zero smoothResolutionCutoff s
  · simpa [BrownianSharp.SmoothResolution.scalarBlock,
      BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock,
      smoothResolutionCutoff] using hξ

/-- Frequency-by-frequency reconstruction of the actual smooth block from
the neighboring inverse multipliers and the derivative block. This is the
multiplier identity used for the convolution reconstruction; the only
zero-frequency condition is the mean-zero condition needed for level zero. -/
theorem inverseNeighbor_multiplier_reconstructs_block
    (s : ℕ) (n : ℤ) (a : ℂ)
    (hmean : n = 0 → a = 0) :
    (∑ j ∈ neighborScales s,
        BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1 n) *
      ((BrownianSharp.SmoothResolution.scalarBlock s (n:ℝ) : ℂ) *
        (2*Real.pi*Complex.I*(n:ℂ)) * a) =
      (BrownianSharp.SmoothResolution.scalarBlock s (n:ℝ) : ℂ) * a := by
  by_cases hn : n = 0
  · subst n
    by_cases hs : s = 0
    · subst s
      simp [BrownianSharp.ScalarHighFrequency.inverseMultiplier,
        BrownianSharp.SmoothResolution.scalarBlock, hmean rfl]
    · have hblock : BrownianSharp.SmoothResolution.scalarBlock s 0 = 0 := by
        simp [BrownianSharp.SmoothResolution.scalarBlock, hs,
          BrownianSharp.SmoothResolution.cutoff_eq_one (by norm_num : |(0:ℝ)| ≤ 1)]
      simp [BrownianSharp.ScalarHighFrequency.inverseMultiplier,
        hblock]
  · by_cases hblock : BrownianSharp.SmoothResolution.scalarBlock s (n:ℝ) = 0
    · simp [BrownianSharp.ScalarHighFrequency.inverseMultiplier, hn, hblock]
    · have hpartition := smoothResolution_neighbor_scalarBlock_sum_eq_one_of_ne_zero
        s hblock
      have hpartitionC :
          (∑ j ∈ neighborScales s,
            (BrownianSharp.SmoothResolution.scalarBlock j (n:ℝ) : ℂ)) = 1 := by
        exact_mod_cast hpartition
      have hden : (2*Real.pi*Complex.I*(n:ℂ)) ≠ 0 := by
        have htwoPi : (2*Real.pi:ℂ) ≠ 0 := by
          exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
        exact mul_ne_zero (mul_ne_zero htwoPi Complex.I_ne_zero) (by exact_mod_cast hn)
      have hsuminv :
          (∑ j ∈ neighborScales s,
              BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1 n) =
            1 / (2*Real.pi*Complex.I*(n:ℂ)) := by
        calc
          _ = (∑ j ∈ neighborScales s,
                (BrownianSharp.SmoothResolution.scalarBlock j (n:ℝ) : ℂ)) /
                (2*Real.pi*Complex.I*(n:ℂ)) := by
                  simp [BrownianSharp.ScalarHighFrequency.inverseMultiplier, hn,
                    pow_one, ← Finset.sum_div]
          _ = _ := by rw [hpartitionC]
      rw [hsuminv]
      field_simp [hden]

/-- Extending a Fourier polynomial's finite index set does not change its
actual continuous function when the newly added coefficients vanish. -/
theorem polynomialKernel_extend_support
    (A B : Finset ℤ) (c : ℤ → ℂ)
    (hAB : A ⊆ B)
    (hc : ∀ n ∈ B, n ∉ A → c n = 0) :
    polynomialKernel A c = polynomialKernel B c := by
  ext x
  unfold polynomialKernel
  rw [Finset.sum_subset hAB]
  · intro n hn hnA
    rw [hc n hn hnA]
    change (0 : ℂ) • fourier n = 0
    exact zero_smul ℂ (fourier n)

/-- The union of exactly the finite frequency boxes of the neighboring
inverse kernels. -/
def neighborFrequencyUnion (s : ℕ) : Finset ℤ :=
  (neighborScales s).biUnion BrownianSharp.ScalarAtomVariance.scalarFrequencyBox

private theorem neighborScale_mem (s : ℕ) : s ∈ neighborScales s := by
  simp [neighborScales, Finset.mem_filter, Finset.mem_range]

private theorem scalarFrequencyBox_subset_neighborUnion (s j : ℕ)
    (hj : j ∈ neighborScales s) :
    BrownianSharp.ScalarAtomVariance.scalarFrequencyBox j ⊆ neighborFrequencyUnion s := by
  intro n hn
  exact Finset.mem_biUnion.mpr ⟨j, hj, hn⟩

private theorem scalarFrequencyBox_self_subset_neighborUnion (s : ℕ) :
    BrownianSharp.ScalarAtomVariance.scalarFrequencyBox s ⊆ neighborFrequencyUnion s :=
  scalarFrequencyBox_subset_neighborUnion s s (neighborScale_mem s)

private theorem inverseMultiplier_zero_outside_box
    (j : ℕ) {n : ℤ}
    (hn : n ∉ BrownianSharp.ScalarAtomVariance.scalarFrequencyBox j) :
    BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1 n = 0 := by
  have haway : (2:ℝ)^(j+1) ≤ |(n:ℝ)| := by
    simp only [BrownianSharp.ScalarAtomVariance.scalarFrequencyBox,
      Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hlo | hhi
    · have hcast : (n:ℝ) < -((2:ℝ)^(j+1)) := by exact_mod_cast hlo
      exact le_trans (by linarith) (neg_le_abs _)
    · have hcast : (2:ℝ)^(j+1) < (n:ℝ) := by exact_mod_cast hhi
      exact hcast.le.trans (le_abs_self _)
  by_cases hn0 : n = 0
  · simp [BrownianSharp.ScalarHighFrequency.inverseMultiplier, hn0]
  · have hz := BrownianSharp.ScalarKernelL1.scalarBlock_eq_zero_of_two_pow_le_abs j haway
    simp [BrownianSharp.ScalarHighFrequency.inverseMultiplier, hn0, hz]

private theorem scalarBlock_zero_outside_box
    (j : ℕ) {n : ℤ}
    (hn : n ∉ BrownianSharp.ScalarAtomVariance.scalarFrequencyBox j) :
    BrownianSharp.SmoothResolution.scalarBlock j (n:ℝ) = 0 := by
  have haway : (2:ℝ)^(j+1) ≤ |(n:ℝ)| := by
    simp only [BrownianSharp.ScalarAtomVariance.scalarFrequencyBox,
      Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hlo | hhi
    · have hcast : (n:ℝ) < -((2:ℝ)^(j+1)) := by exact_mod_cast hlo
      exact le_trans (by linarith) (neg_le_abs _)
    · have hcast : (2:ℝ)^(j+1) < (n:ℝ) := by exact_mod_cast hhi
      exact hcast.le.trans (le_abs_self _)
  exact BrownianSharp.ScalarKernelL1.scalarBlock_eq_zero_of_two_pow_le_abs j haway

/-- The neighboring inverse kernels together form one finite Fourier
polynomial over their actual union of supports. -/
theorem neighborInverseKernel_eq_polynomialKernel
    (s : ℕ) :
    neighborInverseKernel s =
      polynomialKernel (neighborFrequencyUnion s)
        (fun n => ∑ j ∈ neighborScales s,
          BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1 n) := by
  let S := neighborFrequencyUnion s
  have hkernel (j : ℕ) (hj : j ∈ neighborScales s) :
      BrownianSharp.inverseMultiplierKernel j 1 =
        polynomialKernel S (BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1) := by
    rw [BrownianSharp.inverseMultiplierKernel]
    apply polynomialKernel_extend_support
      (BrownianSharp.ScalarAtomVariance.scalarFrequencyBox j) S
      (BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1)
    · exact scalarFrequencyBox_subset_neighborUnion s j hj
    · intro n hn hnbox
      exact inverseMultiplier_zero_outside_box j hnbox
  ext x
  rw [neighborInverseKernel]
  rw [ContinuousMap.coe_sum, Finset.sum_apply]
  calc
    _ = ∑ j ∈ neighborScales s,
        polynomialKernel S (BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1) x := by
          apply Finset.sum_congr rfl
          intro j hj
          exact congrArg (fun f : C(UnitAddCircle, ℂ) => f x) (hkernel j hj)
    _ = polynomialKernel S
        (fun n => ∑ j ∈ neighborScales s,
          BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1 n) x := by
          simp only [polynomialKernel, ContinuousMap.coe_sum,
            Finset.sum_apply, ContinuousMap.smul_apply]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_smul]

/-- Every smooth scalar block kernel is the polynomial over the common
neighbor-frequency union, with zero coefficients outside its actual block. -/
theorem smoothBlockKernel_eq_polynomialKernel_union
    (s : ℕ) :
    BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel
        BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff s =
      polynomialKernel (neighborFrequencyUnion s)
        (fun n => (BrownianSharp.SmoothResolution.scalarBlock s (n:ℝ) : ℂ)) := by
  rw [BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel]
  apply polynomialKernel_extend_support
    (BrownianSharp.ScalarAtomVariance.scalarFrequencyBox s)
    (neighborFrequencyUnion s)
    (fun n => (BrownianSharp.SmoothResolution.scalarBlock s (n:ℝ) : ℂ))
  · exact scalarFrequencyBox_self_subset_neighborUnion s
  · intro n hn hnbox
    exact_mod_cast scalarBlock_zero_outside_box s hnbox

open BrownianSharp.AlignmentPaperSignedKernelSquareLp

end BrownianSharp.AlignmentPaperInverseDerivativeNeighborIdentity

end
