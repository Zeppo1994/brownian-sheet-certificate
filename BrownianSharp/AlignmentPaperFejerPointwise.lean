import BrownianSharp.TheoremDFejerFourier
import Mathlib.Algebra.Ring.GeomSum

/-! Pointwise bounds for the positive Fejér kernels in terms of the circle
character chord. These estimates are the spatial input to the scalar kernel
decay argument. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperFejerPointwise

open HaarQuarter.TheoremD.FejerFourier
open HaarQuarter.TrigonometricHaarExtraction

def characterChord (x : ℝ) : ℝ := ‖character 1 x - 1‖

def circleCharacterChord (x : UnitAddCircle) : ℝ :=
  ‖fourier (T := (1 : ℝ)) 1 x - 1‖

private theorem character_frequency_add (k l : ℤ) (x : ℝ) :
    character (k + l) x = character k x * character l x := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem character_nat_pow (n : ℕ) (x : ℝ) :
    character (n : ℤ) x = character 1 x ^ n := by
  induction n with
  | zero => simp [character]
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_num
      rw [hcast, character_frequency_add, ih]
      simp [pow_succ]

theorem character_geometric_sum (N : ℕ) (x : ℝ) :
    (∑ r ∈ Finset.range N, character (r : ℤ) x) *
        (character 1 x - 1) = character (N : ℤ) x - 1 := by
  let z := character 1 x
  have hs : (∑ r ∈ Finset.range N, character (r : ℤ) x) =
      ∑ r ∈ Finset.range N, z ^ r := by
    apply Finset.sum_congr rfl
    intro r hr
    simpa [z] using character_nat_pow r x
  rw [hs]
  have hg := geom_sum_mul_add (z - 1) N
  rw [sub_add_cancel] at hg
  rw [character_nat_pow N x]
  change (∑ r ∈ Finset.range N, z ^ r) * (z - 1) = z ^ N - 1
  linear_combination hg

theorem weighted_geometric_sum (N : ℕ) (z : ℂ) :
    (1-z) * (∑ r ∈ Finset.range N, (r:ℂ)*z^r) =
      z * (∑ r ∈ Finset.range N, z^r) - (N:ℂ)*z^N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      rw [pow_succ]
      calc
        _ = ((1-z) * (∑ r ∈ Finset.range N, (r:ℂ)*z^r)) +
            (1-z) * ((N:ℂ)*z^N) := by ring
        _ = (z * (∑ r ∈ Finset.range N, z^r) - (N:ℂ)*z^N) +
            (1-z) * ((N:ℂ)*z^N) := by rw [ih]
        _ = z * ((∑ r ∈ Finset.range N, z^r) + z^N) -
            ((N:ℂ)+1)*z^(N+1) := by ring
        _ = _ := by simp [Finset.sum_range_succ, Nat.cast_succ, pow_succ]

theorem realFejerKernel_le_nat (N : ℕ) (hN : 0 < N) (x : ℝ) :
    realFejerKernel N x ≤ N := by
  rw [realFejerKernel]
  have hsum : ‖∑ r ∈ Finset.range N, character (r : ℤ) x‖ ≤ N := by
    calc
      _ ≤ ∑ r ∈ Finset.range N, ‖character (r : ℤ) x‖ := norm_sum_le _ _
      _ = N := by simp [character_norm, Finset.sum_const, nsmul_eq_mul]
  have hsq : Complex.normSq (∑ r ∈ Finset.range N,
      character (r : ℤ) x) ≤ (N : ℝ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).2 (by exact_mod_cast hsum)
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  exact (div_le_iff₀ hNreal).2 (by simpa [pow_two] using hsq)

theorem realFejerKernel_le_chord (N : ℕ) (hN : 0 < N) (x : ℝ)
    (hx : characterChord x ≠ 0) :
    realFejerKernel N x ≤ 4 / ((N : ℝ) * characterChord x ^ 2) := by
  rw [realFejerKernel]
  let z := character 1 x
  let S := ∑ r ∈ Finset.range N, character (r : ℤ) x
  have hid := character_geometric_sum N x
  have hmul : Complex.normSq S * Complex.normSq (z - 1) =
      Complex.normSq (character (N : ℤ) x - 1) := by
    have h := congrArg Complex.normSq hid
    simpa only [Complex.normSq_mul] using h
  have hnum : Complex.normSq (character (N : ℤ) x - 1) ≤ 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have hnorm : ‖character (N : ℤ) x - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖character (N : ℤ) x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp [character_norm]; norm_num
    have hnon : 0 ≤ ‖character (N : ℤ) x - 1‖ := norm_nonneg _
    nlinarith [sq_nonneg (2 - ‖character (N : ℤ) x - 1‖)]
  have hz : 0 < Complex.normSq (z - 1) := by
    have : ‖z - 1‖ ≠ 0 := by
      intro h
      apply hx
      simpa [characterChord, z, norm_sub_rev] using h
    rw [Complex.normSq_eq_norm_sq]
    positivity
  have hD : Complex.normSq (z - 1) = characterChord x ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    simpa [characterChord, z, norm_sub_rev]
  rw [hD] at hmul
  have hquot : Complex.normSq S ≤ 4 / characterChord x ^ 2 := by
    exact (le_div_iff₀ (by positivity : 0 < characterChord x ^ 2)).2 (by nlinarith)
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ hNreal).2
  calc
    Complex.normSq S ≤ 4 / characterChord x ^ 2 := hquot
    _ = 4 / ((N : ℝ) * characterChord x ^ 2) * N := by field_simp

theorem realFejerKernel_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ realFejerKernel N x := by
  unfold realFejerKernel
  exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fejerFourierPolynomial_pointwise_decay (N : ℕ) (hN : 0 < N)
    (x : UnitAddCircle) :
    ‖fejerFourierPolynomial N x‖ ≤
      8 * (N : ℝ) / (1 + ((N : ℝ) * circleCharacterChord x) ^ 2) := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
      have hchar : fourier (T := (1 : ℝ)) 1 (t : UnitAddCircle) = character 1 t := by
        simpa [HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter] using
          HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter_coe 1 t
      rw [fejerFourierPolynomial_eval_eq_real]
      have hchord : circleCharacterChord (t : UnitAddCircle) = characterChord t := by
        simp [circleCharacterChord, characterChord, hchar, norm_sub_rev]
      rw [hchord]
      have hreal : 0 ≤ realFejerKernel N t := realFejerKernel_nonneg N t
      have hlow := realFejerKernel_le_nat N hN t
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreal]
      by_cases hsmall : (N : ℝ) * characterChord t ≤ 1
      · have hqnon : 0 ≤ (N : ℝ) * characterChord t :=
          mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
        have hsq : ((N : ℝ) * characterChord t) ^ 2 ≤ 1 := by nlinarith
        have hden : 1 + ((N : ℝ) * characterChord t) ^ 2 ≤ 2 := by nlinarith
        have hpos : 0 < 1 + ((N : ℝ) * characterChord t) ^ 2 := by positivity
        have : (N : ℝ) ≤ 8 * (N : ℝ) / (1 + ((N : ℝ) * characterChord t) ^ 2) := by
          rw [le_div_iff₀ hpos]
          nlinarith [show 0 ≤ (N : ℝ) by positivity]
        exact hlow.trans this
      · have hlarge : 1 < (N : ℝ) * characterChord t := lt_of_not_ge hsmall
        have hD : characterChord t ≠ 0 := by
          intro hzero
          rw [hzero] at hlarge
          norm_num at hlarge
        have hdecay := realFejerKernel_le_chord N hN t hD
        have hden : 1 + ((N : ℝ) * characterChord t) ^ 2 ≤
            2 * ((N : ℝ) * characterChord t) ^ 2 := by nlinarith
        have hpos : 0 < (N : ℝ) * characterChord t ^ 2 := by positivity
        have htarget : 4 / ((N : ℝ) * characterChord t ^ 2) ≤
            8 * (N : ℝ) / (1 + ((N : ℝ) * characterChord t) ^ 2) := by
          rw [div_le_div_iff₀ hpos (by positivity)]
          nlinarith [sq_nonneg ((N : ℝ) * characterChord t)]
        exact hdecay.trans htarget

end BrownianSharp.AlignmentPaperFejerPointwise
