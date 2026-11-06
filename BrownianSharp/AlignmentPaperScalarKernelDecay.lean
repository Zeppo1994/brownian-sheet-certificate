import BrownianSharp.AlignmentPaperFejerPointwise
import BrownianSharp.FejerMixture
import Mathlib.Tactic

/-! Pointwise decay for finite smooth Fejér mixtures from the sampled
second-derivative bound. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperScalarKernelDecay

open BrownianSharp.AlignmentPaperFejerPointwise
open BrownianSharp.ScalarKernelL1
open HaarQuarter.TheoremD.FejerFourier

theorem fejerMixture_decay_of_weight_bound
    (J N : ℕ) (R M : ℝ) (hN : 0 < N) (hM : 0 ≤ M)
    (hR : 1 ≤ R) (hJ : (J : ℝ) ≤ R * (N : ℝ))
    (c : ℕ → ℂ) (x : UnitAddCircle)
    (hw : ∀ j ∈ Finset.range J,
      ‖secondWeight c j‖ ≤ M * ((j + 1 : ℕ) : ℝ) / (N : ℝ) ^ 2) :
    ‖fejerMixture J c x‖ ≤
      16 * R ^ 3 * M * (N : ℝ) /
        (1 + ((N : ℝ) * circleCharacterChord (x : UnitAddCircle)) ^ 2) := by
  classical
  let D := circleCharacterChord (x : UnitAddCircle)
  have hD : 0 ≤ D := by dsimp [D, circleCharacterChord]; positivity
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNle : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hJnon : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
  have hsumForm :
      ‖fejerMixture J c x‖ ≤
        (8 * M / (N : ℝ) ^ 2) *
          (∑ j ∈ Finset.range J,
            (((j + 1 : ℕ) : ℝ) ^ 2 /
              (1 + (((j + 1 : ℕ) : ℝ) * D) ^ 2))) := by
    unfold fejerMixture fejerKernel
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul,
      Finset.sum_apply]
    calc
      _ ≤ ∑ j ∈ Finset.range J,
          ‖secondWeight c j‖ *
            ‖fejerFourierPolynomial (j+1) x‖ := by
        calc
          _ ≤ ∑ j ∈ Finset.range J,
              ‖secondWeight c j * fejerFourierPolynomial (j+1) x‖ := norm_sum_le _ _
          _ = _ := by simp [norm_mul]
      _ ≤ ∑ j ∈ Finset.range J,
          (M * ((j + 1 : ℕ) : ℝ) / (N : ℝ)^2) *
            (8 * ((j+1:ℕ):ℝ) /
              (1 + (((j+1:ℕ):ℝ) * D)^2)) := by
        apply Finset.sum_le_sum
        intro j hj
        have ht : 0 < j+1 := by omega
        have hweight := hw j hj
        have hF := fejerFourierPolynomial_pointwise_decay (j+1) ht x
        exact mul_le_mul hweight hF (norm_nonneg _) (by positivity)
      _ = (8 * M / (N : ℝ)^2) *
          (∑ j ∈ Finset.range J,
            (((j + 1 : ℕ) : ℝ)^2 /
              (1 + (((j + 1 : ℕ) : ℝ) * D)^2))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hsmallSum : (∑ j ∈ Finset.range J,
        (((j + 1 : ℕ) : ℝ)^2 /
          (1 + (((j + 1 : ℕ) : ℝ) * D)^2))) ≤ (J : ℝ)^3 := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, ((j + 1 : ℕ) : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hpos : 0 < 1 + (((j+1:ℕ):ℝ)*D)^2 := by positivity
        rw [div_le_iff₀ hpos]
        nlinarith [sq_nonneg (((j+1:ℕ):ℝ)*D)]
      _ ≤ ∑ _j ∈ Finset.range J, (J : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : ((j+1:ℕ):ℝ) ≤ (J:ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
        nlinarith [sq_nonneg ((J:ℝ) - ((j+1:ℕ):ℝ))]
      _ = (J:ℝ)^3 := by simp [Finset.sum_const, nsmul_eq_mul, pow_succ, mul_comm]
  have hlargeSum (hDpos : 0 < D) :
      (∑ j ∈ Finset.range J,
        (((j + 1 : ℕ) : ℝ)^2 /
          (1 + (((j + 1 : ℕ) : ℝ) * D)^2))) ≤ (J : ℝ) / D^2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range J, (1 / D^2) := by
        apply Finset.sum_le_sum
        intro j hj
        have ht : 0 < ((j+1:ℕ):ℝ) := by positivity
        have hden : 0 < 1 + (((j+1:ℕ):ℝ)*D)^2 := by positivity
        rw [div_le_iff₀ hden]
        have hDsquare : 0 < D^2 := sq_pos_of_pos hDpos
        field_simp [ne_of_gt hDsquare]
        nlinarith [sq_nonneg (((j+1:ℕ):ℝ)*D)]
      _ = (J:ℝ) / D^2 := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        <;> ring
  by_cases hsmall : (N:ℝ) * D ≤ 1
  · have hJbound : (J:ℝ)^3 ≤ R^3 * (N:ℝ)^3 := by
      calc
        (J:ℝ)^3 ≤ (R * (N:ℝ))^3 := pow_le_pow_left₀ hJnon hJ 3
        _ = R^3 * (N:ℝ)^3 := by rw [mul_pow]
    have hden : 1 + ((N:ℝ)*D)^2 ≤ 2 := by
      have hqnon : 0 ≤ (N:ℝ)*D := mul_nonneg (le_trans (by norm_num) hNle) hD
      nlinarith
    have hdenpos : 0 < 1 + ((N:ℝ)*D)^2 := by positivity
    calc
      _ ≤ (8*M/(N:ℝ)^2) *
          (∑ j ∈ Finset.range J,
            (((j + 1 : ℕ) : ℝ)^2 /
              (1 + (((j + 1 : ℕ) : ℝ) * D)^2))) := hsumForm
      _ ≤ (8*M/(N:ℝ)^2) * (J:ℝ)^3 :=
        mul_le_mul_of_nonneg_left hsmallSum (by positivity)
      _ ≤ 8 * R^3 * M * (N:ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hJbound (by positivity : 0 ≤ 8*M/(N:ℝ)^2)
        have hratio : (8*M/(N:ℝ)^2) * (R^3*(N:ℝ)^3) =
            8*R^3*M*(N:ℝ) := by field_simp
        rw [hratio] at hmul
        exact hmul
      _ ≤ 16 * R^3 * M * (N:ℝ) /
          (1 + ((N:ℝ)*D)^2) := by
        rw [le_div_iff₀ hdenpos]
        nlinarith [show 0 ≤ R^3*M*(N:ℝ) by positivity]
  · have hlarge : 1 < (N:ℝ)*D := lt_of_not_ge hsmall
    have hDpos : 0 < D := by
      by_contra h
      have hz : D = 0 := le_antisymm (le_of_not_gt h) hD
      rw [hz] at hlarge
      norm_num at hlarge
    have hJbound : (J:ℝ)/D^2 ≤ R*(N:ℝ)/D^2 := by
      exact div_le_div_of_nonneg_right hJ (sq_nonneg D)
    have hden : 1 + ((N:ℝ)*D)^2 ≤ 2*((N:ℝ)*D)^2 := by nlinarith
    have hdenpos : 0 < 1 + ((N:ℝ)*D)^2 := by positivity
    calc
      _ ≤ (8*M/(N:ℝ)^2) *
          (∑ j ∈ Finset.range J,
            (((j + 1 : ℕ) : ℝ)^2 /
              (1 + (((j + 1 : ℕ) : ℝ) * D)^2))) := by
        exact hsumForm
      _ ≤ (8*M/(N:ℝ)^2) * ((J:ℝ)/D^2) := by
        exact mul_le_mul_of_nonneg_left (hlargeSum hDpos) (by positivity)
      _ ≤ 8*R*M/((N:ℝ)*D^2) := by
        calc
          _ ≤ (8*M/(N:ℝ)^2) * ((R*(N:ℝ))/D^2) :=
            mul_le_mul_of_nonneg_left hJbound (by positivity)
          _ = 8*R*M/((N:ℝ)*D^2) := by field_simp
      _ ≤ 16*R^3*M*(N:ℝ)/(1+((N:ℝ)*D)^2) := by
        have hR3 : 1 ≤ R^3 :=
          le_trans hR (le_self_pow₀ hR (by norm_num : (3:ℕ) ≠ 0))
        have hqpos : 0 < ((N:ℝ)*D)^2 := by positivity
        have hfactor : 8*R*M*(N:ℝ) / ((N:ℝ)*D)^2 ≤
            16*R^3*M*(N:ℝ) / (1+((N:ℝ)*D)^2) := by
          rw [div_le_div_iff₀ hqpos hdenpos]
          have hA : 0 ≤ 8*R*M*(N:ℝ) := by positivity
          have hbase : 8*R*M*(N:ℝ)*(1+((N:ℝ)*D)^2) ≤
              16*R*M*(N:ℝ)*((N:ℝ)*D)^2 := by
            have hh := mul_le_mul_of_nonneg_left hden hA
            nlinarith
          have hRle : R ≤ R^3 := by
            have h1 : 0 ≤ R-1 := by linarith
            have h2 : 0 ≤ R+1 := by linarith
            nlinarith [mul_nonneg h1 h2]
          have hconst : 16*R*M*(N:ℝ) ≤ 16*R^3*M*(N:ℝ) := by
            calc
              16*R*M*(N:ℝ) = 16*M*(N:ℝ)*R := by ring
              _ ≤ 16*M*(N:ℝ)*R^3 :=
                mul_le_mul_of_nonneg_left hRle (by positivity)
              _ = 16*R^3*M*(N:ℝ) := by ring
          have hsecond := mul_le_mul_of_nonneg_right hconst
            (sq_nonneg ((N:ℝ)*D))
          nlinarith
        have hconvert : 8*R*M/((N:ℝ)*D^2) =
            8*R*M*(N:ℝ)/((N:ℝ)*D)^2 := by field_simp
        rw [hconvert]
        exact hfactor

end BrownianSharp.AlignmentPaperScalarKernelDecay
