import BrownianSharp.AlignmentIntegerFractionalApproximationLower
import BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
import Mathlib.Tactic

/-! Homogeneous one-step lower bound for the order-two sine block. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentIntegerTwoHomogeneousLower

open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
open BrownianSharp.AlignmentOrdinaryIntegrationLower

theorem integerTwoL2Operator_norm_sq_of_jet (K D : ℕ)
    (c : Fin D → ℝ) (hc : c ∈ sineJetKernel K D) :
    ‖integerTwoL2Operator (sineSecondSourceMap K D c)‖^2 =
      ∑ i : Fin D, (c i)^2 := by
  rw [integerTwoL2Operator_source_apply K D c hc]
  have hs := orthonormal_sum_norm_sq
    (fun i : Fin D => shiftedSineMode K i.val)
    (shiftedSineMode_orthonormal K D) (fun i => -c i)
  calc
    ‖-∑ i : Fin D, c i • shiftedSineMode K i.val‖^2 =
        ‖∑ i : Fin D, (-c i) • shiftedSineMode K i.val‖^2 := by
          congr 1
          simp [Finset.sum_neg_distrib, neg_smul]
    _ = ∑ i : Fin D, ((-c i))^2 := hs
    _ = ∑ i : Fin D, (c i)^2 := by simp

/-- Every first-jet-compatible sine block loses at most the square of its
largest frequency under one order-two integration, homogeneously in the
source norm. -/
theorem integerTwoL2Operator_homogeneous_lower_of_jet
    (K D : ℕ) (hD : 0 < D) (c : Fin D → ℝ)
    (hc : c ∈ sineJetKernel K D) :
    ((halfFrequency (K+D))^2)⁻¹ *
        ‖sineSecondSourceMap K D c‖ ≤
      ‖integerTwoL2Operator (sineSecondSourceMap K D c)‖ := by
  let freqMax : ℝ := halfFrequency (K+D)
  have hfreqMax : 0 < freqMax := by
    dsimp [freqMax, halfFrequency]
    positivity
  have hfreq (i : Fin D) :
      0 < halfFrequency (K+i.val) ∧ halfFrequency (K+i.val) ≤ freqMax := by
    constructor
    · dsimp [halfFrequency]
      positivity
    · dsimp [freqMax, halfFrequency]
      have hi : (K+i.val:ℕ) ≤ K+D := by omega
      have hcast : ((K+i.val:ℕ):ℝ) ≤ (K+D:ℕ) := by exact_mod_cast hi
      nlinarith [Real.pi_pos]
  have hsumle :
      (∑ i : Fin D, (c i * (halfFrequency (K+i.val))^2)^2) ≤
        freqMax^4 * ∑ i : Fin D, (c i)^2 := by
    calc
      _ ≤ ∑ i : Fin D, (c i)^2 * freqMax^4 := by
        apply Finset.sum_le_sum
        intro i hi
        have hf := hfreq i
        have hsquare : (halfFrequency (K+i.val))^4 ≤ freqMax^4 := by
          gcongr
          exact (hfreq i).1.le
          exact hf.2
        nlinarith [sq_nonneg (c i)]
      _ = freqMax^4 * ∑ i : Fin D, (c i)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hsource := sineSecondSourceMap_norm_sq K D c
  have htarget := integerTwoL2Operator_norm_sq_of_jet K D c hc
  have hnormsq :
      ‖sineSecondSourceMap K D c‖^2 ≤
        (freqMax^2 * ‖integerTwoL2Operator (sineSecondSourceMap K D c)‖)^2 := by
    rw [hsource]
    calc
      ∑ i : Fin D, (c i * (halfFrequency (K+i.val))^2)^2 ≤
          freqMax^4 * ∑ i : Fin D, (c i)^2 := hsumle
      _ = (freqMax^2 * ‖integerTwoL2Operator
          (sineSecondSourceMap K D c)‖)^2 := by
        rw [← htarget]
        ring
  have hnorm : ‖sineSecondSourceMap K D c‖ ≤
      freqMax^2 * ‖integerTwoL2Operator (sineSecondSourceMap K D c)‖ :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).1 hnormsq
  have hmul := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (sq_nonneg freqMax))
  have hcancel : (freqMax^2)⁻¹ * freqMax^2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hfreqMax.ne')
  calc
    ((halfFrequency (K+D))^2)⁻¹ * ‖sineSecondSourceMap K D c‖ =
        (freqMax^2)⁻¹ * ‖sineSecondSourceMap K D c‖ := by rfl
    _ ≤ (freqMax^2)⁻¹ *
        (freqMax^2 * ‖integerTwoL2Operator (sineSecondSourceMap K D c)‖) := hmul
    _ = ‖integerTwoL2Operator (sineSecondSourceMap K D c)‖ := by
      rw [← mul_assoc, hcancel, one_mul]

/-- Iterating the homogeneous one-step estimate across the common endpoint
jet kernel gives the expected largest-frequency loss for every even order. -/
theorem integerTwoL2Iterate_homogeneous_lower_of_common_jet
    (K D m : ℕ) (hD : 0 < D) (c : Fin D → ℝ)
    (hc : c ∈ (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
      (evenOrderJetConstraints K D m)).ker) :
    (((halfFrequency (K+D))^2)⁻¹)^m * ‖sineSecondSourceMap K D c‖ ≤
      ‖integerTwoL2Iterate m (sineSecondSourceMap K D c)‖ := by
  induction m generalizing c with
  | zero => simp [integerTwoL2Iterate]
  | succ m ih =>
      have hall := (evenOrderJetKernel_mem_iff K D (m+1) c).mp hc
      have hsmall : c ∈
          (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
            (evenOrderJetConstraints K D m)).ker :=
        (evenOrderJetKernel_mem_iff K D m c).mpr (fun j => hall j.castSucc)
      have hprev := ih c hsmall
      let cₘ := ((inverseFrequencySquared K D)^m) c
      have hlast : cₘ ∈ sineJetKernel K D :=
        evenOrderJetKernel_iterates_mem K D (m+1) c hc ⟨m, by omega⟩
      have hone := integerTwoL2Operator_homogeneous_lower_of_jet
        K D hD cₘ hlast
      have hiterate := integerTwoL2Iterate_source_apply K D m c hc
      have hnormprev :
          ‖integerTwoL2Iterate m (sineSecondSourceMap K D c)‖ =
            ‖sineSecondSourceMap K D cₘ‖ := by
        rw [hiterate]
        simp [cₘ, norm_smul]
      have hnormnext :
          ‖integerTwoL2Iterate (m+1) (sineSecondSourceMap K D c)‖ =
            ‖integerTwoL2Operator (sineSecondSourceMap K D cₘ)‖ := by
        rw [integerTwoL2Iterate, hiterate]
        simp [cₘ, map_smul, norm_smul]
      have hσ : 0 ≤ ((halfFrequency (K+D))^2)⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_left hprev hσ
      calc
        (((halfFrequency (K+D))^2)⁻¹)^(m+1) *
            ‖sineSecondSourceMap K D c‖ =
            ((halfFrequency (K+D))^2)⁻¹ *
              ((((halfFrequency (K+D))^2)⁻¹)^m *
                ‖sineSecondSourceMap K D c‖) := by ring
        _ ≤ ((halfFrequency (K+D))^2)⁻¹ *
              ‖integerTwoL2Iterate m (sineSecondSourceMap K D c)‖ := hmul
        _ = ((halfFrequency (K+D))^2)⁻¹ * ‖sineSecondSourceMap K D cₘ‖ := by
              rw [hnormprev]
        _ ≤ ‖integerTwoL2Operator (sineSecondSourceMap K D cₘ)‖ := hone
        _ = ‖integerTwoL2Iterate (m+1) (sineSecondSourceMap K D c)‖ := by
              rw [hnormnext]

end BrownianSharp.AlignmentIntegerTwoHomogeneousLower
