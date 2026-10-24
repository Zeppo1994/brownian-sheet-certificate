import BrownianSharp.AlignmentGaussianHolderFiniteFeature
import BrownianSharp.AlignmentExponentialFiniteGaussianSmallBall
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open HaarQuarter
open BrownianSharp

namespace BrownianSharp.AlignmentGaussianHolderGradedHalfMass

open BrownianSharp.AlignmentGaussianFiniteFeature
open BrownianSharp.AlignmentGaussianHolderFiniteFeature
open BrownianSharp.AlignmentHolderGaussianChaining
open BrownianSharp.AlignmentExponentialFiniteGaussianSmallBall

private def gradedHalfMassIndex (β h : ℝ) : ℕ := Nat.ceil (β/(2*h)) + 1

private theorem ratio_le_gradedHalfMassIndex {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    β/(2*h) ≤ (gradedHalfMassIndex β h : ℝ) := by
  dsimp [gradedHalfMassIndex]
  have hceil : β/(2*h) ≤ (Nat.ceil (β/(2*h)) : ℝ) := Nat.le_ceil _
  exact le_trans hceil (by exact_mod_cast Nat.le_succ (Nat.ceil (β/(2*h))))

private theorem gradedHalfMass_index_bound {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) (N : ℕ) :
    β * (N : ℝ) ≤ 2*h*(gradedHalfMassIndex β h : ℝ) * (N + 1 : ℝ) := by
  have hK := ratio_le_gradedHalfMassIndex hβ hh
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have htwo : 0 < 2*h := by positivity
  have hmul := mul_le_mul_of_nonneg_right hK (mul_nonneg htwo.le hN)
  have heq : (β/(2*h))*(2*h*(N:ℝ))=β*(N:ℝ) := by field_simp
  nlinarith

private theorem gradedHalfMass_height_bound {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) (N : ℕ) :
    ((gradedHalfMassIndex β h * (N + 1) + 1 : ℕ) : ℝ) ≤
      ((gradedHalfMassIndex β h + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) := by
  have hK : 0 ≤ (gradedHalfMassIndex β h : ℝ) := Nat.cast_nonneg _
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  dsimp [gradedHalfMassIndex]
  push_cast
  nlinarith

/-- Uniform half-mass confinement for finite Gaussian feature fields with a
dyadic polynomial variance profile. Constants are independent of the finite
feature index type, feature maps, and level N. -/
theorem finiteGaussianFeaturePath_half_mass_of_graded_variance
    {d : ℕ}
    (β h C R : ℝ) (k : ℕ) (hβ : 0 < β) (hh : 0 < h)
    (hC : 0 ≤ C) (hR : 0 ≤ R) : ∃ A : ℝ, 0 < A ∧ ∀ {ι : Type*} [Fintype ι] (N : ℕ)
      (v : ι → C(HaarQuarter.BrownianCubeAnchor d, ℝ)),
      (∀ x, ∑ i, (v i x)^2 ≤
        C * (Real.rpow 2 (-β * (N : ℝ) / 2))^2 * (((N + 1 : ℕ) : ℝ)^k)) →
      (∀ x y, ∑ i, (v i x - v i y)^2 ≤ R * (dist x y)^(2*h)) →
      (1 / 2 : ℝ≥0∞) ≤
        (BrownianSharp.productStandardGaussian ι)
          {z | ‖finiteGaussianFeaturePath v z‖ ≤
            A * Real.rpow 2 (-β * (N : ℝ) / 2) *
              Real.sqrt (((N + 1 : ℕ) : ℝ)^(k + 1))} := by
  let K := gradedHalfMassIndex β h
  let S := holderChainingConstant d h * Real.sqrt ((K + 1 : ℕ) : ℝ) *
    (1 + Real.sqrt C + Real.sqrt R * (2:ℝ)^h)
  let A := 2 * S
  have hKbound (N : ℕ) : β * (N : ℝ) ≤ 2*h*(K : ℝ) * (N + 1 : ℝ) :=
    gradedHalfMass_index_bound hβ hh N
  have hHbound (N : ℕ) :
      ((K * (N + 1) + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    simpa [K] using gradedHalfMass_height_bound hβ hh N
  have hS : 0 < S := by
    dsimp [S]
    exact mul_pos (mul_pos (holderChainingConstant_pos d h) (Real.sqrt_pos.2 (by positivity)))
      (by positivity)
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · intro ι _ N v hvar hincrement
    let rate := Real.rpow 2 (-β * (N : ℝ) / 2)
    let base := ((N + 1 : ℕ) : ℝ)
    let σ := Real.sqrt C * rate * Real.sqrt (base^k)
    let H := K * (N + 1)
    have hrate : 0 < rate := by
      dsimp [rate]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hbase : 1 ≤ base := by dsimp [base]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    have hσ : 0 ≤ σ := by dsimp [σ]; positivity
    have hσsq : σ^2 = C * rate^2 * base^k := by
      dsimp [σ]
      rw [mul_pow, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt (pow_nonneg (by positivity : 0 ≤ base) k)]
    have hvar' : ∀ x, ∑ i, (v i x)^2 ≤ σ^2 := by
      intro x
      have h := hvar x
      rw [hσsq]
      simpa [rate, base] using h
    have hH : β * (N : ℝ) ≤ 2*h*(H : ℝ) := by
      simpa [H, Nat.cast_mul, Nat.cast_add, mul_assoc] using hKbound N
    have hdecay :
        (2 : ℝ)^(-h*(H : ℝ)) ≤ rate := by
      change (2 : ℝ) ^ (-h*(H : ℝ)) ≤
        (2 : ℝ) ^ (-β * (N : ℝ) / 2)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [hH]
    have hrootH : Real.sqrt ((H + 1 : ℕ) : ℝ) ≤
        Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt base := by
      have hh := hHbound N
      calc
        Real.sqrt ((H + 1 : ℕ) : ℝ) ≤
            Real.sqrt (((K + 1 : ℕ) : ℝ) * base) := by
          apply Real.sqrt_le_sqrt
          simpa [base, H, Nat.cast_add, Nat.cast_mul] using hh
        _ = Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt base := by
          rw [Real.sqrt_mul (by positivity)]
    have hpoly : Real.sqrt base * Real.sqrt (base^k) ≤
        Real.sqrt (base^(k+1)) := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ base)]
      apply Real.sqrt_le_sqrt
      rw [pow_succ]
      exact le_of_eq (mul_comm base (base^k))
    have hbase_le : Real.sqrt base ≤ Real.sqrt (base^(k+1)) := by
      apply Real.sqrt_le_sqrt
      have hpow : base ≤ base^(k+1) := by
        calc
          base = base^1 := by simp
          _ ≤ base^(k+1) := by
            gcongr
            omega
      exact hpow
    let M := S * rate * Real.sqrt (base^(k+1))
    have hM : 0 < M := by
      dsimp [M]
      positivity
    have hchain := finiteGaussianFeaturePath_expected_norm_holder h hh v σ R
      hσ hR hvar' hincrement H
    have hmean :
        (∫ z : ι → ℝ, ‖finiteGaussianFeaturePath v z‖
          ∂BrownianSharp.productStandardGaussian ι) ≤ M := by
      have hchain' := hchain.2
      have hroot :
          Real.sqrt ((H : ℝ) + 1) ≤
            Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt base := by
        simpa [H, base] using hrootH
      have hnormRate : (2 : ℝ)^(-h*(H : ℝ)) ≤ rate := by
        exact hdecay
      have hfirst : Real.sqrt ((H : ℝ) + 1) * σ ≤
          Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt C * rate *
            Real.sqrt (base^(k+1)) := by
        change Real.sqrt ((H : ℝ) + 1) *
            (Real.sqrt C * rate * Real.sqrt (base^k)) ≤ _
        calc
          _ ≤ (Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt base) *
              (Real.sqrt C * rate * Real.sqrt (base^k)) :=
                mul_le_mul_of_nonneg_right hroot (by positivity)
          _ = Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt C * rate *
              (Real.sqrt base * Real.sqrt (base^k)) := by ring
          _ ≤ _ := by gcongr
      have hsecond : Real.sqrt ((H : ℝ) + 1) *
          (Real.sqrt R * (2:ℝ)^h * (2 : ℝ)^(-h*(H:ℝ))) ≤
          Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt R * (2:ℝ)^h * rate *
            Real.sqrt (base^(k+1)) := by
        calc
          _ ≤ (Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt base) *
              (Real.sqrt R * (2:ℝ)^h * rate) := by gcongr
          _ ≤ _ := by
            rw [show (Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt base) *
                (Real.sqrt R * (2:ℝ)^h * rate) =
                  Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt R * (2:ℝ)^h * rate * Real.sqrt base by ring]
            gcongr
      calc
        _ ≤ holderChainingConstant d h * Real.sqrt ((H : ℝ) + 1) *
            (σ + Real.sqrt R * (2:ℝ)^h * (2 : ℝ)^(-h*(H:ℝ))) := hchain'
        _ ≤ holderChainingConstant d h *
            (Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt C * rate *
                Real.sqrt (base^(k+1)) +
              Real.sqrt ((K + 1 : ℕ) : ℝ) * Real.sqrt R * (2:ℝ)^h * rate *
                Real.sqrt (base^(k+1))) := by
          have hc := holderChainingConstant_pos d h |>.le
          calc
            _ = holderChainingConstant d h * (Real.sqrt ((H : ℝ) + 1) * σ +
                Real.sqrt ((H : ℝ) + 1) *
                  (Real.sqrt R * (2:ℝ)^h * (2 : ℝ)^(-h*(H:ℝ)))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hc
            _ = _ := by ring
        _ ≤ M := by
          dsimp [M, S]
          have hc : 0 ≤ holderChainingConstant d h := (holderChainingConstant_pos d h).le
          have hk : 0 ≤ Real.sqrt ((K + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
          have hr : 0 ≤ rate := hrate.le
          have hf : 0 ≤ holderChainingConstant d h * Real.sqrt ((K + 1 : ℕ) : ℝ) *
              rate * Real.sqrt (base^(k+1)) := by positivity
          have hz : 0 ≤ holderChainingConstant d h * Real.sqrt ((K + 1 : ℕ) : ℝ) *
              rate * Real.sqrt R * (2:ℝ)^h * Real.sqrt (base^(k+1)) := by positivity
          nlinarith [hz]
    have hhalf : (1 / 2 : ℝ≥0∞) ≤
        (BrownianSharp.productStandardGaussian ι)
          {z | ‖finiteGaussianFeaturePath v z‖ ≤ 2 * M} := by
      exact gaussian_nonneg_energy_cutoff_mass _ _
        (by
          exact (continuous_norm.comp (finiteGaussianFeaturePath_continuous v)).measurable)
        hchain.1 (fun z => norm_nonneg _) hM hmean
    have hrad : 2 * M ≤ A * rate * Real.sqrt (base^(k+1)) := by
      calc
        2 * M = A * rate * Real.sqrt (base^(k+1)) := by
          dsimp [M, A]
          ring
        _ ≤ _ := le_rfl
    have hsubset :
        {z | ‖finiteGaussianFeaturePath v z‖ ≤ 2 * M} ⊆
          {z | ‖finiteGaussianFeaturePath v z‖ ≤
            A * rate * Real.sqrt (base^(k+1))} := by
      intro z hz
      exact hz.trans hrad
    have hprob :
        (BrownianSharp.productStandardGaussian ι)
            {z | ‖finiteGaussianFeaturePath v z‖ ≤ 2 * M} ≤
          (BrownianSharp.productStandardGaussian ι)
            {z | ‖finiteGaussianFeaturePath v z‖ ≤
              A * rate * Real.sqrt (base^(k+1))} := measure_mono hsubset
    change (1 / 2 : ℝ≥0∞) ≤
      (BrownianSharp.productStandardGaussian ι)
        {z | ‖finiteGaussianFeaturePath v z‖ ≤
          A * rate * Real.sqrt (base^(k+1))}
    exact hhalf.trans hprob

end BrownianSharp.AlignmentGaussianHolderGradedHalfMass
