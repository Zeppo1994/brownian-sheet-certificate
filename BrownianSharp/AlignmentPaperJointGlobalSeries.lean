import BrownianSharp.AlignmentPaperJointGlobalCover
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Summability and finite-window tail control for the global grade-series class. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointGlobalSeries

open BrownianSharp.AlignmentPaperJointGlobalCover

theorem gradeSeriesNormEnvelope_summable
    {d : ℕ} {p A : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) : Summable (gradeSeriesNormEnvelope d p A) := by
  let q : ℕ := d - 1
  let δ : ℝ := (1 - 1 / p) * Real.log 2
  let C : ℝ := (2 * (5 : ℝ)^d) * (Real.sqrt ((25 / 4 : ℝ)^d) + 1) * A
  have hq : 0 < q := by dsimp [q]; omega
  have hδ : 0 < δ := by
    apply mul_pos
    · have hp0 : 0 < p := by linarith
      have : 1 / p < 1 := (div_lt_one hp0).2 (by linarith)
      linarith
    · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hbase (n : ℕ) : (n + 1 : ℝ) ^ ((d - 1 : ℝ) / p) ≤ (n + 1 : ℝ) ^ (q : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ n + 1 by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    have hdp : 0 < p := by linarith
    have hqreal : (q : ℝ) = (d : ℝ) - 1 := by
      dsimp [q]
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    rw [hqreal]
    have hfrac : 1 / p ≤ 1 := (div_le_one hdp).2 (by linarith)
    have hcoef : 0 ≤ (d : ℝ) - 1 := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      linarith
    calc
      ((d : ℝ) - 1) / p = ((d : ℝ) - 1) * (1 / p) := by ring
      _ ≤ ((d : ℝ) - 1) * 1 := mul_le_mul_of_nonneg_left hfrac hcoef
      _ = (d : ℝ) - 1 := by ring
  have hpowexp (n : ℕ) :
      (2 : ℝ) ^ (-(1 - 1 / p) * (n : ℝ)) = Real.exp (-δ * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [δ]
    ring
  have hpoly (n : ℕ) (hn : 1 ≤ n) :
      (n + 1 : ℝ) ^ q ≤ (2 : ℝ)^q * (n : ℝ)^q := by
    have hnR : (n : ℝ) + 1 ≤ 2 * n := by exact_mod_cast (by omega : n + 1 ≤ 2 * n)
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (n + 1 : ℝ)) hnR q
    convert hpow using 1 <;> ring
  have hexp (n : ℕ) : Real.exp (-δ * (n : ℝ)) ≤
      Real.exp (-(δ / 2) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg hδ.le hn]
  have hmajor (n : ℕ) (hn : 1 ≤ n) :
      gradeSeriesNormEnvelope d p A n ≤
        (C * (2 : ℝ)^q) * (n : ℝ)^q * Real.exp (-(δ / 2) * (n : ℝ)) := by
    unfold gradeSeriesNormEnvelope
    rw [hpowexp]
    have hbase' := hbase n
    have hpoly' := hpoly n hn
    have hexp' := hexp n
    have hqreal : (q : ℝ) = (d : ℝ) - 1 := by
      dsimp [q]
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    have hrpow : (n + 1 : ℝ) ^ (q : ℝ) = (n + 1 : ℝ) ^ q := by
      rw [← Real.rpow_natCast]
    have hpow_nonneg : 0 ≤ (n + 1 : ℝ) ^ ((d - 1 : ℝ) / p) := by positivity
    calc
      C * Real.exp (-δ * (n : ℝ)) * (n + 1 : ℝ) ^ ((d - 1 : ℝ) / p)
          ≤ C * Real.exp (-δ * (n : ℝ)) * ((n + 1 : ℝ) ^ (q : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hbase' (mul_nonneg hC.le (Real.exp_nonneg _))
      _ = C * Real.exp (-δ * (n : ℝ)) * ((n + 1 : ℝ) ^ q) := by rw [hrpow]
      _ ≤ C * Real.exp (-(δ / 2) * (n : ℝ)) * ((2 : ℝ)^q * (n : ℝ)^q) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hexp' hC.le)
              hpoly' (by positivity) (by positivity)
      _ = (C * (2 : ℝ)^q) * (n : ℝ)^q * Real.exp (-(δ / 2) * (n : ℝ)) := by ring
  have hsum := Real.summable_pow_mul_exp_neg_nat_mul q (show 0 < δ / 2 by linarith)
  have hsum' : Summable (fun n : ℕ =>
      (C * (2 : ℝ)^q) * (n : ℝ)^q * Real.exp (-(δ / 2) * (n : ℝ))) := by
    simpa only [mul_assoc] using hsum.mul_left (C * (2 : ℝ)^q)
  apply Summable.of_norm_bounded_eventually_nat hsum'
  filter_upwards [Filter.eventually_atTop.2 ⟨1, by
    intro n hn
    exact hmajor n hn⟩] with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gradeSeriesNormEnvelope d p A n by
    unfold gradeSeriesNormEnvelope; positivity)] using hn

theorem gradeSeries_witness_summable
    {d : ℕ} {p A : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) {u : ℕ → C(UnitAddTorus (Fin d), ℂ)}
    (hu : ∀ n, u n ∈ decodedJointLpFeatureImage (d := d) (n := n) p
      (gradeSeriesSourceRadius d p A n)) : Summable u := by
  apply Summable.of_norm_bounded (gradeSeriesNormEnvelope_summable hd hp hp2 hA)
  intro n
  exact gradeSeriesComponent_norm_le hd hp hp2 hA (hu n)

theorem gradeSeries_norm_tsum_nat_add_le
    {d : ℕ} {p A : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) {u : ℕ → C(UnitAddTorus (Fin d), ℂ)}
    (hu : ∀ n, u n ∈ decodedJointLpFeatureImage (d := d) (n := n) p
      (gradeSeriesSourceRadius d p A n)) (M : ℕ) :
    ‖∑' n : ℕ, u (n + M)‖ ≤ ∑' n : ℕ, gradeSeriesNormEnvelope d p A (n + M) := by
  let hs := gradeSeries_witness_summable hd hp hp2 hA hu
  have hshift : Summable (fun n : ℕ => u (n + M)) := hs.comp_injective (fun a b hab => by
    exact Nat.add_right_cancel hab)
  have henv := gradeSeriesNormEnvelope_summable hd hp hp2 hA
  have henvshift : Summable (fun n : ℕ => gradeSeriesNormEnvelope d p A (n + M)) :=
    henv.comp_injective (fun a b hab => Nat.add_right_cancel hab)
  have hshiftNorm : Summable (fun n : ℕ => ‖u (n + M)‖) :=
    Summable.of_norm_bounded henvshift (fun n =>
      by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        gradeSeriesComponent_norm_le hd hp hp2 hA (hu (n + M)))
  calc
    ‖∑' n : ℕ, u (n + M)‖ ≤ ∑' n : ℕ, ‖u (n + M)‖ := norm_tsum_le_tsum_norm hshiftNorm
    _ ≤ ∑' n : ℕ, gradeSeriesNormEnvelope d p A (n + M) := by
      exact Summable.tsum_le_tsum
        (fun n => gradeSeriesComponent_norm_le hd hp hp2 hA (hu (n + M))) hshiftNorm henvshift

end BrownianSharp.AlignmentPaperJointGlobalSeries
