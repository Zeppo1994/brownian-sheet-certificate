import BrownianSharp.AlignmentFractionalPaddingPermutation
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic

noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentFractionalEntropyTransfer

open Metric

/-- A Lipschitz image cannot have a larger external covering number, with the
radius multiplied by the Lipschitz constant. -/
theorem externalCoveringNumber_image_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (L : ℝ≥0) (hL : LipschitzWith L f)
    (K : Set X) (ρ : ℝ≥0) :
    externalCoveringNumber (L * ρ) (f '' K) ≤ externalCoveringNumber ρ K := by
  unfold externalCoveringNumber
  refine le_iInf fun C => le_iInf fun hC => ?_
  refine iInf_le_of_le (f '' C) (iInf_le_of_le (hC.image_lipschitz hL) ?_)
  exact Set.encard_image_le f C

/-- A contractive linear image inclusion transfers covers back to the source
set, after undoing a positive scalar. -/
theorem externalCoveringNumber_le_of_scaled_contractive_image
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hT : ‖T‖ ≤ 1)
    (K : Set X) (J : Set Y) (c : ℝ) (hc : 0 < c)
    (hsub : (fun y : Y => c • y) '' J ⊆ T '' K) (ρ : ℝ≥0) :
    externalCoveringNumber (Real.toNNReal c⁻¹ * ρ) J ≤
      externalCoveringNumber ρ K := by
  let κ : ℝ≥0 := Real.toNNReal c⁻¹
  let S : X → Y := fun x => c⁻¹ • T x
  have hκ : (κ : ℝ) = c⁻¹ := Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hc))
  have hS : LipschitzWith κ S := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (c⁻¹ • T x) (c⁻¹ • T y) ≤ (κ : ℝ) * dist x y
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, ← map_sub]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), hκ]
    calc
      c⁻¹ * ‖T (x-y)‖ ≤ c⁻¹ * (‖T‖ * ‖x-y‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm (x-y)) (le_of_lt (inv_pos.mpr hc))
      _ ≤ c⁻¹ * ‖x-y‖ := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_left (norm_nonneg _) hT)
          (le_of_lt (inv_pos.mpr hc))
  have hJ : J ⊆ S '' K := by
    intro y hy
    have hy' : c • y ∈ T '' K := hsub (Set.mem_image_of_mem _ hy)
    rcases hy' with ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    dsimp [S]
    rw [hxy]
    simp [hc.ne']
  calc
    externalCoveringNumber (κ * ρ) J ≤ externalCoveringNumber (κ * ρ) (S '' K) :=
      externalCoveringNumber_mono_set hJ
    _ ≤ externalCoveringNumber ρ K := externalCoveringNumber_image_lipschitz S κ hS K ρ

/-- Entropy lower bounds pass through a contractive restriction whenever a
positive scalar multiple of the source class embeds into its image. -/
theorem entropyNumber_ge_of_scaled_contractive_image
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hT : ‖T‖ ≤ 1)
    (K : Set X) (J : Set Y) (c E : ℝ) (hc : 0 < c) (hE : 0 ≤ E)
    (hsub : (fun y : Y => c • y) '' J ⊆ T '' K)
    (k : ℕ) (hJ : ENNReal.ofReal E ≤ HaarQuarter.TheoremD.entropyNumber k J) :
    ENNReal.ofReal (c * E) ≤ HaarQuarter.TheoremD.entropyNumber k K := by
  unfold HaarQuarter.TheoremD.entropyNumber
  apply le_sInf
  rintro q ⟨ρ, rfl, hcover⟩
  let κ : ℝ≥0 := Real.toNNReal c⁻¹
  have hcκ : (κ : ℝ) = c⁻¹ := Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hc))
  have hJcover : Metric.externalCoveringNumber (κ * ρ) J ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞) :=
    (externalCoveringNumber_le_of_scaled_contractive_image T hT K J c hc hsub ρ).trans hcover
  have hInf : HaarQuarter.TheoremD.entropyNumber k J ≤ ENNReal.ofNNReal (κ * ρ) := by
    unfold HaarQuarter.TheoremD.entropyNumber
    apply sInf_le
    exact ⟨κ * ρ, rfl, hJcover⟩
  have hreal : E ≤ (κ * ρ : ℝ) := by
    have hle := hJ.trans hInf
    rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top] at hle
    simpa using hle
  have hcρ : c * E ≤ (ρ : ℝ) := by
    calc
      c * E ≤ c * (κ * ρ) := mul_le_mul_of_nonneg_left hreal hc.le
      _ = (c * c⁻¹) * (ρ : ℝ) := by rw [hcκ]; ring
      _ = (ρ : ℝ) := by rw [mul_inv_cancel₀ hc.ne']; simp
  exact (ENNReal.ofReal_le_coe).2 hcρ

end BrownianSharp.AlignmentFractionalEntropyTransfer
