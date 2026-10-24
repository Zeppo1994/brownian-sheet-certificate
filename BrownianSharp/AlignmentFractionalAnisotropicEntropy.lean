import BrownianSharp.AlignmentExponentialFractionalEntropy
import BrownianSharp.AlignmentFractionalEntropyTransfer
import Mathlib.Tactic

noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentFractionalAnisotropicEntropy

open BrownianSharp.AlignmentFractionalPadding
open BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentExponentialFractionalEntropy
open BrownianSharp.AlignmentFractionalEntropyTransfer
open HaarQuarter

/-- Coordinate permutation of continuous-function outputs is contractive. -/
theorem reindexOutput_norm_le {d : ℕ} (e : Fin d ≃ Fin d)
    (F : C(BrownianCubeAnchor d, ℝ)) : ‖reindexOutput e F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le (f := reindexOutput e F) (C := ‖F‖) (norm_nonneg _)).2
  intro t
  rw [reindexOutput_apply]
  exact ContinuousMap.norm_coe_le_norm F (reindexAnchor e t)

theorem reindexOutput_opNorm_le {d : ℕ} (e : Fin d ≃ Fin d) :
    ‖reindexOutput e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro F
  calc
    ‖reindexOutput e F‖ ≤ ‖F‖ := reindexOutput_norm_le e F
    _ ≤ 1 * ‖F‖ := by simp

theorem paddedRestriction_opNorm_le {ν e : ℕ} :
    ‖paddedRestriction (ν := ν) (e := e)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro F
  calc
    ‖paddedRestriction F‖ ≤ ‖F‖ := paddedRestriction_norm_le F
    _ ≤ 1 * ‖F‖ := by simp

/-- Full anisotropic entropy lower bound from its minimum-order block, with
all coordinate locations handled by an actual RL coordinate permutation. -/
theorem fractional_entropy_lower_of_minimum_multiplicity
    {ν e : ℕ} (hν : 2 ≤ ν) (a : Fin (ν+e) → ℝ)
    (ha : ∀ i, 1/2 < a i) (r : ℝ) (hr : 1/2 < r)
    (hm : Latest.minimumMultiplicity a r ν) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((ν-1:ℕ):ℝ)+1/2)) ≤
        HaarQuarter.TheoremD.entropyNumber k (Latest.fractionalIntegrationBall a) := by
  let b : Fin e → ℝ := fun j =>
    reindexOrders (minimumCoordinatePermutation a r hm.2) a (Fin.natAdd ν j)
  have hb : ∀ j, 1/2 < b j := by
    intro j
    exact ha (minimumCoordinatePermutation a r hm.2 (Fin.natAdd ν j))
  have horders := reindexOrders_eq_paddedOrders a r hm.2
  have hordergt := paddedOrders_gt (ν := ν) (e := e) hr hb
  let eperm := minimumCoordinatePermutation a r hm.2
  have horders' : reindexOrders eperm a = paddedOrders r b := by
    simpa [eperm, b] using horders
  have hpermBall := fractionalIntegrationBall_reindex eperm a ha
  have hReindexNorm : ‖reindexOutput eperm‖ ≤ 1 := reindexOutput_opNorm_le eperm
  have hpadInclusion := scaled_active_ball_subset_restricted_full_ball
    (ν := ν) (e := e) r hr b hb
  have hfactor : 0 < inactivePaddingFactor b := inactivePaddingFactor_pos b hb
  obtain ⟨c₀, hc₀, k₀, hk₀, hIso⟩ :=
    isotropic_fractional_entropy_lower (d := ν) hν hr
  refine ⟨inactivePaddingFactor b * c₀, mul_pos hfactor hc₀, k₀, hk₀, ?_⟩
  intro k hk
  let rate : ℝ := (k:ℝ)^(-r) * (Real.log (k:ℝ))^
    (r*((ν-1:ℕ):ℝ)+1/2)
  have hIsoK : ENNReal.ofReal (c₀ * rate) ≤ HaarQuarter.TheoremD.entropyNumber k
      (Latest.fractionalIntegrationBall (fun _ : Fin ν => r)) := by
    simpa [rate, mul_assoc] using hIso k hk
  have hpad : ENNReal.ofReal (inactivePaddingFactor b * (c₀ * rate)) ≤
      HaarQuarter.TheoremD.entropyNumber k
        (Latest.fractionalIntegrationBall (paddedOrders (ν := ν) (e := e) r b)) := by
    exact entropyNumber_ge_of_scaled_contractive_image
      (paddedRestriction (ν := ν) (e := e))
      (paddedRestriction_opNorm_le (ν := ν) (e := e))
      (Latest.fractionalIntegrationBall (paddedOrders (ν := ν) (e := e) r b))
      (Latest.fractionalIntegrationBall (fun _ : Fin ν => r))
      (inactivePaddingFactor b) (c₀*rate) hfactor
      (by positivity)
      hpadInclusion k hIsoK
  have hpermSub : (fun f : C(BrownianCubeAnchor (ν+e),ℝ) => (1:ℝ) • f) ''
      Latest.fractionalIntegrationBall (reindexOrders eperm a) ⊆
      reindexOutput eperm '' Latest.fractionalIntegrationBall a := by
    intro f hf
    rcases (Set.mem_image _ _ _).mp hf with ⟨f₀, hf₀, heq⟩
    have heq' : f₀ = f := by simpa using heq
    subst f
    rw [hpermBall] at hf₀
    simpa using hf₀
  have hfull : ENNReal.ofReal (inactivePaddingFactor b * (c₀ * rate)) ≤
      HaarQuarter.TheoremD.entropyNumber k (Latest.fractionalIntegrationBall a) := by
    have hpad' : ENNReal.ofReal (inactivePaddingFactor b * (c₀ * rate)) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (Latest.fractionalIntegrationBall (reindexOrders eperm a)) := by
      simpa [horders'] using hpad
    have hfull' := entropyNumber_ge_of_scaled_contractive_image
      (reindexOutput eperm) hReindexNorm
      (Latest.fractionalIntegrationBall a)
      (Latest.fractionalIntegrationBall (reindexOrders eperm a))
      1 (inactivePaddingFactor b * (c₀*rate)) (by norm_num)
      (by positivity) hpermSub k hpad'
    simpa using hfull'
  simpa [rate, mul_assoc] using hfull


/-- The same lower bound stated without assuming in advance that the ambient
dimension is written as an active-plus-inactive sum. -/
theorem fractional_entropy_lower_general
    {d ν : ℕ} (hd : 2 ≤ d) (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hr : 1/2 < r) (hν : 2 ≤ ν)
    (hm : Latest.minimumMultiplicity a r ν) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((ν-1:ℕ):ℝ)+1/2)) ≤
        HaarQuarter.TheoremD.entropyNumber k (Latest.fractionalIntegrationBall a) := by
  change (∀ i, r ≤ a i) ∧
    (Finset.univ.filter (fun i => a i = r)).card = ν at hm
  have hνd : ν ≤ d := by
    calc
      ν = (Finset.univ.filter (fun i : Fin d => a i = r)).card := hm.2.symm
      _ ≤ Finset.univ.card := Finset.card_le_univ _
      _ = d := by simp
  obtain ⟨e, hde⟩ := Nat.exists_eq_add_of_le hνd
  subst d
  exact fractional_entropy_lower_of_minimum_multiplicity hν a ha r hr hm

end BrownianSharp.AlignmentFractionalAnisotropicEntropy
