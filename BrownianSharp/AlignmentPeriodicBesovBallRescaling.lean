import BrownianSharp.AlignmentPeriodicCutoffScaling
import BrownianSharp.AlignmentCountableFiniteOverlapRpow

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPeriodicBesovBallRescaling
open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffScaling

private theorem ofReal_inverse_power_mul_power (C q : ℝ) (hC : 0 < C) :
    ENNReal.ofReal ((C⁻¹) ^ q) * ENNReal.ofReal (C ^ q) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← Real.mul_rpow (inv_nonneg.mpr hC.le) hC.le]
  simp [inv_mul_cancel₀ (ne_of_gt hC)]

/-- Besov energy and supremum-endpoint rescaling: the source unit ball supplies a
uniform bound on the target blocks, rather than requiring a pointwise
same-index comparison of the two cutoff norms. -/
theorem besovUnitBall_rescale_of_energy_and_sup_bound {d : ℕ}
    (φ ψ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ) (theta : ℝ≥0∞)
    (C : ℝ) (hC : 0 < C)
    (henergy : theta ≠ ⊤ → ∀ f : RealPeriodic d,
      (∑' s : Fin d → ℕ, weightedBlockNorm φ p r s f ^ theta.toReal) ≤
        ENNReal.ofReal (C ^ theta.toReal) *
          (∑' s : Fin d → ℕ, weightedBlockNorm ψ p r s f ^ theta.toReal))
    (hsup : ∀ f : RealPeriodic d, BesovUnitBall ψ p r ⊤ f →
      ∀ s : Fin d → ℕ, weightedBlockNorm φ p r s f ≤ ENNReal.ofReal C) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : RealPeriodic d,
      BesovUnitBall ψ p r theta f → BesovUnitBall φ p r theta (c • f) := by
  classical
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro f hf
  by_cases htop : theta = ⊤
  · simp only [BesovUnitBall, htop, ↓reduceIte] at hf ⊢
    intro s
    rw [AlignmentPeriodicCutoffScaling.weightedBlockNorm_smul φ (inv_pos.mpr hC)]
    have htarget := hsup f hf s
    have hcancellation : ENNReal.ofReal (C⁻¹) * ENNReal.ofReal C = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hC.le)]
      simp [inv_mul_cancel₀ (ne_of_gt hC)]
    calc
      ENNReal.ofReal (C⁻¹) * weightedBlockNorm φ p r s f ≤
          ENNReal.ofReal (C⁻¹) * ENNReal.ofReal C :=
        mul_le_mul_of_nonneg_left htarget (by positivity)
      _ = 1 := hcancellation
  · simp only [BesovUnitBall, htop, ↓reduceIte] at hf ⊢
    rw [AlignmentPeriodicCutoffScaling.BesovEnergy_smul φ (inv_pos.mpr hC) p r theta f]
    have hψ : (∑' s : Fin d → ℕ,
        weightedBlockNorm ψ p r s f ^ theta.toReal) ≤ 1 := hf
    have hcancel := ofReal_inverse_power_mul_power C theta.toReal hC
    calc
      ENNReal.ofReal ((C⁻¹) ^ theta.toReal) *
          (∑' s : Fin d → ℕ, weightedBlockNorm φ p r s f ^ theta.toReal) ≤
        ENNReal.ofReal ((C⁻¹) ^ theta.toReal) *
          (ENNReal.ofReal (C ^ theta.toReal) *
            (∑' s : Fin d → ℕ, weightedBlockNorm ψ p r s f ^ theta.toReal)) :=
        mul_le_mul_of_nonneg_left (henergy htop f) (by positivity)
      _ = ∑' s : Fin d → ℕ, weightedBlockNorm ψ p r s f ^ theta.toReal := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ 1 := hψ

/-- A finite-overlap neighbor estimate yields the cutoff Besov ball
inclusion for every summability exponent, including the supremum endpoint. -/
theorem besovUnitBall_transfer_of_neighbor_comparison {d : ℕ}
    (φ ψ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ) (theta : ℝ≥0∞)
    (R : (Fin d → ℕ) → (Fin d → ℕ) → Prop) [DecidableRel R]
    (row : (Fin d → ℕ) → Finset (Fin d → ℕ))
    (col : (Fin d → ℕ) → Finset (Fin d → ℕ))
    (hrowSpec : ∀ s t, t ∈ row s ↔ R s t)
    (hcolSpec : ∀ s t, s ∈ col t ↔ R s t)
    (A : ℝ) (hA : 0 < A) (N : ℕ) (hN : 0 < N)
    (htheta : theta ≠ ⊤ → 1 ≤ theta.toReal)
    (hrow : ∀ s, (row s).card ≤ N) (hcol : ∀ t, (col t).card ≤ N)
    (hneighbor : ∀ f : RealPeriodic d, ∀ s,
      weightedBlockNorm φ p r s f ≤ ENNReal.ofReal A *
        ∑' t, if R s t then weightedBlockNorm ψ p r t f else 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : RealPeriodic d,
      BesovUnitBall ψ p r theta f → BesovUnitBall φ p r theta (c • f) := by
  classical
  let C : ℝ := A * (N : ℝ)
  have hC : 0 < C := by simp [C]; positivity
  let Ade : ℝ≥0∞ := ENNReal.ofReal A
  have hAcast : Ade * (N : ℝ≥0∞) = ENNReal.ofReal C := by
    change ENNReal.ofReal A * (N : ℝ≥0∞) = ENNReal.ofReal C
    rw [show (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by simp]
    rw [← ENNReal.ofReal_mul hA.le]
  have henergy : theta ≠ ⊤ → ∀ f : RealPeriodic d,
      (∑' s : Fin d → ℕ, weightedBlockNorm φ p r s f ^ theta.toReal) ≤
        ENNReal.ofReal (C ^ theta.toReal) *
          (∑' s : Fin d → ℕ, weightedBlockNorm ψ p r s f ^ theta.toReal) := by
    intro htop f
    have h := BrownianSharp.AlignmentCountableFiniteOverlapRpow.countable_overlap_rpow_tsum_le
      R row col hrowSpec hcolSpec Ade N hN theta.toReal
      (htheta htop) hrow hcol
      (fun s => weightedBlockNorm φ p r s f)
      (fun t => weightedBlockNorm ψ p r t f) (hneighbor f)
    rw [hAcast, ENNReal.ofReal_rpow_of_pos hC] at h
    exact h
  have hsup : ∀ f : RealPeriodic d, BesovUnitBall ψ p r ⊤ f →
      ∀ s, weightedBlockNorm φ p r s f ≤ ENNReal.ofReal C := by
    intro f hf s
    have hψ : ∀ t, weightedBlockNorm ψ p r t f ≤ 1 := by
      simpa [BesovUnitBall] using hf
    have hrowsum : (∑' t, if R s t then weightedBlockNorm ψ p r t f else 0) ≤ N := by
      rw [tsum_eq_sum (f := fun t => if R s t then weightedBlockNorm ψ p r t f else 0)
        (L := SummationFilter.unconditional (Fin d → ℕ)) (s := row s) ?_]
      · calc
          (∑ t ∈ row s, if R s t then weightedBlockNorm ψ p r t f else 0) ≤
              ∑ t ∈ row s, (1 : ℝ≥0∞) := by
                apply Finset.sum_le_sum
                intro t ht
                by_cases hst : R s t
                · simp [hst, hψ t]
                · simp [hst]
          _ = (row s).card := by simp
          _ ≤ N := by exact_mod_cast hrow s
      · intro t ht
        exact if_neg (fun hst => ht ((hrowSpec s t).2 hst))
    have hbound : weightedBlockNorm φ p r s f ≤ Ade * (N : ℝ≥0∞) :=
      (hneighbor f s).trans (mul_le_mul_of_nonneg_left hrowsum (by positivity))
    rw [hAcast] at hbound
    exact hbound
  exact besovUnitBall_rescale_of_energy_and_sup_bound φ ψ p r theta C hC
    henergy hsup

end BrownianSharp.AlignmentPeriodicBesovBallRescaling

end
