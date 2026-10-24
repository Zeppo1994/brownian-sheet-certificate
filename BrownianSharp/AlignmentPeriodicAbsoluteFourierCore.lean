import BrownianSharp.AlignmentPeriodicSpectralEnergy
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 20000000
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPeriodicAbsoluteFourier
open BrownianSharp.Torus
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.AlignmentPeriodicSpectralEnergy
open BrownianSharp.SmoothResolution
open UnitAddTorus

private theorem summable_inv_one_dim (r : ℝ) (hr : 1/2 < r) :
    Summable (fun z : ℤ => (1 + (z : ℝ)^2)^(-r)) := by
  have hpow : 1 < 2*r := by linarith
  have hs := Real.summable_abs_int_rpow hpow
  have hdelta : Summable (fun z : ℤ => if z = 0 then (1:ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    change ({z : ℤ | (if z = 0 then (1:ℝ) else 0) ≠ 0}).Finite
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    split_ifs at hz with h
    · subst z; simp
    · simp at hz
  have hmajor : Summable (fun z : ℤ => |(z:ℝ)|^(-2*r) + (if z = 0 then (1:ℝ) else 0)) := by
    simpa only [show -(2*r) = -2*r by ring] using hs.add hdelta
  apply Summable.of_norm_bounded hmajor
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1+(z:ℝ)^2)^(-r))]
  by_cases hz : z = 0
  · simp [hz]
    positivity
  · have hzpos : 0 < |(z:ℝ)| := abs_pos.mpr (by exact_mod_cast hz)
    have hbase : (z:ℝ)^2 ≤ 1 + (z:ℝ)^2 := by linarith
    have hpowle := Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero (by exact_mod_cast hz))
      hbase (by linarith : -r ≤ 0)
    have habs : (z:ℝ)^2 = |(z:ℝ)|^2 := by rw [sq_abs]
    have hform : ((z:ℝ)^2)^(-r) = |(z:ℝ)|^(-2*r) := by
      rw [habs]
      calc
        (|(z:ℝ)|^2)^(-r) = (|(z:ℝ)|^(2:ℝ))^(-r) :=
          congrArg (fun y : ℝ => y ^ (-r)) (Real.rpow_natCast _ 2).symm
        _ = |(z:ℝ)|^(2*(-r)) :=
          (Real.rpow_mul (abs_nonneg (z:ℝ)) 2 (-r)).symm
        _ = |(z:ℝ)|^(-2*r) := by congr 1 <;> ring
    rw [if_neg hz, add_zero, ← hform]
    exact hpowle

private theorem summable_inverse_weight (d : ℕ) (r : ℝ) (hr : 1/2 < r) :
    Summable (fun k : Fin d → ℤ => (spectralWeight r k)⁻¹) := by
  induction d with
  | zero =>
      classical
      apply summable_of_hasFiniteSupport
      change ({k : Fin 0 → ℤ | (spectralWeight r k)⁻¹ ≠ 0}).Finite
      exact Set.toFinite _
  | succ d ih =>
      let e : ℤ × (Fin d → ℤ) ≃ (Fin (d+1) → ℤ) :=
        Fin.consEquiv (fun _ : Fin (d+1) => ℤ)
      have hprod : Summable (fun p : ℤ × (Fin d → ℤ) =>
          (1 + (p.1:ℝ)^2)^(-r) * (spectralWeight r p.2)⁻¹) := by
        apply (summable_inv_one_dim r hr).mul_of_nonneg ih
        · intro z; positivity
        · intro k
          unfold spectralWeight
          positivity
      have hprod' : Summable
          ((fun k : Fin (d+1) → ℤ => (spectralWeight r k)⁻¹) ∘ e) := by
        refine hprod.congr ?_
        intro p
        change (1+(p.1:ℝ)^2)^(-r) * (∏ i : Fin d, (1+(p.2 i:ℝ)^2)^r)⁻¹ =
          (∏ i : Fin (d+1), (1+(((e p) i:ℝ)^2))^r)⁻¹
        rw [Fin.prod_univ_succ]
        simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        rw [Real.rpow_neg (by positivity) r, mul_inv_rev]
        ring
      have htrans := e.summable_iff.mp hprod'
      refine htrans.congr ?_
      intro k
      rfl

theorem realPeriodicFourierCoeff_summable {d : ℕ} (r : ℝ) (hr : 1/2 < r)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    Summable (fun k : Fin d → ℤ => ‖realPeriodicFourierCoeff f k‖) := by
  have henergy := sobolev_two_spectral_energy_le r (by linarith) f hf |>.1
  have hinv := summable_inverse_weight d r hr
  let F : (Fin d → ℤ) → ℝ := fun k => spectralWeight r k * ‖realPeriodicFourierCoeff f k‖^2
  let G : (Fin d → ℤ) → ℝ := fun k => (spectralWeight r k)⁻¹
  have hF : Summable F := by simpa [F] using henergy
  have hG : Summable G := by simpa [G] using hinv
  have hr0 : 0 ≤ r := by linarith
  have hWpos : ∀ k : Fin d → ℤ, 0 < spectralWeight r k := by
    intro k
    unfold spectralWeight
    apply Finset.prod_pos
    intro i hi
    exact Real.rpow_pos_of_pos (by positivity) r
  have hFnonneg : ∀ k, 0 ≤ F k := by
    intro k
    unfold F
    exact mul_nonneg (le_of_lt (hWpos k)) (sq_nonneg _)
  have hGnonneg : ∀ k, 0 ≤ G k := by
    intro k
    unfold G
    exact le_of_lt (inv_pos.mpr (hWpos k))
  have hbound : ∀ s : Finset (Fin d → ℤ),
      ∑ k ∈ s, ‖realPeriodicFourierCoeff f k‖ ≤
        Real.sqrt ((∑' k, F k) * (∑' k, G k)) := by
    intro s
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
        (fun k => Real.sqrt (F k)) (fun k => Real.sqrt (G k))
    have hsumF : ∑ k ∈ s, F k ≤ ∑' k, F k := hF.sum_le_tsum s (fun k hk =>
      hFnonneg k)
    have hsumG : ∑ k ∈ s, G k ≤ ∑' k, G k := hG.sum_le_tsum s (fun k hk =>
      hGnonneg k)
    have hFtsum : 0 ≤ ∑' k, F k := tsum_nonneg hFnonneg
    have hGtsum : 0 ≤ ∑' k, G k := tsum_nonneg hGnonneg
    have hprod : ∀ k, Real.sqrt (F k) * Real.sqrt (G k) =
        ‖realPeriodicFourierCoeff f k‖ := by
      intro k
      have hw := hWpos k
      change Real.sqrt (spectralWeight r k * ‖realPeriodicFourierCoeff f k‖^2) *
        Real.sqrt ((spectralWeight r k)⁻¹) = _
      rw [Real.sqrt_mul (le_of_lt hw), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg _), Real.sqrt_inv]
      field_simp
    have hcs' : (∑ k ∈ s, ‖realPeriodicFourierCoeff f k‖)^2 ≤
        (∑' k, F k) * (∑' k, G k) := by
      calc
        _ = (∑ k ∈ s, Real.sqrt (F k) * Real.sqrt (G k))^2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [hprod]
        _ ≤ (∑ k ∈ s, (Real.sqrt (F k))^2) *
              (∑ k ∈ s, (Real.sqrt (G k))^2) := hcs
        _ ≤ _ := by
          have hsF : ∑ k ∈ s, (Real.sqrt (F k))^2 = ∑ k ∈ s, F k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact Real.sq_sqrt (hFnonneg k)
          have hsG : ∑ k ∈ s, (Real.sqrt (G k))^2 = ∑ k ∈ s, G k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact Real.sq_sqrt (hGnonneg k)
          rw [hsF, hsG]
          exact mul_le_mul hsumF hsumG (Finset.sum_nonneg fun _ _ => hGnonneg _) hFtsum
    have hsum_nonneg : 0 ≤ ∑ k ∈ s, ‖realPeriodicFourierCoeff f k‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hroot' := Real.sqrt_le_sqrt hcs'
    calc
      ∑ k ∈ s, ‖realPeriodicFourierCoeff f k‖ =
          Real.sqrt ((∑ k ∈ s, ‖realPeriodicFourierCoeff f k‖)^2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg]
      _ ≤ Real.sqrt ((∑' k, F k) * (∑' k, G k)) := hroot'
  exact summable_of_sum_le (fun k => norm_nonneg _) hbound


end BrownianSharp.AlignmentPeriodicAbsoluteFourier
