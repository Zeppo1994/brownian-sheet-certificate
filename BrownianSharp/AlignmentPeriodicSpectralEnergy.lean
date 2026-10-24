import BrownianSharp.AlignmentPeriodicRealEnergy
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.ScalarHighFrequency
import Mathlib.Tactic

/-! The literal p=2 smooth square-function ball controls its actual weighted
Fourier coefficients. This is the spectral energy used by the Matérn source
embedding; the cutoff remains the manuscript certificate's concrete cutoff. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPeriodicSpectralEnergy
open Torus SmoothResolution

theorem scalarBlock_nonzero_indices_near {s t : ℕ} {ξ : ℝ}
    (hs : scalarBlock s ξ ≠ 0) (ht : scalarBlock t ξ ≠ 0) :
    t ≤ s+1 := by
  by_contra h
  have hts : s+2 ≤ t := by omega
  have hu : |ξ| < (2:ℝ)^(s+1) := by
    by_contra hnot
    exact hs (ScalarKernelL1.scalarBlock_eq_zero_of_two_pow_le_abs s (le_of_not_gt hnot))
  have hl : (2:ℝ)^(t-1) < |ξ| := by
    by_contra hnot
    exact ht (ScalarHighFrequency.scalarBlock_eq_zero_of_abs_le_lower t (by omega)
      (le_of_not_gt hnot))
  have hp : (2:ℝ)^(s+1) ≤ (2:ℝ)^(t-1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

theorem scalarBlock_active_card_le_two (N : ℕ) (ξ : ℝ) :
    ((Finset.range (N+1)).filter (fun s => scalarBlock s ξ ≠ 0)).card ≤ 2 := by
  classical
  let S := (Finset.range (N+1)).filter (fun s => scalarBlock s ξ ≠ 0)
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := Finset.min'_mem S hS
    have hsub : S ⊆ {m,m+1} := by
      intro s hs
      have hlo : m ≤ s := Finset.min'_le S s hs
      have hhi : s ≤ m+1 := scalarBlock_nonzero_indices_near
        (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hs).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simpa [S] using (show S.card ≤ 2 by rw [he]; simp)

theorem scalarBlock_frequency_weight_le (r ξ : ℝ) (hr : 0 ≤ r) (s : ℕ)
    (hs : scalarBlock s ξ ≠ 0) :
    (1+ξ^2)^r ≤ (5:ℝ)^r * (2:ℝ)^(2*r*(s:ℝ)) := by
  have hu : |ξ| < (2:ℝ)^(s+1) := by
    by_contra hnot
    exact hs (ScalarKernelL1.scalarBlock_eq_zero_of_two_pow_le_abs s (le_of_not_gt hnot))
  have hpow : 1 ≤ (2:ℝ)^s := one_le_pow₀ (by norm_num)
  have hsq : ξ^2 ≤ 4*((2:ℝ)^s)^2 := by
    rw [pow_succ] at hu
    nlinarith [sq_abs ξ, abs_nonneg ξ]
  have hbase : 1+ξ^2 ≤ 5*((2:ℝ)^s)^2 := by nlinarith
  calc
    (1+ξ^2)^r ≤ (5*((2:ℝ)^s)^2)^r :=
      Real.rpow_le_rpow (by positivity) hbase hr
    _ = (5:ℝ)^r * (2:ℝ)^(2*r*(s:ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 2
      ring


theorem scalar_spectral_weight_le_energy (r ξ : ℝ) (hr : 0 ≤ r) (N : ℕ)
    (hpart : ∑ s ∈ Finset.range (N+1), scalarBlock s ξ = 1) :
    (1+ξ^2)^r ≤ 2*(5:ℝ)^r *
      ∑ s ∈ Finset.range (N+1), (2:ℝ)^(2*r*(s:ℝ)) * (scalarBlock s ξ)^2 := by
  classical
  let S := (Finset.range (N+1)).filter (fun s => scalarBlock s ξ ≠ 0)
  have hsum : ∑ s ∈ S, scalarBlock s ξ = 1 := by
    simpa [S, Finset.sum_filter_ne_zero] using hpart
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ))
    (fun s => scalarBlock s ξ)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum] at hcs
  have hcard : (S.card:ℝ) ≤ 2 := by
    exact_mod_cast scalarBlock_active_card_le_two N ξ
  have h1 : 1 ≤ 2 * ∑ s ∈ S, (scalarBlock s ξ)^2 := by
    have h0 : 0 ≤ ∑ s ∈ S, (scalarBlock s ξ)^2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have hw : (1+ξ^2)^r * (∑ s ∈ S, (scalarBlock s ξ)^2) ≤
      (5:ℝ)^r * (∑ s ∈ S, (2:ℝ)^(2*r*(s:ℝ)) * (scalarBlock s ξ)^2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hp := scalarBlock_frequency_weight_le r ξ hr s (Finset.mem_filter.mp hs).2
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg (scalarBlock s ξ))]
  have hall : (∑ s ∈ S, (2:ℝ)^(2*r*(s:ℝ)) * (scalarBlock s ξ)^2) ≤
      ∑ s ∈ Finset.range (N+1), (2:ℝ)^(2*r*(s:ℝ)) * (scalarBlock s ξ)^2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have hweight : 0 ≤ (1+ξ^2)^r := Real.rpow_nonneg (by positivity) _
  have h5 : 0 ≤ (5:ℝ)^r := by positivity
  nlinarith

def spectralWeight {d : ℕ} (r : ℝ) (k : Fin d → ℤ) : ℝ :=
  ∏ i, (1+(k i:ℝ)^2)^r

theorem tensor_spectral_weight_le_energy {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (k : Fin d → ℤ) (N : ℕ)
    (hpart : ∀ i, ∑ s ∈ Finset.range (N+1), scalarBlock s (k i) = 1) :
    spectralWeight r k ≤ (2*(5:ℝ)^r)^d *
      ∑ s ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (N+1)),
        (2:ℝ)^(2*r*∑ i,(s i:ℝ)) * tensorMultiplier s k ^ 2 := by
  classical
  have hp := Finset.prod_le_prod₀
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1+(k i:ℝ)^2) r)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      scalar_spectral_weight_le_energy r (k i) hr N (hpart i))
  change spectralWeight r k ≤ _ at hp
  calc
    spectralWeight r k ≤ ∏ i, (2*(5:ℝ)^r *
      ∑ s ∈ Finset.range (N+1), (2:ℝ)^(2*r*(s:ℝ)) * (scalarBlock s (k i))^2) := hp
    _ = (2*(5:ℝ)^r)^d * ∏ i : Fin d,
        ∑ s ∈ Finset.range (N+1), (2:ℝ)^(2*r*(s:ℝ)) * (scalarBlock s (k i))^2 := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = _ := by
      rw [Finset.prod_univ_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2),
        tensorMultiplier, Finset.prod_pow]
      congr 1
      congr 1
      rw [← Finset.mul_sum]

theorem block_l2_energy_eq {d : ℕ} (r : ℝ) (f : RealPeriodic d) (s : Fin d → ℕ) :
    AlignmentPeriodicRealEnergy.realBlockEnergy r f s =
      ∑ k ∈ frequencyBox s, (2:ℝ)^(2*r*∑ i,(s i:ℝ)) *
        (tensorMultiplier s k)^2 * ‖realPeriodicFourierCoeff f k‖^2 := by
  unfold AlignmentPeriodicRealEnergy.realBlockEnergy
  have hn : ‖(block s f).toLp 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ‖^2 =
      ∑ k ∈ frequencyBox s, ‖(tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k‖^2 := by
    have hp := AlignmentTrigonometricL2.fourierPolynomial_L2_norm_sq (frequencyBox s)
      (fun k => (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k)
    change ‖(block s f).toLp 2 (Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ℂ‖^2 = _ at hp
    have he (μ : Measure (UnitAddTorus (Fin d))) [IsFiniteMeasure μ] :
        ‖(block s f).toLp 2 μ ℂ‖ = (eLpNorm (block s f) 2 μ).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ _)]
    rw [he] at hp
    rw [he]
    simpa only [unitAddTorus_volume_eq_productHaar] using hp
  rw [mul_pow, hn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have he : ((2:ℝ)^(r*∑ i,(s i:ℝ)))^2 =
      (2:ℝ)^(2*r*∑ i,(s i:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  rw [he]
  ring


theorem finite_frequency_block_energy_le {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (s : Fin d → ℕ) (K : Finset (Fin d → ℤ)) :
    (∑ k ∈ K, (2:ℝ)^(2*r*∑ i,(s i:ℝ)) * (tensorMultiplier s k)^2 *
      ‖realPeriodicFourierCoeff f k‖^2) ≤
      AlignmentPeriodicRealEnergy.realBlockEnergy r f s := by
  classical
  rw [block_l2_energy_eq]
  let F := fun k => (2:ℝ)^(2*r*∑ i,(s i:ℝ)) * (tensorMultiplier s k)^2 *
      ‖realPeriodicFourierCoeff f k‖^2
  change (∑ k ∈ K, F k) ≤ ∑ k ∈ frequencyBox s, F k
  have heq : ∑ k ∈ K, F k = ∑ k ∈ K ∩ frequencyBox s, F k := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro k hk hknot
    have hnot : k ∉ frequencyBox s := by simpa [hk] using hknot
    simp [F, AlignmentPeriodicFourierReconstruction.tensorMultiplier_eq_zero_outside_box s k hnot]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
    (fun _ _ _ => by dsimp [F]; positivity)

theorem sobolev_two_finite_spectral_energy_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f)
    (K : Finset (Fin d → ℤ)) :
    (∑ k ∈ K, spectralWeight r k * ‖realPeriodicFourierCoeff f k‖^2) ≤
      (2*(5:ℝ)^r)^d := by
  classical
  have hgood : ∀ᶠ N : ℕ in Filter.atTop, ∀ k : K, ∀ i : Fin d,
      ∑ s ∈ Finset.range (N+1), scalarBlock s (k.val i) = 1 :=
    Filter.eventually_all.mpr (fun k => Filter.eventually_all.mpr
      (fun i => scalarBlock_sum_eventually_one (k.val i)))
  obtain ⟨N,hN⟩ := hgood.exists
  let S := Fintype.piFinset (fun _ : Fin d => Finset.range (N+1))
  let D : ℝ := (2*(5:ℝ)^r)^d
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint : ∀ k ∈ K, spectralWeight r k ≤ D *
      ∑ s ∈ S, (2:ℝ)^(2*r*∑ i,(s i:ℝ)) * tensorMultiplier s k ^ 2 := by
    intro k hk
    exact tensor_spectral_weight_le_energy r hr k N (hN ⟨k,hk⟩)
  have hmain :
      (∑ k ∈ K, spectralWeight r k * ‖realPeriodicFourierCoeff f k‖^2) ≤
      D * ∑ s ∈ S, AlignmentPeriodicRealEnergy.realBlockEnergy r f s := by
    calc
      _ ≤ ∑ k ∈ K, (D * ∑ s ∈ S,
          (2:ℝ)^(2*r*∑ i,(s i:ℝ)) * tensorMultiplier s k ^ 2) *
          ‖realPeriodicFourierCoeff f k‖^2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (hpoint k hk) (sq_nonneg _)
      _ = D * ∑ s ∈ S, ∑ k ∈ K,
          (2:ℝ)^(2*r*∑ i,(s i:ℝ)) * tensorMultiplier s k ^ 2 *
          ‖realPeriodicFourierCoeff f k‖^2 := by
        simp_rw [mul_assoc, Finset.sum_mul]
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Finset.sum_le_sum
        intro s hs
        exact finite_frequency_block_energy_le r f s K
  have henergy := AlignmentPeriodicRealEnergy.sobolev_two_finite_real_energy_le_one r f hf S
  exact hmain.trans (by simpa [D] using mul_le_mul_of_nonneg_left henergy hD)

/-- No differentiability or spectral-energy premise is added to the literal
smooth square-function Sobolev ball. -/
theorem sobolev_two_spectral_energy_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    Summable (fun k : Fin d → ℤ => spectralWeight r k * ‖realPeriodicFourierCoeff f k‖^2) ∧
      (∑' k : Fin d → ℤ, spectralWeight r k * ‖realPeriodicFourierCoeff f k‖^2) ≤
        (2*(5:ℝ)^r)^d := by
  have hnonneg : ∀ k : Fin d → ℤ,
      0 ≤ spectralWeight r k * ‖realPeriodicFourierCoeff f k‖^2 := by
    intro k
    apply mul_nonneg _ (sq_nonneg _)
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
  have hfin := sobolev_two_finite_spectral_energy_le r hr f hf
  have hs := summable_of_sum_le hnonneg hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end BrownianSharp.AlignmentPeriodicSpectralEnergy
