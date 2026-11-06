import BrownianSharp.AlignmentPeriodicSpectralEnergy
import BrownianSharp.AlignmentPeriodicP2BesovIdentity
import BrownianSharp.AlignmentPeriodicCutoffClasses
import BrownianSharp.AlignmentPeriodicCutoffPartition

/-! Reverse control of the literal smooth dyadic Sobolev square function by
the weighted Fourier coefficient energy. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperPeriodicFourierReverse

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicSpectralEnergy
open BrownianSharp.AlignmentPeriodicCutoffPartition
open BrownianSharp.AlignmentPeriodicRealEnergy

private theorem scalarBlock_abs_le_one (s : ℕ) (ξ : ℝ) :
    |SmoothResolution.scalarBlock s ξ| ≤ 1 := by
  by_cases hs : s = 0
  · subst s
    simpa [SmoothResolution.scalarBlock, abs_of_nonneg (cutoff_bounds ξ).1] using (cutoff_bounds ξ).2
  · have h₁ := cutoff_bounds (ξ / (2 : ℝ) ^ s)
    have h₀ := cutoff_bounds (ξ / (2 : ℝ) ^ (s - 1))
    unfold SmoothResolution.scalarBlock
    rw [if_neg hs]
    exact abs_le.mpr ⟨by linarith [h₁.2, h₀.1], by linarith [h₁.1, h₀.2]⟩

private theorem scalarBlock_dyadic_weight_le (r ξ : ℝ) (hr : 0 ≤ r)
    (s : ℕ) (hs : SmoothResolution.scalarBlock s ξ ≠ 0) :
    (2 : ℝ) ^ (2 * r * (s : ℝ)) ≤
      (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r := by
  by_cases hs0 : s = 0
  · subst s
    have hbase : 1 ≤ 1 + ξ ^ 2 := by nlinarith [sq_nonneg ξ]
    have hpow : 1 ≤ (1 + ξ ^ 2) ^ r :=
      Real.one_le_rpow (by nlinarith [sq_nonneg ξ]) hr
    have hfour : 1 ≤ (4 : ℝ) ^ r := Real.one_le_rpow (by norm_num) hr
    calc
      (2 : ℝ) ^ (2 * r * ((0 : ℕ) : ℝ)) = 1 := by simp
      _ ≤ (1 + ξ ^ 2) ^ r := hpow
      _ ≤ (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hfour
            (Real.rpow_nonneg (show 0 ≤ 1 + ξ ^ 2 by nlinarith [sq_nonneg ξ]) r))
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
    have hlow : (2 : ℝ) ^ (s - 1) < |ξ| := by
      by_contra h
      have hle : |ξ| ≤ (2 : ℝ) ^ (s - 1) := le_of_not_gt h
      have hzero := BrownianSharp.AlignmentPeriodicCutoffPartition.scalarBlock_eq_zero_of_abs_le_lower
        smoothResolutionCutoff s hspos hle
      exact hs (by simpa only [BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock_smoothResolution_eq]
        using hzero)
    have hbase : (2 : ℝ) ^ s ≤ 2 * |ξ| := by
      have hp : (2 : ℝ) ^ s = 2 * (2 : ℝ) ^ (s - 1) := by
        have hn : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hs0)
        calc
          (2 : ℝ) ^ s = (2 : ℝ) ^ (s - 1 + 1) := by rw [hn]
          _ = (2 : ℝ) ^ (s - 1) * 2 := by rw [pow_succ]
          _ = 2 * (2 : ℝ) ^ (s - 1) := by ring
      rw [hp]
      nlinarith
    have hpow : ((2 : ℝ) ^ s) ^ (2 * r) = (2 : ℝ) ^ (2 * r * (s : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hpow' : (2 * |ξ|) ^ (2 * r) =
        (4 : ℝ) ^ r * (ξ ^ 2) ^ r := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg ξ)]
      have htwo : (2 : ℝ) ^ (2 * r) = (4 : ℝ) ^ r := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1 <;> ring
      have habs : |ξ| ^ (2 * r) = (ξ ^ 2) ^ r := by
        rw [show (ξ ^ 2) = |ξ| ^ (2 : ℕ) by rw [sq_abs]]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg ξ)]
        congr 1 <;> ring
      rw [htwo, habs]
    have hxi : (ξ ^ 2) ^ r ≤ (1 + ξ ^ 2) ^ r :=
      Real.rpow_le_rpow (sq_nonneg ξ) (by nlinarith) hr
    calc
      (2 : ℝ) ^ (2 * r * (s : ℝ)) = ((2 : ℝ) ^ s) ^ (2 * r) := hpow.symm
      _ ≤ (2 * |ξ|) ^ (2 * r) := Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = (4 : ℝ) ^ r * (ξ ^ 2) ^ r := hpow'
      _ ≤ (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r :=
        mul_le_mul_of_nonneg_left hxi (Real.rpow_nonneg (by norm_num) _)

private theorem scalar_dyadic_square_sum_le (r ξ : ℝ) (hr : 0 ≤ r)
    (S : Finset ℕ) :
    ∑ s ∈ S, (2 : ℝ) ^ (2 * r * (s : ℝ)) *
      (SmoothResolution.scalarBlock s ξ) ^ 2 ≤
        2 * (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r := by
  classical
  let F : ℕ → ℝ := fun s =>
    (2 : ℝ) ^ (2 * r * (s : ℝ)) * (SmoothResolution.scalarBlock s ξ) ^ 2
  let T := S.filter (fun s => SmoothResolution.scalarBlock s ξ ≠ 0)
  have hTcard : T.card ≤ 2 := by
    by_cases hT : T.Nonempty
    · let m := T.min' hT
      have hm : m ∈ T := Finset.min'_mem T hT
      have hsub : T ⊆ {m,m+1} := by
        intro s hs
        have hlo : m ≤ s := Finset.min'_le T s hs
        have hhi : s ≤ m+1 := scalarBlock_nonzero_indices_near
          (by simpa [T] using (Finset.mem_filter.mp hm).2)
          (by simpa [T] using (Finset.mem_filter.mp hs).2)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · simp [Finset.not_nonempty_iff_eq_empty.mp hT]
  have hsum : (∑ s ∈ S, F s) = ∑ s ∈ T, F s := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    have hz : SmoothResolution.scalarBlock s ξ = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hs, hn⟩)
    simp [F, hz]
  rw [hsum]
  calc
    ∑ s ∈ T, F s ≤ ∑ s ∈ T, (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r := by
      apply Finset.sum_le_sum
      intro s hs
      dsimp [F]
      have hw := scalarBlock_dyadic_weight_le r ξ hr s
        (Finset.mem_filter.mp hs).2
      have hb := scalarBlock_abs_le_one s ξ
      have hb2 : (SmoothResolution.scalarBlock s ξ) ^ 2 ≤ 1 := by
        have habs := abs_le.mp hb
        nlinarith
      calc
        _ ≤ (2 : ℝ) ^ (2 * r * (s : ℝ)) := by
          simpa using mul_le_mul_of_nonneg_left hb2
            (by positivity : 0 ≤ (2 : ℝ) ^ (2 * r * (s : ℝ)))
        _ ≤ _ := hw
    _ = (T.card : ℝ) * ((4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r) := by simp
    _ ≤ 2 * (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r := by
      have hA : 0 ≤ (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) r)
          (Real.rpow_nonneg (show 0 ≤ 1 + ξ ^ 2 by nlinarith [sq_nonneg ξ]) r)
      have hcard' : (T.card : ℝ) ≤ 2 := by exact_mod_cast hTcard
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcard' hA

/-- The scalar dyadic partition has a uniformly bounded weighted square
sum at each frequency. -/
theorem scalar_dyadic_square_tsum_le (r ξ : ℝ) (hr : 0 ≤ r) :
    (∑' s : ℕ, ENNReal.ofReal
      ((2 : ℝ) ^ (2 * r * (s : ℝ)) * (SmoothResolution.scalarBlock s ξ) ^ 2)) ≤
      ENNReal.ofReal (2 * (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r) := by
  classical
  let F : ℕ → ℝ := fun s =>
    (2 : ℝ) ^ (2 * r * (s : ℝ)) * (SmoothResolution.scalarBlock s ξ) ^ 2
  have hnonneg : ∀ s, 0 ≤ F s := by intro s; dsimp [F]; positivity
  have hfinite : ∀ S : Finset ℕ, ∑ s ∈ S, F s ≤
      2 * (4 : ℝ) ^ r * (1 + ξ ^ 2) ^ r := by
    intro S
    simpa [F] using scalar_dyadic_square_sum_le r ξ hr S
  have hs : Summable F := summable_of_sum_le hnonneg hfinite
  have hreal := hs.tsum_le_of_sum_le hfinite
  have htoENN : (∑' s, ENNReal.ofReal (F s)) = ENNReal.ofReal (∑' s, F s) :=
    (ENNReal.ofReal_tsum_of_nonneg hnonneg hs).symm
  rw [show (fun s : ℕ => ENNReal.ofReal
      ((2 : ℝ) ^ (2 * r * (s : ℝ)) * (SmoothResolution.scalarBlock s ξ) ^ 2)) =
      (fun s => ENNReal.ofReal (F s)) by rfl, htoENN]
  exact ENNReal.ofReal_le_ofReal hreal

private def tensorDyadicSquareTerm {d : ℕ} (r : ℝ)
    (s : Fin d → ℕ) (k : Fin d → ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
    (∏ i, SmoothResolution.scalarBlock (s i) (k i)) ^ 2)

private theorem tensorDyadicSquareTerm_eq_prod {d : ℕ} (r : ℝ)
    (s : Fin d → ℕ) (k : Fin d → ℤ) :
    tensorDyadicSquareTerm r s k =
      ∏ i : Fin d, ENNReal.ofReal
        ((2 : ℝ) ^ (2 * r * (s i : ℝ)) *
          (SmoothResolution.scalarBlock (s i) (k i)) ^ 2) := by
  unfold tensorDyadicSquareTerm
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
    congr 1
    · rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [Finset.mul_sum]
  · intro i hi
    positivity

/-- Tensor dyadic square kernels have uniformly bounded overlap on the
integer Fourier lattice. -/
theorem tensor_dyadic_square_tsum_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (k : Fin d → ℤ) :
    (∑' s : Fin d → ℕ, tensorDyadicSquareTerm r s k) ≤
      ENNReal.ofReal (((2 * (4 : ℝ) ^ r) ^ d) * spectralWeight r k) := by
  rw [show (∑' s : Fin d → ℕ, tensorDyadicSquareTerm r s k) =
      ∑' s : Fin d → ℕ, ∏ i : Fin d,
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * (s i : ℝ)) *
          (SmoothResolution.scalarBlock (s i) (k i)) ^ 2) by
        apply tsum_congr
        intro s
        exact tensorDyadicSquareTerm_eq_prod r s k]
  calc
    (∑' s : Fin d → ℕ, ∏ i : Fin d,
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * (s i : ℝ)) *
          (SmoothResolution.scalarBlock (s i) (k i)) ^ 2)) =
      ∏ i : Fin d, ∑' n : ℕ, ENNReal.ofReal
        ((2 : ℝ) ^ (2 * r * (n : ℝ)) *
          (SmoothResolution.scalarBlock n (k i)) ^ 2) := by
      exact BrownianSharp.LayerBlockSummability.tsum_pi_prod d
        (fun i n => ENNReal.ofReal ((2 : ℝ) ^ (2 * r * (n : ℝ)) *
          (SmoothResolution.scalarBlock n (k i)) ^ 2))
    _ ≤ ∏ i : Fin d, ENNReal.ofReal
          (2 * (4 : ℝ) ^ r * (1 + (k i : ℝ) ^ 2) ^ r) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact bot_le
      · intro i hi
        exact scalar_dyadic_square_tsum_le r (k i) hr
    _ = ENNReal.ofReal (((2 * (4 : ℝ) ^ r) ^ d) * spectralWeight r k) := by
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · congr 1
        simp [spectralWeight, Finset.prod_mul_distrib]
      · intro i hi
        positivity

private def coefficientSquareTerm {d : ℕ} (r : ℝ)
    (f : RealPeriodic d) (k : Fin d → ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖realPeriodicFourierCoeff f k‖ ^ 2)

private theorem weightedBlockNorm_sq_eq_fourier_tsum {d : ℕ} (r : ℝ)
    (f : RealPeriodic d) (s : Fin d → ℕ) :
    (AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f) ^ 2 =
      ∑' k : Fin d → ℤ,
        tensorDyadicSquareTerm r s k * coefficientSquareTerm r f k := by
  classical
  let μ := (volume : Measure (UnitAddTorus (Fin d)))
  let W := AlignmentPeriodicCutoffClasses.weightedBlockNorm
    smoothResolutionCutoff 2 r s f
  have hmem : MemLp (SmoothResolution.block s f) 2 μ :=
    (SmoothResolution.block s f).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmem' : MemLp (fun x =>
      (AlignmentPeriodicAdmissibleCutoff.admissibleBlock smoothResolutionCutoff s f) x) 2 μ := by
    simpa [AlignmentPeriodicCutoffClasses.admissibleBlock_fixed] using hmem
  have hWtop : W ≠ ⊤ := by
    dsimp [W, AlignmentPeriodicCutoffClasses.weightedBlockNorm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmem'.eLpNorm_ne_top
  have hparseval : realBlockEnergy r f s =
      ∑ k ∈ SmoothResolution.frequencyBox s,
        (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
          (SmoothResolution.tensorMultiplier s k) ^ 2 *
            ‖realPeriodicFourierCoeff f k‖ ^ 2 := by
    simpa [SmoothResolution.tensorMultiplier] using
      (AlignmentPeriodicSpectralEnergy.block_l2_energy_eq r f s)
  have hfiniteSum : W ^ 2 = ∑ k ∈ SmoothResolution.frequencyBox s,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
        (SmoothResolution.tensorMultiplier s k) ^ 2 *
          ‖realPeriodicFourierCoeff f k‖ ^ 2) := by
    have hW : W ^ 2 = ENNReal.ofReal (realBlockEnergy r f s) := by
      rw [AlignmentPeriodicRealEnergy.realBlockEnergy_eq_toReal]
      have hW2top : (SmoothResolution.weightedBlockNorm 2 r s f) ^ 2 ≠ ⊤ := by
        simpa [W, AlignmentPeriodicCutoffClasses.weightedBlockNorm_fixed, pow_two] using
          ENNReal.mul_ne_top hWtop hWtop
      simpa [W, AlignmentPeriodicCutoffClasses.weightedBlockNorm_fixed] using
        (ENNReal.ofReal_toReal hW2top).symm
    rw [hW, hparseval]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => by positivity)]
  have hsupport (k : Fin d → ℤ)
      (hk : k ∉ SmoothResolution.frequencyBox s) :
      tensorDyadicSquareTerm r s k = 0 := by
    have hz := AlignmentPeriodicFourierReconstruction.tensorMultiplier_eq_zero_outside_box s k hk
    change ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
      (SmoothResolution.tensorMultiplier s k) ^ 2) = 0
    rw [hz]
    simp
  have htsum : (∑' k : Fin d → ℤ,
      tensorDyadicSquareTerm r s k * coefficientSquareTerm r f k) =
      ∑ k ∈ SmoothResolution.frequencyBox s,
        tensorDyadicSquareTerm r s k * coefficientSquareTerm r f k := by
    exact tsum_eq_sum (f := fun k : Fin d → ℤ =>
      tensorDyadicSquareTerm r s k * coefficientSquareTerm r f k)
      (L := SummationFilter.unconditional (Fin d → ℤ))
      (s := SmoothResolution.frequencyBox s)
      (fun k hk => by rw [hsupport k hk]; simp)
  rw [htsum, hfiniteSum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold tensorDyadicSquareTerm coefficientSquareTerm
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤
    (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
      (SmoothResolution.tensorMultiplier s k) ^ 2)]
  congr 1

private theorem square_two_sum_eq (x : ℝ) : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
  congr 1
  ring

/-- Reverse spectral estimate for the actual fixed smooth square function.
It uses Parseval on each literal cutoff block, then the finite-overlap tensor
dyadic multiplier estimate above. -/
theorem squareFunction_lintegral_le_of_fourier_energy {d : ℕ}
    (r : ℝ) (hr : 0 ≤ r) (f : RealPeriodic d) (B : ℝ≥0∞)
    (hB : (∑' k : Fin d → ℤ,
      ENNReal.ofReal (spectralWeight r k * ‖realPeriodicFourierCoeff f k‖ ^ 2)) ≤ B) :
    (∫⁻ x : UnitAddTorus (Fin d),
      AlignmentPeriodicCutoffClasses.squareFunctionSquared smoothResolutionCutoff r f x
        ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤
      ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) * B := by
  classical
  let μ := (volume : Measure (UnitAddTorus (Fin d)))
  let g : (Fin d → ℕ) → UnitAddTorus (Fin d) → ℂ := fun s =>
    AlignmentPeriodicAdmissibleCutoff.admissibleBlock smoothResolutionCutoff s f
  let w : (Fin d → ℕ) → ℝ := fun s =>
    (2 : ℝ) ^ (r * ∑ i, (s i : ℝ))
  have hw : ∀ s, 0 ≤ w s := by intro s; dsimp [w]; positivity
  have hg : ∀ s, AEStronglyMeasurable (g s) μ := by
    intro s
    exact (AlignmentPeriodicAdmissibleCutoff.admissibleBlock
      smoothResolutionCutoff s f).continuous.aestronglyMeasurable
  have hP2 := BrownianSharp.AlignmentPeriodicP2BesovIdentity.lintegral_tsum_weighted_block_sq_eq_tsum
    μ g w hw (fun s => hg s)
  have hpoint (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
      ENNReal.ofReal
        ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) * ‖g s x‖ ^ 2) =
      ENNReal.ofReal (w s ^ 2 * ‖g s x‖ ^ 2) := by
    apply congrArg ENNReal.ofReal
    have hpow : (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) =
        ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ 2 := by
      calc
        _ = (2 : ℝ) ^ (2 * (r * ∑ i, (s i : ℝ))) := by congr 1 <;> ring
        _ = _ := square_two_sum_eq (r * ∑ i, (s i : ℝ))
    calc
      (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) * ‖g s x‖ ^ 2 =
          ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ 2 * ‖g s x‖ ^ 2 := by
        rw [hpow]
      _ = w s ^ 2 * ‖g s x‖ ^ 2 := by rfl
  have hsq : (∫⁻ x : UnitAddTorus (Fin d),
      AlignmentPeriodicCutoffClasses.squareFunctionSquared smoothResolutionCutoff r f x ∂μ) =
      ∑' s : Fin d → ℕ,
        (AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f) ^ 2 := by
    calc
      _ = ∫⁻ x, ∑' s : Fin d → ℕ,
          ENNReal.ofReal (w s ^ 2 * ‖g s x‖ ^ 2) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards [] with x
            unfold AlignmentPeriodicCutoffClasses.squareFunctionSquared
            apply tsum_congr
            intro s
            exact hpoint s x
      _ = ∑' s : Fin d → ℕ,
          (ENNReal.ofReal (w s) * eLpNorm (g s) 2 μ) ^ 2 := hP2
      _ = _ := by
        apply tsum_congr
        intro s
        dsimp [g, w, AlignmentPeriodicCutoffClasses.weightedBlockNorm]
  have htotal :
      (∑' s : Fin d → ℕ,
        (AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f) ^ 2) =
      ∑' k : Fin d → ℤ,
        coefficientSquareTerm r f k *
          (∑' s : Fin d → ℕ, tensorDyadicSquareTerm r s k) := by
    calc
      _ = ∑' s : Fin d → ℕ, ∑' k : Fin d → ℤ,
          tensorDyadicSquareTerm r s k * coefficientSquareTerm r f k := by
            apply tsum_congr
            intro s
            exact weightedBlockNorm_sq_eq_fourier_tsum r f s
      _ = ∑' k : Fin d → ℤ, ∑' s : Fin d → ℕ,
          tensorDyadicSquareTerm r s k * coefficientSquareTerm r f k := ENNReal.tsum_comm
      _ = _ := by
        apply tsum_congr
        intro k
        rw [ENNReal.tsum_mul_right]
        simp [mul_comm]
  have hpointwise (k : Fin d → ℤ) :
      coefficientSquareTerm r f k * (∑' s : Fin d → ℕ, tensorDyadicSquareTerm r s k) ≤
        ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) *
          ENNReal.ofReal (spectralWeight r k * ‖realPeriodicFourierCoeff f k‖ ^ 2) := by
    have hkernel := tensor_dyadic_square_tsum_le r hr k
    have hmul := mul_le_mul_of_nonneg_left hkernel (bot_le : 0 ≤ coefficientSquareTerm r f k)
    have hfactor : coefficientSquareTerm r f k *
        ENNReal.ofReal (((2 * (4 : ℝ) ^ r) ^ d) * spectralWeight r k) =
        ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) *
          ENNReal.ofReal (spectralWeight r k * ‖realPeriodicFourierCoeff f k‖ ^ 2) := by
      unfold coefficientSquareTerm
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * (4 : ℝ) ^ r) ^ d),
        ENNReal.ofReal_mul (show 0 ≤ spectralWeight r k from
          Finset.prod_nonneg fun i hi => Real.rpow_nonneg (by positivity) r)]
      ac_rfl
    rw [hfactor] at hmul
    exact hmul
  have htotalBound := ENNReal.tsum_le_tsum hpointwise
  calc
    _ = ∑' s : Fin d → ℕ,
        (AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f) ^ 2 := hsq
    _ = ∑' k : Fin d → ℤ,
        coefficientSquareTerm r f k * (∑' s : Fin d → ℕ,
          tensorDyadicSquareTerm r s k) := htotal
    _ ≤ ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) * B := by
      calc
        _ ≤ ∑' k : Fin d → ℤ,
            ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) *
              ENNReal.ofReal (spectralWeight r k * ‖realPeriodicFourierCoeff f k‖ ^ 2) := htotalBound
        _ = ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) *
            (∑' k : Fin d → ℤ,
              ENNReal.ofReal (spectralWeight r k * ‖realPeriodicFourierCoeff f k‖ ^ 2)) := by
              rw [ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) * B :=
              mul_le_mul_of_nonneg_left hB bot_le

/-- A weighted Fourier-energy bound with the explicit normalization needed to
place the actual periodic function in the literal smooth-cutoff Sobolev unit
ball. This is the scaled-ball interface used for localized source outputs. -/
theorem mem_sobolev_two_unitBall_of_fourier_energy {d : ℕ}
    (r : ℝ) (hr : 0 ≤ r) (f : RealPeriodic d) (B : ℝ≥0∞)
    (hB : (∑' k : Fin d → ℤ,
      ENNReal.ofReal (spectralWeight r k * ‖realPeriodicFourierCoeff f k‖ ^ 2)) ≤ B)
    (hscale : ENNReal.ofReal ((2 * (4 : ℝ) ^ r) ^ d) * B ≤ 1) :
    AlignmentPeriodicCutoffClasses.SobolevUnitBall smoothResolutionCutoff 2 r f := by
  rw [AlignmentPeriodicCutoffClasses.SobolevUnitBall_fixed]
  change (∫⁻ x : UnitAddTorus (Fin d),
    (SmoothResolution.squareFunctionSquared r f x) ^ (2 / 2)
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1
  simpa using (squareFunction_lintegral_le_of_fourier_energy r hr f B hB).trans hscale

end BrownianSharp.AlignmentPaperPeriodicFourierReverse
