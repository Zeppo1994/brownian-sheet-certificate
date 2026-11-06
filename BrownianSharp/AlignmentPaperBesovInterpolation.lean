import BrownianSharp.AlignmentPaperBesovMaskedSynthesis
import BrownianSharp.AlignmentPaperSequenceSplit
import BrownianSharp.AlignmentPeriodicCutoffScaling
import BrownianSharp.AlignmentPaperWidthDecomposition
import BrownianSharp.AlignmentPaperPeriodic
import BrownianSharp.AlignmentPaperInterpolationRates
import BrownianSharp.AlignmentPaperPeriodicBesov
import BrownianSharp.AlignmentEndpointDyadicEntropy
import BrownianSharp.AlignmentPeriodicUpperReduction
import BrownianSharp.AlignmentPeriodicScaledClassTransfer
import BrownianSharp.AlignmentScaledWidthRates

/-! The actual high/low K-method decomposition for finite-theta periodic
Besov balls. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

private instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
private instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩

namespace BrownianSharp.AlignmentPaperBesovInterpolation

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffScaling
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.AlignmentPaperBesovMaskedSynthesis
open BrownianSharp.AlignmentPaperSequenceSplit
open BrownianSharp.AlignmentPeriodicCutoffYoung
open BrownianSharp.AlignmentPaperWidthDecomposition
open BrownianSharp.AlignmentPaperPeriodic
open BrownianSharp.AlignmentPaperSequenceSplit
open BrownianSharp.AlignmentPaperInterpolationRates
open BrownianSharp.AlignmentPaperPeriodicBesov
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentEndpointDyadicEntropy
open BrownianSharp.AlignmentPeriodicUpperReduction
open BrownianSharp.AlignmentPeriodicScaledClassTransfer
open BrownianSharp.AlignmentScaledSetWidth
open BrownianSharp.AlignmentScaledWidthRates
open BrownianSharp.Latest
open HaarQuarter.TheoremD.Width

private theorem half_index_rate_le {r a : ℝ} {k N : ℕ}
    (hr : 0 < r) (ha : 0 ≤ a) (hk : 2 ≤ k)
    (hNk : N ≤ 4 * k) (hkN : k ≤ N) :
    logarithmicIndexRate r a k ≤ 4 ^ r * logarithmicIndexRate r a N := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNkR : (N : ℝ) ≤ 4 * k := by exact_mod_cast hNk
  have hkNR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hfourk : (0 : ℝ) < 4 * k := by positivity
  have hpow : (4 * (k : ℝ)) ^ (-r) ≤ (N : ℝ) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos hNpos hNkR (by linarith)
  have hmulrpow : (4 * (k : ℝ)) ^ (-r) = 4 ^ (-r) * (k : ℝ) ^ (-r) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
  have hcancel : (4 : ℝ) ^ r * 4 ^ (-r) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hpoly : (k : ℝ) ^ (-r) ≤ 4 ^ r * (N : ℝ) ^ (-r) := by
    calc
      (k : ℝ) ^ (-r) = (4 ^ r * 4 ^ (-r)) * (k : ℝ) ^ (-r) := by rw [hcancel, one_mul]
      _ = 4 ^ r * (4 ^ (-r) * (k : ℝ) ^ (-r)) := by ring
      _ = 4 ^ r * (4 * (k : ℝ)) ^ (-r) := by rw [hmulrpow]
      _ ≤ 4 ^ r * (N : ℝ) ^ (-r) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by norm_num) _)
  have hlogle : Real.log (k : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hkpos hkNR
  have hlogpow : (Real.log (k : ℝ)) ^ a ≤ (Real.log (N : ℝ)) ^ a :=
    Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
      hlogle ha
  unfold logarithmicIndexRate
  calc
    (k : ℝ) ^ (-r) * (Real.log (k : ℝ)) ^ a ≤
        (4 ^ r * (N : ℝ) ^ (-r)) * (Real.log (k : ℝ)) ^ a :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))) _)
    _ ≤ (4 ^ r * (N : ℝ) ^ (-r)) * (Real.log (N : ℝ)) ^ a := by
      gcongr
    _ = 4 ^ r * ((N : ℝ) ^ (-r) * (Real.log (N : ℝ)) ^ a) := by ring

/-- One fixed cutoff-kernel constant, selected once for each dimension. -/
noncomputable def maskedKernelConstant (d : ℕ) : ℝ := by
  let h := exists_admissibleBlockKernel_uniform_L1_bound (d := d) smoothResolutionCutoff
  exact max 1 (Classical.choose h)

theorem maskedKernelConstant_pos (d : ℕ) : 0 < maskedKernelConstant d := by
  dsimp [maskedKernelConstant]
  positivity

theorem maskedKernelConstant_bound {d : ℕ} (s : Fin d → ℕ) :
    (∫ x : UnitAddTorus (Fin d),
      ‖(admissibleBlockKernel smoothResolutionCutoff s) x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      maskedKernelConstant d ^ d := by
  let h := exists_admissibleBlockKernel_uniform_L1_bound (d := d) smoothResolutionCutoff
  have hspec := Classical.choose_spec h
  dsimp [maskedKernelConstant]
  have hnonneg := hspec.1
  calc
    _ ≤ Classical.choose h ^ d := hspec.2 s
    _ ≤ max 1 (Classical.choose h) ^ d := by
      gcongr
      exact le_max_right (1 : ℝ) _

/-- Threshold splitting of the actual smooth dyadic blocks, with each part
normalized into the two literal endpoint balls. -/
theorem actualBesov_highLow_decomposition {d : ℕ} {r T : ℝ}
    (hr : 1/2 < r) (hrr : 0 ≤ r) (hT : 0 < T) (f : RealPeriodic d)
    {theta : ℝ≥0∞} (htheta : theta ≠ ⊤) (htheta2 : 2 ≤ theta.toReal)
    (hf : AlignmentPeriodicCutoffClasses.BesovUnitBall
      smoothResolutionCutoff 2 r theta f) :
    ∃ u v : RealPeriodic d,
      AlignmentPeriodicCutoffClasses.BesovUnitBall smoothResolutionCutoff 2 r 2 u ∧
      AlignmentPeriodicCutoffClasses.NikolskyUnitBall smoothResolutionCutoff 2 r v ∧
      f = (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * T ^ (1 - theta.toReal / 2)) • u +
        (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * T) • v := by
  classical
  let a : (Fin d → ℕ) → ℝ≥0∞ := fun s => weightedBlockNorm smoothResolutionCutoff 2 r s f
  have henergy : (∑' s : Fin d → ℕ, a s ^ theta.toReal) ≤ 1 := by
    simpa [AlignmentPeriodicCutoffClasses.BesovUnitBall, htheta, a] using hf
  have hthetaPos : 0 < theta.toReal := by linarith
  have hNClass : NikolskyUnitBall smoothResolutionCutoff 2 r f := by
    change ∀ s, weightedBlockNorm smoothResolutionCutoff 2 r s f ≤ 1
    intro s
    exact term_le_one_of_power_sum_le_one a theta.toReal hthetaPos henergy s
  have hN : SmoothResolution.NikolskyUnitBall 2 r f := by
    simpa using hNClass
  let L : ℝ := maskedKernelConstant d
  have hL : 0 ≤ L := (maskedKernelConstant_pos d).le
  have hLpos : 0 < L := maskedKernelConstant_pos d
  have hKernel : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d),
        ‖(admissibleBlockKernel smoothResolutionCutoff s) x‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d := by
    intro s
    exact maskedKernelConstant_bound s
  let τ : ℝ≥0∞ := ENNReal.ofReal T
  have hτpos : 0 < τ := ENNReal.ofReal_pos.mpr hT
  have hτtop : τ ≠ ⊤ := ENNReal.ofReal_ne_top
  let S : Set (Fin d → ℕ) := {s | τ < a s}
  let high : RealPeriodic d := maskedBlockRealization S f r hr hN
  let low : RealPeriodic d := maskedBlockRealization Sᶜ f r hr hN
  have hhighSel : (∑' s : Fin d → ℕ,
      if s ∈ S then a s ^ (2 : ℕ) else 0) ≤ τ ^ (2 - theta.toReal) := by
    calc
      _ = ∑' s : Fin d → ℕ, highPart a τ s ^ (2 : ℕ) := by
        apply tsum_congr
        intro s
        change (if τ < a s then a s ^ (2 : ℕ) else 0) =
          highPart a τ s ^ (2 : ℕ)
        simp [highPart]
      _ ≤ τ ^ (2 - theta.toReal) :=
        highPart_square_sum_le a theta.toReal htheta2 τ hτpos hτtop henergy
  have hhighSel' : (∑' s : Fin d → ℕ,
      if s ∈ S then a s ^ (ENNReal.toReal (2 : ℝ≥0∞)) else 0) ≤
        τ ^ (2 - theta.toReal) := by
    calc
      _ = ∑' s : Fin d → ℕ, if s ∈ S then a s ^ (2 : ℕ) else 0 := by
        apply tsum_congr
        intro s
        by_cases hs : s ∈ S <;> simp [ENNReal.toReal_ofNat, ENNReal.rpow_natCast, hs]
      _ ≤ _ := hhighSel
  have hlowSel : ∀ s, s ∈ Sᶜ → a s ≤ τ := by
    intro s hs
    have hnot : ¬ τ < a s := by simpa [S] using hs
    calc
      a s = lowPart a τ s := by simp [lowPart, hnot]
      _ ≤ τ := lowPart_le a τ s
  have hEnergyHigh :=
    maskedBesovEnergy_le_selectedEnergy hr hrr f hN S L hL hKernel
      (2 : ℝ≥0∞) (by norm_num) (by norm_num) (τ ^ (2 - theta.toReal))
      (by simpa only [ENNReal.toReal_ofNat] using hhighSel')
  have hSupLow :=
    maskedWeightedBlockNorm_le_selectedSup hr hrr f hN Sᶜ L hL hKernel τ
      (by intro s hs; exact hlowSel s (by simpa using hs))
  have hsum := complementary_maskedBlockRealizations_add hr f hN S
  let K : ℝ := (L ^ d * (2 : ℝ) ^ (2 * r * d)) * (5 : ℝ) ^ d
  have hrpos : 0 < r := by linarith
  have hK : 0 < K := by dsimp [K, L]; positivity
  have hKcast :
      ENNReal.ofReal (L ^ d * (2 : ℝ) ^ (2 * r * d)) * (5 ^ d : ℝ≥0∞) =
        ENNReal.ofReal K := by
    rw [show (5 ^ d : ℝ≥0∞) = ENNReal.ofReal ((5 : ℝ) ^ d) by norm_num]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ d * (2 : ℝ) ^ (2 * r * d))]
  have hhighBound : (∑' s : Fin d → ℕ,
      weightedBlockNorm smoothResolutionCutoff 2 r s high ^ (2 : ℝ)) ≤
      ENNReal.ofReal (K ^ 2 * T ^ (2 - theta.toReal)) := by
    have hbase := hEnergyHigh
    rw [hKcast] at hbase
    have hτreal : τ ^ (2 - theta.toReal) =
        ENNReal.ofReal (T ^ (2 - theta.toReal)) := by
      change (ENNReal.ofReal T) ^ (2 - theta.toReal) = _
      rw [ENNReal.ofReal_rpow_of_pos hT]
    rw [hτreal] at hbase
    have hfac₁ : ENNReal.ofReal K ^ (ENNReal.toReal (2 : ℝ≥0∞)) =
        ENNReal.ofReal (K ^ 2) := by
      calc
        ENNReal.ofReal K ^ ENNReal.toReal (2 : ℝ≥0∞) =
            ENNReal.ofReal K ^ (↑(2 : ℕ) : ℝ) := by
              norm_num [ENNReal.toReal_ofNat]
        _ = ENNReal.ofReal K ^ (2 : ℕ) := ENNReal.rpow_natCast _ _
        _ = ENNReal.ofReal (K ^ 2) := (ENNReal.ofReal_pow hK.le 2).symm
    rw [hfac₁, ← ENNReal.ofReal_mul (by positivity : 0 ≤ K ^ 2)] at hbase
    simpa [high, ENNReal.toReal_ofNat] using hbase
  have hlowBound : ∀ s, weightedBlockNorm smoothResolutionCutoff 2 r s low ≤
      ENNReal.ofReal (K * T) := by
    intro s
    have h := hSupLow s
    rw [hKcast] at h
    rw [show τ = ENNReal.ofReal T by rfl] at h
    simpa [low, ← ENNReal.ofReal_mul hK.le] using h
  let A : ℝ := K * T ^ (1 - theta.toReal / 2)
  let B : ℝ := K * T
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let cA : ℝ := A⁻¹
  let cB : ℝ := B⁻¹
  have hcA : 0 < cA := by dsimp [cA]; positivity
  have hcB : 0 < cB := by dsimp [cB]; positivity
  refine ⟨cA • high, cB • low, ?_, ?_, ?_⟩
  · change (∑' s : Fin d → ℕ,
        AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s (cA • high) ^
        (ENNReal.toReal (2 : ℝ≥0∞))) ≤ 1
    rw [BesovEnergy_smul smoothResolutionCutoff hcA 2 r (2 : ℝ≥0∞) high]
    have hcPow : ENNReal.ofReal (cA ^ ENNReal.toReal (2 : ℝ≥0∞)) =
        ENNReal.ofReal (cA ^ 2) := by norm_num [ENNReal.toReal_ofNat]
    rw [hcPow]
    have hscaled : ENNReal.ofReal (cA ^ 2) *
        ENNReal.ofReal (K ^ 2 * T ^ (2 - theta.toReal)) = 1 := by
      have hp : (T ^ (1 - theta.toReal / 2)) ^ 2 =
          T ^ (2 - theta.toReal) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
        congr 1
        ring
      have hdenom : (K * T ^ (1 - theta.toReal / 2)) ^ 2 =
          K ^ 2 * T ^ (2 - theta.toReal) := by
        rw [mul_pow, hp]
      have hcancel : cA ^ 2 * (K ^ 2 * T ^ (2 - theta.toReal)) = 1 := by
        change (K * T ^ (1 - theta.toReal / 2))⁻¹ ^ 2 *
          (K ^ 2 * T ^ (2 - theta.toReal)) = 1
        rw [← hdenom]
        field_simp [ne_of_gt (mul_pos hK (Real.rpow_pos_of_pos hT _))]
      calc
        _ = ENNReal.ofReal (cA ^ 2 * (K ^ 2 * T ^ (2 - theta.toReal))) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg cA)]
        _ = 1 := by rw [hcancel]; norm_num
    calc
      _ ≤ ENNReal.ofReal (cA ^ 2) *
          ENNReal.ofReal (K ^ 2 * T ^ (2 - theta.toReal)) :=
        mul_le_mul_of_nonneg_left hhighBound bot_le
      _ = 1 := hscaled
  · change ∀ s, AlignmentPeriodicCutoffClasses.weightedBlockNorm
      smoothResolutionCutoff 2 r s (cB • low) ≤ 1
    intro s
    rw [AlignmentPeriodicCutoffScaling.weightedBlockNorm_smul
      smoothResolutionCutoff hcB 2 r s low]
    calc
      ENNReal.ofReal cB * weightedBlockNorm smoothResolutionCutoff 2 r s low ≤
          ENNReal.ofReal cB * ENNReal.ofReal (K * T) :=
        mul_le_mul_of_nonneg_left (hlowBound s) bot_le
      _ = 1 := by
        rw [← ENNReal.ofReal_mul hcB.le]
        dsimp [cB, B]
        field_simp [ne_of_gt hK, ne_of_gt hT]
        norm_num
  · have hAc : A * cA = 1 := by dsimp [cA]; exact mul_inv_cancel₀ hA.ne'
    have hBc : B * cB = 1 := by dsimp [cB]; exact mul_inv_cancel₀ hB.ne'
    have hAeq : A = ((maskedKernelConstant d ^ d * (2 : ℝ) ^
        (2 * r * d)) * (5 : ℝ) ^ d) * T ^ (1 - theta.toReal / 2) := by
      dsimp [A, K, L]
    have hBeq : B = ((maskedKernelConstant d ^ d * (2 : ℝ) ^
        (2 * r * d)) * (5 : ℝ) ^ d) * T := by
      dsimp [B, K, L]
    have hu : (A * cA) • high = A • (cA • high) := by rw [smul_smul]
    have hv : (B * cB) • low = B • (cB • low) := by rw [smul_smul]
    calc
      f = high + low := hsum.symm
      _ = (A * cA) • high + (B * cB) • low := by
        simp [hAc, hBc]
      _ = A • (cA • high) + B • (cB • low) := by rw [hu, hv]
      _ = (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
            (5 : ℝ) ^ d) * T ^ (1 - theta.toReal / 2)) •
            (cA • high) + (((maskedKernelConstant d ^ d * (2 : ℝ) ^
            (2 * r * d)) * (5 : ℝ) ^ d) * T) • (cB • low) := by
        rw [hAeq, hBeq]

/-- Concrete width-sum estimate for the actual finite-theta smooth cutoff
Besov class, with the threshold scale left free for balancing endpoint rates. -/
theorem actualBesov_width_upper_of_endpoint_widths
    {d : ℕ} {r T : ℝ} (hr : 1/2 < r) (hrr : 0 ≤ r) (hT : 0 < T)
    {theta : ℝ≥0∞} (htheta : theta ≠ ⊤) (htheta2 : 2 ≤ theta.toReal)
    (m n : ℕ) (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (h₀ : kolmogorovWidth
      (periodicLInfinityImage {u : RealPeriodic d |
        BesovUnitBall smoothResolutionCutoff 2 r 2 u}) m ≤ ENNReal.ofReal E₀)
    (h₁ : kolmogorovWidth
      (periodicLInfinityImage {v : RealPeriodic d |
        NikolskyUnitBall smoothResolutionCutoff 2 r v}) n ≤ ENNReal.ofReal E₁) :
    kolmogorovWidth
      (periodicLInfinityImage {f : RealPeriodic d |
        BesovUnitBall smoothResolutionCutoff 2 r theta f}) (m+n) ≤
      ENNReal.ofReal
        ((((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * T ^ (1 - theta.toReal / 2)) * E₀ +
        (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * T) * E₁) := by
  let K : ℝ := (maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) * (5 : ℝ) ^ d
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hrpos : 0 < r := by linarith
  have hmasked : 0 < maskedKernelConstant d := maskedKernelConstant_pos d
  have hK : 0 < K := by dsimp [K]; positivity
  let A : ℝ := K * T ^ (1 - theta.toReal / 2)
  let B : ℝ := K * T
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hdecomp : ∀ y ∈ periodicLInfinityImage
      {f : RealPeriodic d | BesovUnitBall smoothResolutionCutoff 2 r theta f},
      ∃ u ∈ periodicLInfinityImage
          {u : RealPeriodic d | BesovUnitBall smoothResolutionCutoff 2 r 2 u},
        ∃ v ∈ periodicLInfinityImage
          {v : RealPeriodic d | NikolskyUnitBall smoothResolutionCutoff 2 r v},
          y = A • u + B • v := by
    rintro y ⟨f, hf, rfl⟩
    obtain ⟨u, v, hu, hv, heq⟩ :=
      actualBesov_highLow_decomposition hr hrr hT f htheta htheta2 hf
    refine ⟨(ContinuousMap.toLp ⊤ volume ℝ) u, ⟨u, hu, rfl⟩,
      (ContinuousMap.toLp ⊤ volume ℝ) v, ⟨v, hv, rfl⟩, ?_⟩
    have hmap := congrArg (ContinuousMap.toLp ⊤ volume ℝ) heq
    have hA : A = K * T ^ (1 - theta.toReal / 2) := rfl
    have hB : B = K * T := rfl
    simpa only [map_add, map_smul, hA, hB, K] using hmap
  have hsum := width_upper_of_endpoint_decomposition
    (periodicLInfinityImage {f : RealPeriodic d |
      BesovUnitBall smoothResolutionCutoff 2 r theta f})
    (periodicLInfinityImage {u : RealPeriodic d |
      BesovUnitBall smoothResolutionCutoff 2 r 2 u})
    (periodicLInfinityImage {v : RealPeriodic d |
      NikolskyUnitBall smoothResolutionCutoff 2 r v}) m n A B E₀ E₁
    hA hB hE₀ hE₁ hdecomp h₀ h₁
  simpa [A, B, K] using hsum

/-- Interpolated eventual width upper rate for the actual smooth cutoff class.
The endpoint width upper estimates are the already certified theta-two and
Nikolsky bounds; the proof balances the concrete masked decomposition and
converts the half-index estimate back to every sufficiently large index. -/
theorem actualBesov_width_upper_rate_of_endpoint_rates
    {d : ℕ} {r : ℝ} {theta : ℝ≥0∞}
    (hd : 2 ≤ d) (hr : 1/2 < r) (htheta : theta ≠ ⊤)
    (htheta2 : 2 < theta.toReal)
    (C₀ C₁ : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (k₀ k₁ : ℕ) (hk₀ : 2 ≤ k₀) (hk₁ : 2 ≤ k₁)
    (h₀ : ∀ k : ℕ, k₀ ≤ k → kolmogorovWidth
      (periodicLInfinityImage {u : RealPeriodic d |
        BesovUnitBall smoothResolutionCutoff 2 r 2 u}) k ≤
      ENNReal.ofReal (C₀ * logarithmicIndexRate r
        (r * (d - 1 : ℕ) + 1 / 2) k))
    (h₁ : ∀ k : ℕ, k₁ ≤ k → kolmogorovWidth
      (periodicLInfinityImage {v : RealPeriodic d |
        NikolskyUnitBall smoothResolutionCutoff 2 r v}) k ≤
      ENNReal.ofReal (C₁ * logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      kolmogorovWidth
        (periodicLInfinityImage {f : RealPeriodic d |
          BesovUnitBall smoothResolutionCutoff 2 r theta f}) N ≤
      ENNReal.ofReal (C * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) N) := by
  have hrpos : 0 < r := by linarith
  have ha₀ : 0 ≤ r * (d - 1 : ℕ) + 1 / 2 := by positivity
  have ha₁ : 0 ≤ (r + 1 / 2) * (d - 1 : ℕ) + 1 / 2 := by positivity
  let a₀ : ℝ := r * (d - 1 : ℕ) + 1 / 2
  let a₁ : ℝ := (r + 1 / 2) * (d - 1 : ℕ) + 1 / 2
  let aθ : ℝ := (r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2
  let w : ℝ := 2 / theta.toReal
  have hθpos : 0 < theta.toReal := by linarith
  have hwpos : 0 < w := by dsimp [w]; positivity
  have hwle : w ≤ 1 := by dsimp [w]; rw [div_le_one hθpos]; linarith
  let D : ℝ := (d - 1 : ℕ)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (by omega : 0 < d - 1)
  have hdcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] 
  have hExp : w * a₀ + (1 - w) * a₁ = aθ := by
    dsimp [w, a₀, a₁, aθ]
    rw [hdcast]
    simpa [one_div] using
      (besov_interpolation_log_exponent r theta.toReal (d - 1 : ℝ)
        (ne_of_gt hθpos))
  have hC : 0 < (maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
      (5 : ℝ) ^ d := by
    have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast Nat.zero_le d
    have hmask : 0 < maskedKernelConstant d := maskedKernelConstant_pos d
    positivity
  let N₀ : ℕ := max 4 (2 * max k₀ k₁ + 2)
  have hN₀ : 2 ≤ N₀ := by dsimp [N₀]; omega
  refine ⟨((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
      (5 : ℝ) ^ d) * 2 * C₀ ^ w * C₁ ^ (1 - w) * 4 ^ r,
    ?_, N₀, hN₀, ?_⟩
  · positivity
  · intro N hN
    let k : ℕ := N / 2
    have hN4 : 4 ≤ N := by dsimp [N₀] at hN; omega
    have hk2 : 2 ≤ k := by dsimp [k]; omega
    have hk0 : k₀ ≤ k := by
      dsimp [k, N₀] at *
      omega
    have hk1 : k₁ ≤ k := by
      dsimp [k, N₀] at *
      omega
    have h2kN : 2 * k ≤ N := by dsimp [k]; omega
    have hNk : N ≤ 4 * k := by dsimp [k]; omega
    have hkN : k ≤ N := by dsimp [k]; omega
    let E₀ := C₀ * logarithmicIndexRate r a₀ k
    let E₁ := C₁ * logarithmicIndexRate r a₁ k
    have hE₀ : 0 < E₀ := by
      dsimp [E₀, a₀]
      exact mul_pos hC₀ (AlignmentWidthRates.logarithmicIndexRate_pos r _ hk2)
    have hE₁ : 0 < E₁ := by
      dsimp [E₁, a₁]
      exact mul_pos hC₁ (AlignmentWidthRates.logarithmicIndexRate_pos r _ hk2)
    let T := balancedThreshold E₀ E₁ theta.toReal
    have hT : 0 < T := balancedThreshold_pos E₀ E₁ theta.toReal hE₀ hE₁
    have hwidth := actualBesov_width_upper_of_endpoint_widths
      hr (by linarith) hT (theta := theta) htheta (le_of_lt htheta2)
      k k E₀ E₁ hE₀.le hE₁.le
      (by simpa [E₀, a₀] using h₀ k hk0)
      (by simpa [E₁, a₁] using h₁ k hk1)
    have hmono := kolmogorovWidth_antitone
      (periodicLInfinityImage {f : RealPeriodic d |
        BesovUnitBall smoothResolutionCutoff 2 r theta f}) h2kN
    have hwidth2k : kolmogorovWidth
        (periodicLInfinityImage {f : RealPeriodic d |
          BesovUnitBall smoothResolutionCutoff 2 r theta f}) (2*k) ≤
        ENNReal.ofReal
          ((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d) *
            (5 : ℝ) ^ d * T ^ (1 - theta.toReal / 2)) * E₀ +
           (maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d) *
            (5 : ℝ) ^ d * T) * E₁) := by
      simpa [two_mul, mul_assoc] using hwidth
    have hwidthN := hmono.trans hwidth2k
    have hcost : E₀ * T ^ (1 - theta.toReal / 2) + E₁ * T =
        2 * E₀ ^ w * E₁ ^ (1 - w) := by
      dsimp [T, w]
      exact balanced_endpoint_cost E₀ E₁ theta.toReal hE₀ hE₁ (ne_of_gt hθpos)
    have hgeom := logarithmicIndexRate_geometric_mean r a₀ a₁ w C₀ C₁
      hC₀ hC₁ k hk2
    have hrateExp := congrArg (fun z : ℝ => logarithmicIndexRate r z k) hExp
    have hfactor : E₀ ^ w * E₁ ^ (1 - w) =
        (C₀ ^ w * C₁ ^ (1 - w)) * logarithmicIndexRate r aθ k := by
      calc
        E₀ ^ w * E₁ ^ (1 - w) =
            (C₀ * logarithmicIndexRate r a₀ k) ^ w *
              (C₁ * logarithmicIndexRate r a₁ k) ^ (1 - w) := by
                rfl
        _ = (C₀ ^ w * C₁ ^ (1 - w)) *
              logarithmicIndexRate r (w * a₀ + (1 - w) * a₁) k := hgeom
        _ = (C₀ ^ w * C₁ ^ (1 - w)) * logarithmicIndexRate r aθ k := by
              rw [hrateExp]
    have hcost' :
        ((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d * T ^ (1 - theta.toReal / 2)) * E₀ +
        ((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d * T) * E₁ =
        (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * 2 * C₀ ^ w * C₁ ^ (1 - w)) *
          logarithmicIndexRate r aθ k := by
      let K := (maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) * (5 : ℝ) ^ d
      calc
        (K * T ^ (1 - theta.toReal / 2)) * E₀ + (K * T) * E₁ =
            K * (E₀ * T ^ (1 - theta.toReal / 2) + E₁ * T) := by ring
        _ = K * (2 * E₀ ^ w * E₁ ^ (1 - w)) := by rw [hcost]
        _ = K * (2 * (C₀ ^ w * C₁ ^ (1 - w)) *
              logarithmicIndexRate r aθ k) := by
          congr 1
          rw [show 2 * E₀ ^ w * E₁ ^ (1 - w) =
            2 * (E₀ ^ w * E₁ ^ (1 - w)) by ring, hfactor]
          ring
        _ = K * 2 * C₀ ^ w * C₁ ^ (1 - w) *
              logarithmicIndexRate r aθ k := by ring
    have hwidthCost : kolmogorovWidth
        (periodicLInfinityImage {f : RealPeriodic d |
          BesovUnitBall smoothResolutionCutoff 2 r theta f}) (2*k) ≤
        ENNReal.ofReal
          ((((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
            (5 : ℝ) ^ d) * 2 * C₀ ^ w * C₁ ^ (1 - w)) *
            logarithmicIndexRate r aθ k) := by
      have hraw := hwidth
      rw [show k+k=2*k by omega] at hraw
      have hEq : ((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d * T ^ (1 - theta.toReal / 2)) * E₀ +
        ((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d * T) * E₁ =
        (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * T ^ (1 - theta.toReal / 2)) * E₀ +
        (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * T) * E₁ := by ring
      rw [hEq, hcost'] at hraw
      exact hraw
    have hinv : theta.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (le_of_lt htheta2)
    have haθpos : 0 < aθ := by
      have hcoef : 0 < r + 1 / 2 - theta.toReal⁻¹ := by linarith
      dsimp [aθ]
      positivity
    have hrateKN := half_index_rate_le hrpos haθpos.le hk2 hNk hkN
    have hCoeff : 0 ≤ ((maskedKernelConstant d ^ d * (2 : ℝ) ^
        (2 * r * d)) * (5 : ℝ) ^ d) * 2 * C₀ ^ w * C₁ ^ (1 - w) := by
      positivity
    have hscale :
        (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * 2 * C₀ ^ w * C₁ ^ (1 - w)) *
          logarithmicIndexRate r aθ k ≤
        (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * 2 * C₀ ^ w * C₁ ^ (1 - w) * 4 ^ r) *
          logarithmicIndexRate r aθ N := by
      calc
        _ ≤ (((maskedKernelConstant d ^ d * (2 : ℝ) ^ (2 * r * d)) *
          (5 : ℝ) ^ d) * 2 * C₀ ^ w * C₁ ^ (1 - w)) *
          (4 ^ r * logarithmicIndexRate r aθ N) :=
          mul_le_mul_of_nonneg_left hrateKN hCoeff
        _ = _ := by ring
    have hwidthN' := hwidthN
    rw [hcost'] at hwidthN'
    have hfinal := hwidthN'.trans (ENNReal.ofReal_le_ofReal hscale)
    simpa [N₀, k, aθ, w, E₀, E₁] using hfinal

/-- Certified finite-theta width upper rate for the smooth cutoff: its two
endpoint hypotheses are discharged by the existing theta-two Besov and
Nikolsky width certificates. -/
theorem actualBesov_width_upper_rate_certified
    {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 1/2 < r)
    {theta : ℝ≥0∞} (htheta : theta ≠ ⊤) (htheta2 : 2 < theta.toReal) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      kolmogorovWidth
        (periodicLInfinityImage {f : RealPeriodic d |
          BesovUnitBall smoothResolutionCutoff 2 r theta f}) N ≤
      ENNReal.ofReal (C * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) N) := by
  have hbesov := periodic_besov_theta_two_width_certified
    smoothResolutionCutoff hd (p := (2 : ℝ≥0∞)) (by norm_num) hr
  obtain ⟨_, C₀, _, hC₀, k₀, hk₀, hB₂⟩ := hbesov
  let K₀ : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {u : RealPeriodic d |
      BesovUnitBall smoothResolutionCutoff 2 r 2 u}
  have hB₂op : ∀ k : ℕ, k₀ ≤ k → operatorKolmogorovNumber K₀ k ≤
      ENNReal.ofReal (C₀ * logarithmicIndexRate r
        (r * (d - 1 : ℕ) + 1 / 2) k) := by
    intro k hk
    exact (hB₂ k hk).2
  obtain ⟨C₀', hC₀', k₀', hk₀', hB₂legacy⟩ :=
    legacy_width_upper_of_operator_upper K₀ (by linarith : 0 < r)
      (by positivity : 0 ≤ r * (d - 1 : ℕ) + 1 / 2) hC₀ k₀ hk₀ hB₂op
  obtain ⟨_hSob, hNik⟩ :=
    BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_width_certified
      smoothResolutionCutoff d hd (2 : ℝ≥0∞) (by norm_num) r hr
  obtain ⟨_, C₁, _, hC₁, k₁, hk₁, hN⟩ := hNik
  let K₁ : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {v : RealPeriodic d |
      NikolskyUnitBall smoothResolutionCutoff 2 r v}
  have hNop : ∀ k : ℕ, k₁ ≤ k → operatorKolmogorovNumber K₁ k ≤
      ENNReal.ofReal (C₁ * logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) := by
    intro k hk
    exact (hN k hk).2
  obtain ⟨C₁', hC₁', k₁', hk₁', hNlegacy⟩ :=
    legacy_width_upper_of_operator_upper K₁ (by linarith : 0 < r)
      (by positivity : 0 ≤ (r + 1 / 2) * (d - 1 : ℕ) + 1 / 2)
      hC₁ k₁ hk₁ hNop
  exact actualBesov_width_upper_rate_of_endpoint_rates hd hr htheta htheta2
    C₀' C₁' hC₀' hC₁' k₀' k₁' hk₀' hk₁' hB₂legacy hNlegacy

/-- Full two-sided finite-theta entropy rate for the actual smooth periodic
cutoff Besov ball, combining the proved interpolation upper bound with the
existing mixed entropy lower certificate. -/
theorem actualBesov_entropy_equivalent_certified
    {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 1/2 < r)
    {theta : ℝ≥0∞} (htheta : theta ≠ ⊤) (htheta2 : 2 < theta.toReal) :
    twoSidedEntropyRate
      (periodicLInfinityImage {f : RealPeriodic d |
        BesovUnitBall smoothResolutionCutoff 2 r theta f})
      r ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) := by
  let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {f : RealPeriodic d |
      BesovUnitBall smoothResolutionCutoff 2 r theta f}
  let J : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {f : RealPeriodic d |
      SmoothResolution.NikolskyUnitBall 2 r f}
  have hsub : K ⊆ J := by
    rintro y ⟨f, hf, rfl⟩
    have henergy : (∑' s : Fin d → ℕ,
        weightedBlockNorm smoothResolutionCutoff 2 r s f ^ theta.toReal) ≤ 1 := by
      simpa [AlignmentPeriodicCutoffClasses.BesovUnitBall, htheta] using hf
    have hclass : NikolskyUnitBall smoothResolutionCutoff 2 r f := by
      change ∀ s, weightedBlockNorm smoothResolutionCutoff 2 r s f ≤ 1
      intro s
      exact term_le_one_of_power_sum_le_one
        (fun s => weightedBlockNorm smoothResolutionCutoff 2 r s f)
        theta.toReal (by linarith) henergy s
    exact ⟨f, (AlignmentPeriodicCutoffClasses.NikolskyUnitBall_fixed
      2 r f).1 hclass, rfl⟩
  have hzeroJ := BrownianSharp.AlignmentAuditPeriodicBoundedness.nikolsky_linf_width_zero_le_of_exponent
    (d := d) (p := (2 : ℝ≥0∞)) (by norm_num) r hr
  have hzero : kolmogorovWidth K 0 ≤
      ENNReal.ofReal (AlignmentAuditPeriodicBoundedness.periodicNikolskyRadius d r) := by
    exact (kolmogorovWidth_mono_set hsub 0).trans (by simpa [J] using hzeroJ)
  obtain ⟨CW, hCW, kW, hkW, hwidth⟩ :=
    actualBesov_width_upper_rate_certified hd hr htheta htheta2
  obtain ⟨cL, hcL, kL, hkL, hLower⟩ :=
    BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_mixed_entropy_certified
      smoothResolutionCutoff d hd (2 : ℝ≥0∞) (by norm_num) r
      (by norm_num [ENNReal.toReal_ofNat]; linarith) theta
      (by
        apply (ENNReal.toReal_le_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) htheta).1
        norm_num
        linarith)
  have hLowerK : ∀ k : ℕ, kL ≤ k →
      ENNReal.ofReal (cL * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k K := by
    intro k hk
    exact (hLower k hk).2.1
  have hUpperK := entropy_upper_all_indices_of_width_upper K (by linarith : 0 < r)
    (by
      have hinv : theta.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (le_of_lt htheta2)
      have hcoef : 0 ≤ r + 1 / 2 - theta.toReal⁻¹ := by linarith
      have hD : 0 ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity)
    (AlignmentAuditPeriodicBoundedness.periodicNikolsky_radius_nonneg
      (d := d) hr) hCW kW hkW hzero hwidth
  obtain ⟨cU, hcU, kU, hkU, hUpper⟩ := hUpperK
  refine ⟨min cL cU, cU, lt_min hcL hcU, hcU, max kL kU,
    hkL.trans (le_max_left _ _), ?_⟩
  intro k hk
  have hLower' := hLowerK k ((le_max_left kL kU).trans hk)
  have hUpper' := hUpper k ((le_max_right kL kU).trans hk)
  refine ⟨?_, hUpper'⟩
  calc
    ENNReal.ofReal (min cL cU * logarithmicIndexRate r
      ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
        ENNReal.ofReal (cL * logarithmicIndexRate r
          ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right (min_le_left _ _) 
              (AlignmentWidthRates.logarithmicIndexRate_nonneg _ _ _)
    _ ≤ HaarQuarter.TheoremD.entropyNumber k K := hLower'

/-- Full finite-theta upper interpolation for every admissible cutoff and
every spatial exponent p≥2, including p=∞. The cutoff comparison transfers
the actual Besov ball into a scalar image of the smooth cutoff ball; blockwise
Lp monotonicity then reduces p to the proved p=2 interpolation theorem. -/
theorem periodicBesov_entropy_equivalent_finite_theta
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {r : ℝ} (hr : 1/2 < r)
    {theta : ℝ≥0∞} (htheta : theta ≠ ⊤) (htheta2 : 2 < theta.toReal) :
    twoSidedEntropyRate
      (periodicLInfinityImage {f : RealPeriodic d |
        BesovUnitBall φ p r theta f})
      r ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) := by
  let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {f : RealPeriodic d |
      BesovUnitBall φ p r theta f}
  let J : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {f : RealPeriodic d |
      BesovUnitBall smoothResolutionCutoff 2 r theta f}
  have htheta1 : 1 ≤ theta := by
    apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top htheta).1
    norm_num
    linarith
  have hTransfer :=
    BrownianSharp.AlignmentPeriodicCutoffYoung.cutoffBesovScaleTransfer_certified
      smoothResolutionCutoff φ d p (by exact_mod_cast (show (1 : ℝ≥0∞) ≤ p from
        le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) hp)) r
      (by linarith : 0 ≤ r) theta htheta1
  obtain ⟨cScale, hcScale, hScale⟩ := hTransfer
  let A : ℝ := cScale⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hKimage : K ⊆ scalarImage A J := by
    apply periodicImage_subset_scalarImage
      {f : RealPeriodic d | BesovUnitBall φ p r theta f}
      {f : RealPeriodic d | BesovUnitBall smoothResolutionCutoff 2 r theta f}
      A hA
    intro f hf
    have hscaled : BesovUnitBall smoothResolutionCutoff p r theta (cScale • f) :=
      hScale f hf
    have hmono := AlignmentPaperPeriodicBesov.besovUnitBall_mono_exponent
      smoothResolutionCutoff (q := (2 : ℝ≥0∞)) (p := p) hp r (cScale • f) hscaled
    simpa [A, inv_inv] using hmono
  have hSmooth := actualBesov_entropy_equivalent_certified hd hr htheta htheta2
  obtain ⟨cS, CS, hcS, hCS, kS, hkS, hSmoothRates⟩ := hSmooth
  have hwidthSmooth := actualBesov_width_upper_rate_certified hd hr htheta htheta2
  obtain ⟨CW, hCW, kW, hkW, hW⟩ := hwidthSmooth
  have hJwidth : ∀ k : ℕ, kW ≤ k → kolmogorovWidth J k ≤
      ENNReal.ofReal (CW * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) := by
    intro k hk
    exact hW k hk
  have hscaledError : ∀ k : ℕ, kW ≤ k → kolmogorovWidth K k ≤
      ENNReal.ofReal (A * (CW * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k)) := by
    intro k hk
    apply kolmogorovWidth_le_of_subset_scalarImage A
      (CW * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k)
      hKimage k hA
    · exact mul_nonneg hCW.le (AlignmentWidthRates.logarithmicIndexRate_nonneg _ _ _)
    · exact hJwidth k hk
  have hzeroJcore := BrownianSharp.AlignmentAuditPeriodicBoundedness.nikolsky_linf_width_zero_le_of_exponent
    (d := d) (p := (2 : ℝ≥0∞)) (by norm_num) r hr
  have hJsubNik : J ⊆ periodicLInfinityImage
      {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall 2 r f} := by
    rintro y ⟨f, hf, rfl⟩
    have henergy : (∑' s : Fin d → ℕ,
        weightedBlockNorm smoothResolutionCutoff 2 r s f ^ theta.toReal) ≤ 1 := by
      simpa [AlignmentPeriodicCutoffClasses.BesovUnitBall, htheta] using hf
    have hclass : NikolskyUnitBall smoothResolutionCutoff 2 r f := by
      change ∀ s, weightedBlockNorm smoothResolutionCutoff 2 r s f ≤ 1
      intro s
      exact term_le_one_of_power_sum_le_one
        (fun s => weightedBlockNorm smoothResolutionCutoff 2 r s f)
        theta.toReal (by linarith) henergy s
    exact ⟨f, (AlignmentPeriodicCutoffClasses.NikolskyUnitBall_fixed
      2 r f).1 hclass, rfl⟩
  have hzeroJ := (kolmogorovWidth_mono_set hJsubNik 0).trans hzeroJcore
  have hzeroK := kolmogorovWidth_le_of_subset_scalarImage A
    (AlignmentAuditPeriodicBoundedness.periodicNikolskyRadius d r)
    hKimage 0 hA
    (AlignmentAuditPeriodicBoundedness.periodicNikolsky_radius_nonneg
      (d := d) hr)
    hzeroJ
  have hwidthK : ∀ k : ℕ, kW ≤ k → kolmogorovWidth K k ≤
      ENNReal.ofReal ((A * CW) * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) := by
    intro k hk
    convert hscaledError k hk using 1 <;> congr 1 <;> ring
  obtain ⟨CU, hCU, kU, hkU, hUpper⟩ :=
    entropy_upper_all_indices_of_width_upper K (by linarith : 0 < r)
      (by
        have hinv : theta.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) (le_of_lt htheta2)
        have hcoef : 0 ≤ r + 1 / 2 - theta.toReal⁻¹ := by linarith
        have hD : 0 ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        positivity)
      (mul_nonneg hA.le
        (AlignmentAuditPeriodicBoundedness.periodicNikolsky_radius_nonneg
          (d := d) hr))
      (mul_pos hA hCW) kW hkW hzeroK hwidthK
  obtain ⟨cL, hcL, kL, hkL, hLower⟩ :=
    BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_mixed_entropy_certified
      φ d hd p (lt_of_lt_of_le (by norm_num) hp) r
      (by
        by_cases htop : p = ⊤
        · simpa [htop] using (show 0 < r by linarith)
        · have hpR : 2 ≤ p.toReal := by
            have h := (ENNReal.toReal_le_toReal
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) htop).2 hp
            simpa only [ENNReal.toReal_ofNat] using h
          have hinv : p.toReal⁻¹ ≤ (1/2:ℝ) := by
            rw [inv_eq_one_div]
            exact one_div_le_one_div_of_le (by norm_num) hpR
          exact hinv.trans_lt hr)
      theta htheta1
  have hLowerK : ∀ k : ℕ, kL ≤ k → ENNReal.ofReal (cL * logarithmicIndexRate r
      ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
      HaarQuarter.TheoremD.entropyNumber k K := by
    intro k hk
    exact (hLower k hk).2.1
  refine ⟨min cL CU, CU, lt_min hcL hCU, hCU, max kL kU,
    hkL.trans (le_max_left _ _), ?_⟩
  intro k hk
  have hL := hLowerK k ((le_max_left kL kU).trans hk)
  have hU := hUpper k ((le_max_right kL kU).trans hk)
  refine ⟨?_, hU⟩
  calc
    ENNReal.ofReal (min cL CU * logarithmicIndexRate r
      ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
        ENNReal.ofReal (cL * logarithmicIndexRate r
          ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right (min_le_left _ _)
              (AlignmentWidthRates.logarithmicIndexRate_nonneg _ _ _)
    _ ≤ HaarQuarter.TheoremD.entropyNumber k K := hL

/-- Strict-index Kolmogorov width equivalence for finite theta above the
theta-two endpoint. The lower width follows from the certified entropy lower
bound and the proved upper width; the final conversion shifts legacy width
indices to the paper's `rank < k` convention. -/
theorem periodicBesov_width_equivalent_finite_theta
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {r : ℝ} (hr : 1/2 < r)
    {theta : ℝ≥0∞} (htheta : theta ≠ ⊤) (htheta2 : 2 < theta.toReal) :
    AlignmentOperatorStatements.twoSidedWidthRate
      (periodicLInfinityImage {f : RealPeriodic d |
        BesovUnitBall φ p r theta f})
      r ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) := by
  let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {f : RealPeriodic d |
      BesovUnitBall φ p r theta f}
  let J : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage {f : RealPeriodic d |
      BesovUnitBall smoothResolutionCutoff 2 r theta f}
  have htheta1 : 1 ≤ theta := by
    apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top htheta).1
    norm_num
    linarith
  have hTransfer :=
    BrownianSharp.AlignmentPeriodicCutoffYoung.cutoffBesovScaleTransfer_certified
      smoothResolutionCutoff φ d p (by exact_mod_cast (show (1 : ℝ≥0∞) ≤ p from
        le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) hp)) r
      (by linarith : 0 ≤ r) theta htheta1
  obtain ⟨cScale, hcScale, hScale⟩ := hTransfer
  let A : ℝ := cScale⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hKimage : K ⊆ scalarImage A J := by
    apply periodicImage_subset_scalarImage
      {f : RealPeriodic d | BesovUnitBall φ p r theta f}
      {f : RealPeriodic d | BesovUnitBall smoothResolutionCutoff 2 r theta f}
      A hA
    intro f hf
    have hscaled : BesovUnitBall smoothResolutionCutoff p r theta (cScale • f) :=
      hScale f hf
    have hmono := AlignmentPaperPeriodicBesov.besovUnitBall_mono_exponent
      smoothResolutionCutoff (q := (2 : ℝ≥0∞)) (p := p) hp r (cScale • f) hscaled
    simpa [A, inv_inv] using hmono
  have hwidthSmooth := actualBesov_width_upper_rate_certified hd hr htheta htheta2
  obtain ⟨CW, hCW, kW, hkW, hW⟩ := hwidthSmooth
  have hUpper : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      kolmogorovWidth K n ≤ ENNReal.ofReal (C * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) n) := by
    refine ⟨A * CW, mul_pos hA hCW, kW, ?_⟩
    intro n hn
    have hscaled := kolmogorovWidth_le_of_subset_scalarImage A
      (CW * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) n)
      hKimage n hA
      (mul_nonneg hCW.le (AlignmentWidthRates.logarithmicIndexRate_nonneg _ _ _))
      (hW n hn)
    convert hscaled using 1 <;> congr 1 <;> ring
  have hzeroCore := BrownianSharp.AlignmentAuditPeriodicBoundedness.nikolsky_linf_width_zero_le_of_exponent
    (d := d) (p := (2 : ℝ≥0∞)) (by norm_num) r hr
  have hJsubNik : J ⊆ periodicLInfinityImage
      {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall 2 r f} := by
    rintro y ⟨f, hf, rfl⟩
    have henergy : (∑' s : Fin d → ℕ,
        weightedBlockNorm smoothResolutionCutoff 2 r s f ^ theta.toReal) ≤ 1 := by
      simpa [AlignmentPeriodicCutoffClasses.BesovUnitBall, htheta] using hf
    have hclass : NikolskyUnitBall smoothResolutionCutoff 2 r f := by
      change ∀ s, weightedBlockNorm smoothResolutionCutoff 2 r s f ≤ 1
      intro s
      exact term_le_one_of_power_sum_le_one
        (fun s => weightedBlockNorm smoothResolutionCutoff 2 r s f)
        theta.toReal (by linarith) henergy s
    exact ⟨f, (AlignmentPeriodicCutoffClasses.NikolskyUnitBall_fixed
      2 r f).1 hclass, rfl⟩
  have hzeroJ := (kolmogorovWidth_mono_set hJsubNik 0).trans hzeroCore
  have hzero := kolmogorovWidth_le_of_subset_scalarImage A
    (AlignmentAuditPeriodicBoundedness.periodicNikolskyRadius d r)
    hKimage 0 hA
    (AlignmentAuditPeriodicBoundedness.periodicNikolsky_radius_nonneg
      (d := d) hr) hzeroJ
  have hpr : p.toReal⁻¹ < r := by
    by_cases htop : p = ⊤
    · simpa [htop] using (show 0 < r by linarith)
    · have hpR : (2 : ℝ) ≤ p.toReal := by
        have h := (ENNReal.toReal_le_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) htop).2 hp
        simpa only [ENNReal.toReal_ofNat] using h
      have hinv : p.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hpR
      exact hinv.trans_lt hr
  obtain ⟨cL, hcL, kL, hkL, hLowerData⟩ :=
    BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_mixed_entropy_certified
      φ d hd p (lt_of_lt_of_le (by norm_num) hp) r hpr theta htheta1
  have hLower : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ENNReal.ofReal (c * logarithmicIndexRate r
        ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) n) ≤
        HaarQuarter.TheoremD.entropyNumber n K := by
    refine ⟨cL, hcL, kL, ?_⟩
    intro n hn
    exact (hLowerData n hn).2.1
  have ha : 0 ≤ (r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2 := by
    have hinv : theta.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (le_of_lt htheta2)
    have hcoef : 0 ≤ r + 1 / 2 - theta.toReal⁻¹ := by linarith
    have hD : 0 ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  let R := A * AlignmentAuditPeriodicBoundedness.periodicNikolskyRadius d r
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg hA.le
      (AlignmentAuditPeriodicBoundedness.periodicNikolsky_radius_nonneg (d := d) hr)
  have hlegacy := AlignmentWidthRates.twoSidedWidthRate_of_entropy_lower_and_width_upper
    K r ((r + 1 / 2 - theta.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) R
    (by linarith) ha hR hzero hLower hUpper
  exact AlignmentScaledWidthRates.operator_width_rate_of_legacy K r _
    (by linarith) ha hlegacy

end BrownianSharp.AlignmentPaperBesovInterpolation

end
