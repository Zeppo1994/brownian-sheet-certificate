import BrownianSharp.AlignmentPaperGenericSmoothBumpBesov
import BrownianSharp.AlignmentPaperMeanZeroBump

/-! Unconditional all-theta synthesis for an arbitrary compactly supported
smooth bump. This selects all kernel, derivative, order, and amplitude
constants internally; callers provide only the bump and coefficient box. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperGenericSmoothBumpBesov
open BrownianSharp
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus
open BrownianSharp.ScalarKernelL1

local instance genericTorusProbability (d : ℕ) :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  rw [BrownianSharp.unitAddTorus_volume_eq_productHaar]
  infer_instance

theorem generic_weightedBlockNorm_mono_spatial {d : ℕ}
    {p : ℝ≥0∞} (r : ℝ) (s : Fin d → ℕ) (f : RealPeriodic d) :
    SmoothResolution.weightedBlockNorm p r s f ≤
      SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r s f := by
  unfold SmoothResolution.weightedBlockNorm
  gcongr
  exact eLpNorm_le_eLpNorm_of_exponent_le le_top

theorem generic_besovUnitBall_mono_spatial {d : ℕ}
    {p : ℝ≥0∞} (r : ℝ) (theta : ℝ≥0∞) (f : RealPeriodic d)
    (hf : SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta f) :
    SmoothResolution.BesovUnitBall p r theta f := by
  unfold SmoothResolution.BesovUnitBall at *
  split_ifs at * with htheta
  · intro s
    exact (generic_weightedBlockNorm_mono_spatial r s f).trans (hf s)
  · apply le_trans _ hf
    apply ENNReal.tsum_le_tsum
    intro s
    exact ENNReal.rpow_le_rpow
      (generic_weightedBlockNorm_mono_spatial r s f) ENNReal.toReal_nonneg

theorem generic_exists_scaled_box_synthesis_Besov
    {d : ℕ} (hd : 2 ≤ d) (ψ : SmoothCompactBump)
    (M r : ℝ) (theta : ℝ≥0∞)
    (hM : 0 < M) (hr : 0 < r) (hθ : 1 ≤ theta) :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, ∀ x : LayerIndex d n → ℝ,
      (∀ j, |x j| ≤ M) →
      ∃ amp : ℝ, 0 < amp ∧ amp ≤ 1 ∧
        amp • genericPeriodicSynthesisLinear ψ x ∈
          {f : RealPeriodic d | SmoothResolution.BesovUnitBall
            (⊤ : ℝ≥0∞) r theta f} ∧
        c * (2:ℝ)^(-r*(n:ℝ)) *
          (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) ≤ amp := by
  classical
  obtain ⟨q, hq⟩ := exists_nat_gt (r+1)
  let K : ℕ := 2*q
  have hqpos : 0 < q := by
    have : (0:ℝ) < (q:ℝ) := by linarith
    exact_mod_cast this
  have hK : Even K := ⟨q, by dsimp [K]; omega⟩
  have hKpos : 0 < K := by dsimp [K]; omega
  have hrK : r < (K:ℝ) := by
    have hqr : r < (q:ℝ) := by linarith
    have hKcast : (K:ℝ) = (2:ℝ)*(q:ℝ) := by simp [K]
    rw [hKcast]
    nlinarith
  obtain ⟨Lscalar, hLs0, hscalar0⟩ := exists_scalarBlockKernel_uniform_L1_bound
  obtain ⟨Lprofile, hLp0, hprofile0⟩ :=
    exists_inverseMultiplierKernel_uniform_L1_bound hK
  obtain ⟨Czero, hCzero, hderiv0⟩ := exists_derivative_envelope ψ 0
  obtain ⟨CK, hCK, hderivK⟩ := exists_derivative_envelope ψ K
  let Ls : ℝ := Lscalar+1
  let Lp : ℝ := Lprofile+1
  let C0 : ℝ := Czero+1
  let CK' : ℝ := CK+1
  have hLs : 0 < Ls := by dsimp [Ls]; linarith
  have hLp : 0 < Lp := by dsimp [Lp]; linarith
  have hC0 : 0 < C0 := by dsimp [C0]; linarith
  have hCK' : 0 < CK' := by dsimp [CK']; linarith
  have hscalar : ∀ q : ℕ,
      (∫ z : UnitAddCircle, ‖scalarBlockKernel q z‖
        ∂AddCircle.haarAddCircle) ≤ Ls := by
    intro q
    dsimp [Ls]
    linarith [hscalar0 q]
  have hprofile : ∀ q : ℕ, 0 < q →
      (∫ z : UnitAddCircle, ‖inverseMultiplierKernel q K z‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lp := by
    intro q hqpos'
    have hh := hprofile0 q hqpos'
    dsimp [Lp]
    calc
      _ ≤ ‖inverseProfileScale q K‖ * Lprofile := hh
      _ ≤ ‖inverseProfileScale q K‖ * (Lprofile+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  have hderiv0' : ∀ y : ℝ, |iteratedDeriv 0 ψ.atom y| ≤ C0 := by
    intro y
    dsimp [C0]
    linarith [hderiv0 y]
  have hderivK' : ∀ y : ℝ, |iteratedDeriv K ψ.atom y| ≤ CK' := by
    intro y
    dsimp [CK']
    linarith [hderivK y]
  let qlowR : ℝ := (2:ℝ)^(-r)
  let qhighR : ℝ := (2:ℝ)^(-((K:ℝ)-r))
  let H : ℝ := ((1-qlowR)⁻¹ + qhighR*(1-qhighR)⁻¹)^d
  let D : ℝ := max (Ls*C0) (Lp*CK')
  have hrK' : r < (K:ℝ) := hrK
  have hlow : qlowR < 1 := by
    dsimp [qlowR]
    exact (real_dyadic_profile_bases_lt_one hr hrK').1
  have hhigh : qhighR < 1 := by
    dsimp [qhighR]
    exact (real_dyadic_profile_bases_lt_one hr hrK').2
  have hH : 0 < H := by
    dsimp [H]
    have hlow0 : 0 ≤ qlowR := by positivity
    have hhigh0 : 0 ≤ qhighR := by positivity
    have hlowden : 0 < 1-qlowR := by linarith
    have hhighden : 0 < 1-qhighR := by linarith
    positivity
  let c : ℝ := (1+M*D^d*H)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro n x hcoeff
  let N : ℕ := Fintype.card (Shape d n)
  let B0 : ℝ := M*D^d*(2:ℝ)^(r*(n:ℝ))
  let amp : ℝ := endpointBesovScale B0 H N theta.toReal
  have hN : 1 ≤ N := by
    dsimp [N]
    rw [shape_card d n (by omega)]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hD : 0 < D := by dsimp [D]; positivity
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hp0 : 0 ≤ theta.toReal := ENNReal.toReal_nonneg
  have hamp : 0 < amp := by dsimp [amp]; exact endpointBesovScale_pos hB0 hH hN hp0
  have hamp_le : amp ≤ 1 := by
    have hden : 1 ≤ 1+B0*H*(N:ℝ)^(1/theta.toReal) := by
      have hpow : 0 ≤ (N:ℝ)^(1/theta.toReal) := Real.rpow_nonneg (by positivity) _
      have hmul : 0 ≤ B0*H*(N:ℝ)^(1/theta.toReal) := by positivity
      linarith
    dsimp [amp, endpointBesovScale]
    exact (inv_le_one₀ (by positivity)).2 hden
  have hXlower : 1 ≤ (2:ℝ)^(r*(n:ℝ)) * (N:ℝ)^(1/theta.toReal) := by
    have htwo : 1 ≤ (2:ℝ)^(r*(n:ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hr.le (by positivity))
    have hNpow : 1 ≤ (N:ℝ)^(1/theta.toReal) :=
      Real.one_le_rpow (by exact_mod_cast hN) (div_nonneg (by norm_num) hp0)
    calc
      1 ≤ (2:ℝ)^(r*(n:ℝ)) := htwo
      _ = (2:ℝ)^(r*(n:ℝ))*1 := by ring
      _ ≤ (2:ℝ)^(r*(n:ℝ))*(N:ℝ)^(1/theta.toReal) :=
        mul_le_mul_of_nonneg_left hNpow (by positivity)
  have hamp_lower : c*(2:ℝ)^(-r*(n:ℝ))*(N:ℝ)^(-(1/theta.toReal)) ≤ amp := by
    have hden : 0 < 1+B0*H*(N:ℝ)^(1/theta.toReal) := by positivity
    have hdenUpper : 1+B0*H*(N:ℝ)^(1/theta.toReal) ≤
        (1+M*D^d*H)*((2:ℝ)^(r*(n:ℝ))*(N:ℝ)^(1/theta.toReal)) := by
      have hbase : 0 ≤ M*D^d*H := by positivity
      rw [show B0 = M*D^d*(2:ℝ)^(r*(n:ℝ)) by rfl]
      nlinarith [mul_nonneg hbase (sub_nonneg.mpr hXlower)]
    have hinv := one_div_le_one_div_of_le hden hdenUpper
    have hpow : ((2:ℝ)^(r*(n:ℝ))*(N:ℝ)^(1/theta.toReal))⁻¹ =
        (2:ℝ)^(-r*(n:ℝ))*(N:ℝ)^(-(1/theta.toReal)) := by
      rw [mul_inv, ← Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)),
        ← Real.rpow_neg (by positivity : 0 ≤ (N:ℝ))]
      congr 2 <;> ring
    have hleft : ((1+M*D^d*H)*
        ((2:ℝ)^(r*(n:ℝ))*(N:ℝ)^(1/theta.toReal)))⁻¹ =
        c*(2:ℝ)^(-r*(n:ℝ))*(N:ℝ)^(-(1/theta.toReal)) := by
      rw [mul_inv, hpow]
      dsimp [c]
      ring
    rw [← hleft]
    simpa [amp, endpointBesovScale, B0, N, mul_assoc, mul_left_comm, mul_comm] using hinv
  have hAmass :
      (((1-ENNReal.ofReal qlowR)⁻¹ +
        ENNReal.ofReal qhighR*(1-ENNReal.ofReal qhighR)⁻¹)^d) = ENNReal.ofReal H := by
    simpa [qlowR, qhighR, H] using
      endpoint_profileMassENNReal_eq_ofReal (d:=d) hr hrK'
  have hbudget : if theta = ⊤ then
      ENNReal.ofReal (amp*B0)*ENNReal.ofReal H ≤ 1 else
      ENNReal.ofReal (amp*B0)^theta.toReal * ENNReal.ofReal H^theta.toReal *
        (N:ℝ≥0∞) ≤ 1 := by
    by_cases htop : theta = ⊤
    · simp only [htop, ↓reduceIte]
      have hreal := endpointBesovScale_sup_budget hB0 hH hN hp0
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ amp*B0)]
      exact ENNReal.ofReal_le_one.mpr hreal
    · simp only [htop, ↓reduceIte]
      have hp : 1 ≤ theta.toReal := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top htop).2 hθ
      have hreal := endpointBesovScale_power_budget hB0 hH hN hp
      have hconvert :
          ENNReal.ofReal (amp*B0)^theta.toReal * ENNReal.ofReal H^theta.toReal *
            (N:ℝ≥0∞) = ENNReal.ofReal ((amp*B0*H)^theta.toReal*(N:ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
          ENNReal.ofReal_rpow_of_nonneg hH.le (by linarith)]
        have hNcast : (N:ℝ≥0∞) = ENNReal.ofReal (N:ℝ) := by norm_cast
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (amp*B0)^theta.toReal),
          hNcast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow (by positivity) hH.le]
      rw [hconvert]
      exact ENNReal.ofReal_le_one.mpr hreal
  have hscaled : ∀ j, |(amp • x) j| ≤ amp*M := by
    intro j
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hamp]
    exact mul_le_mul_of_nonneg_left (hcoeff j) hamp.le
  have hbudgetScaled : if theta = ⊤ then
      ENNReal.ofReal (amp*M*D^d*(2:ℝ)^(r*(n:ℝ))) *
        (((1-ENNReal.ofReal qlowR)⁻¹ + ENNReal.ofReal qhighR *
          (1-ENNReal.ofReal qhighR)⁻¹)^d) ≤ 1 else
      ENNReal.ofReal (amp*M*D^d*(2:ℝ)^(r*(n:ℝ)))^theta.toReal *
        (((1-ENNReal.ofReal qlowR)⁻¹ + ENNReal.ofReal qhighR *
          (1-ENNReal.ofReal qhighR)⁻¹)^d)^theta.toReal * (N:ℝ≥0∞) ≤ 1 := by
    have hcoef : amp*M*D^d*(2:ℝ)^(r*(n:ℝ)) = amp*B0 := by
      dsimp [B0]
      ring
    by_cases htop : theta = ⊤
    · simp only [htop, ↓reduceIte]
      have hb := hbudget
      simp only [htop, ↓reduceIte] at hb
      rw [hAmass, hcoef]
      exact hb
    · simp only [htop, ↓reduceIte]
      have hb := hbudget
      simp only [htop, ↓reduceIte] at hb
      rw [hAmass, hcoef]
      exact hb
  have hclass := genericPeriodicBesov_of_boundedCoefficients
    ψ (fun j => amp*x j) (amp*M) r theta K Ls Lp C0 CK'
    (mul_nonneg hamp.le hM.le) hscaled hr hK hKpos hrK hθ
    hLs.le hLp.le hC0.le hCK'.le hscalar hprofile hderiv0' hderivK'
    (by simpa [N, qlowR, qhighR] using hbudgetScaled)
  have hmap : genericPeriodicSynthesisLinear ψ (fun j => amp*x j) =
      amp • genericPeriodicSynthesisLinear ψ x := by
    exact (genericPeriodicSynthesisLinear (d:=d) (n:=n) ψ).map_smul amp x
  refine ⟨amp,hamp,hamp_le,?_,?_⟩
  · rw [← hmap]
    exact hclass
  · simpa [N] using hamp_lower

theorem generic_exists_scaled_box_synthesis_Besov_spatial
    {d : ℕ} (hd : 2 ≤ d) (ψ : SmoothCompactBump)
    (M r : ℝ) (theta p : ℝ≥0∞)
    (hM : 0 < M) (hr : 0 < r) (hθ : 1 ≤ theta)
    (hp : 1 ≤ p) :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, ∀ x : LayerIndex d n → ℝ,
      (∀ j, |x j| ≤ M) →
      ∃ amp : ℝ, 0 < amp ∧ amp ≤ 1 ∧
        amp • genericPeriodicSynthesisLinear ψ x ∈
          {f : RealPeriodic d | SmoothResolution.BesovUnitBall p r theta f} ∧
        c * (2:ℝ)^(-r*(n:ℝ)) *
          (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) ≤ amp := by
  obtain ⟨c,hc,hall⟩ :=
    generic_exists_scaled_box_synthesis_Besov hd ψ M r theta hM hr hθ
  refine ⟨c,hc,?_⟩
  intro n x hcoeff
  obtain ⟨amp,hamp,hamp_le,hball,hscale⟩ := hall n x hcoeff
  exact ⟨amp,hamp,hamp_le,
    generic_besovUnitBall_mono_spatial r theta _ hball,hscale⟩

/-- The mean-zero smooth bump from the manuscript belongs to the actual
generic periodized-bump class used by the uniform synthesis theorem. -/
theorem exists_meanZero_generic_smooth_bump_endpoint
    {d : ℕ} (hd : 2 ≤ d) (M r : ℝ) (theta : ℝ≥0∞)
    (hM : 0 < M) (hr : 0 < r) (hθ : 1 ≤ theta) :
    ∃ b : AlignmentPaperContinuumGenericBump.AdmissibleBump,
      ∃ ψ : SmoothCompactBump, ψ.atom = b.atom ∧
      (∫ x in (0:ℝ)..1, ψ.atom x) = 0 ∧
      (∃ t, ψ.atom t ≠ 0) ∧ (∀ t, |ψ.atom t| ≤ 1) ∧
      ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, ∀ x : LayerIndex d n → ℝ,
        (∀ j, |x j| ≤ M) →
        ∃ amp : ℝ, 0 < amp ∧ amp ≤ 1 ∧
          amp • genericPeriodicSynthesisLinear ψ x ∈
            {f : RealPeriodic d | SmoothResolution.BesovUnitBall
              (⊤ : ℝ≥0∞) r theta f} ∧
          c * (2:ℝ)^(-r*(n:ℝ)) *
            (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) ≤ amp := by
  obtain ⟨b,hsm,hsupp,hmean⟩ :=
    BrownianSharp.AlignmentPaperMeanZeroBump.exists_meanZero_smooth_admissibleBump
  let ψ : SmoothCompactBump := {
    atom := b.atom
    smooth := hsm
    tsupport_subset := by
      intro x hx
      rcases hsupp hx with ⟨hlo,hhi⟩
      constructor
      · have hpos : (0:ℝ) < 1/8 := by norm_num
        linarith
      · have hlt : (7/8:ℝ) < 1 := by norm_num
        linarith }
  obtain ⟨c,hc,hall⟩ :=
    generic_exists_scaled_box_synthesis_Besov hd ψ M r theta hM hr hθ
  exact ⟨b,ψ,rfl,hmean,b.nonzero,b.abs_le_one,c,hc,hall⟩

end BrownianSharp.AlignmentPaperGenericSmoothBumpBesov
