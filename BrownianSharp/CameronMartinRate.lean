import BrownianSharp.CameronMartinEntropyLower
import BrownianSharp.PeriodicEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exponential confinement to the Cameron--Martin entropy rate

The result below carries the exact finite-grid confinement family as its only
analytic input.  All dimension crossing, Gaussian cutoff mass, radius
normalization, and dyadic entropy-index calculations are proved here.
-/

open MeasureTheory ProbabilityTheory HaarQuarter BrownianSharp
open scoped NNReal ENNReal

namespace BrownianSharp.CameronMartinRate

/-- The exponential cutoff mass is smaller than the dyadic cover budget for
all native dimensions at least `k`. -/
theorem dyadic_exponential_mass_lt
    {k s : ℕ} (hk : 2 ≤ k) {b D : ℝ} (hb : 0 < b)
    (hD : (s : ℝ) * (k : ℝ) ≤ D) (hfactor : 2 ≤ b * (s : ℝ)) :
    ((2 ^ (k - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-b * D)) <
      (3 / 4 : ℝ≥0∞) := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hpow : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
    calc
      (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ (by norm_num) hexp1 k
      _ = Real.exp (k : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hprev : ((2 ^ (k - 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    have hnat : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact_mod_cast hnat
  have hprod : ((2 ^ (k - 1) : ℕ) : ℝ) * Real.exp (-b * D) < (3 / 4 : ℝ) := by
    have hbkD : 2 * (k : ℝ) ≤ b * D := by
      calc
        2 * (k : ℝ) ≤ (b * (s : ℝ)) * (k : ℝ) := by nlinarith [hkR, hfactor]
        _ ≤ b * D := by
          calc
            (b * (s : ℝ)) * (k : ℝ) = b * ((s : ℝ) * (k : ℝ)) := by ring
            _ ≤ b * D := mul_le_mul_of_nonneg_left hD hb.le
    have hExpMono : Real.exp ((k : ℝ) + -b * D) ≤ Real.exp (-(k : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [hbkD])
    have hmul : ((2 ^ (k - 1) : ℕ) : ℝ) * Real.exp (-b * D) ≤
        Real.exp (k : ℝ) * Real.exp (-b * D) :=
      mul_le_mul_of_nonneg_right (hprev.trans hpow) (Real.exp_nonneg _)
    have hprod' : Real.exp (k : ℝ) * Real.exp (-b * D) =
        Real.exp ((k : ℝ) + -b * D) := by rw [← Real.exp_add]
    have hexp2 : (3 : ℝ) < Real.exp 2 := by
      have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
      linarith
    have hinv : Real.exp (-2) < (1 / 3 : ℝ) := by
      rw [Real.exp_neg]
      have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3) hexp2
      simpa [one_div] using h
    calc
      _ ≤ Real.exp (k : ℝ) * Real.exp (-b * D) := hmul
      _ = Real.exp ((k : ℝ) + -b * D) := hprod'
      _ ≤ Real.exp (-(k : ℝ)) := hExpMono
      _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      _ < (3 / 4 : ℝ) := by linarith
  have hcast : ((2 ^ (k - 1) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-b * D)) =
      ENNReal.ofReal (((2 ^ (k - 1) : ℕ) : ℝ) * Real.exp (-b * D)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [hcast]
  have hthree : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  rw [← hthree]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hprod

/-- Uniform dyadic entropy lower rate on the actual restricted-cube
Cameron--Martin set, assuming only the displayed centered finite-grid
confinement family.  The probability bound is the explicit `exp(-2D)` form;
the theorem proves that it suffices for every large dyadic entropy index. -/
theorem native_entropy_rate_of_exponential_confinement
    {d : ℕ} (hd : 2 ≤ d) (b : ℝ) (hb : 0 < b) (η : ℝ) (hη : 0 < η)
    (M : ℕ → ℕ)
    (t : ∀ q : ℕ, Fin (M q) → BrownianCubeAnchor d)
    (hconf : ∀ q : ℕ, 0 < q →
      let D : ℝ := (Fintype.card (LayerIndex d (2 * q)) : ℝ)
      let δ : ℝ := periodicNativeRadius d q (1 / 2 : ℝ) (1 / 2 : ℝ)
      (Measure.pi (fun _ : Fin (Fintype.card (LayerIndex d (2 * q))) =>
        ProbabilityTheory.gaussianReal 0 1))
        {x | ‖rowEvaluation
          (CameronMartinCover.nativeGridMatrix
            (Fintype.equivFin (LayerIndex d (2 * q))).symm (t q)) x‖ ≤
            η * periodicNativeRadius d q (1 / 2 : ℝ) (1 / 2 : ℝ)} ≤ ENNReal.ofReal (Real.exp (-b * D))) :
    ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal
        ((η / (2 * (max 1 ⌈(2 / b)⌉₊ : ℝ))) * periodicNativeRateConstant d 1 0 *
          (k : ℝ) ^ (-1 : ℝ) *
          (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2)) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) := by
  intro k hk
  let s : ℕ := max 1 ⌈(2 / b)⌉₊
  have hsNat : 1 ≤ s := by dsimp [s]; omega
  have hsceil : (⌈(2 / b)⌉₊ : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast (Nat.le_max_right 1 ⌈(2 / b)⌉₊)
  have hlarge : 2 / b ≤ (s : ℝ) := (Nat.le_ceil _).trans hsceil
  have hs : 2 ≤ b * (s : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hb).1 hlarge
  let k₂ : ℕ := s * k
  have hk₂ : 2 ≤ k₂ := by
    calc
      2 ≤ k := hk
      _ = 1 * k := by simp
      _ ≤ s * k := Nat.mul_le_mul_right k hsNat
  let q : ℕ := nativeEntropyCrossing d k₂ (by omega)
  have hbr := nativeEntropyCrossing_bracket hd hk₂
  have hq : 0 < q := by simpa [q, k₂] using hbr.1
  have hcardpos : 0 < Fintype.card (LayerIndex d (2 * q)) := by
    rw [layerIndex_card d (2 * q) (by omega)]
    exact Nat.mul_pos (by positivity) (Nat.choose_pos (by omega))
  letI : Nonempty (LayerIndex d (2 * q)) := Fintype.card_pos_iff.mp hcardpos
  have hDidentity : (Fintype.card (LayerIndex d (2 * q)) : ℝ) =
      nativeDimension d (2 * q) := by
    rw [layerIndex_card d (2 * q) (by omega)]
    simp [nativeDimension, hyperbolicCount]
  have hD : (k₂ : ℝ) ≤ (Fintype.card (LayerIndex d (2 * q)) : ℝ) := by
    rw [hDidentity]
    simpa [q, k₂] using hbr.2.2.1
  have hDmass : (s : ℝ) * (k : ℝ) ≤ (Fintype.card (LayerIndex d (2 * q)) : ℝ) := by
    have hk₂cast : (k₂ : ℝ) = (s : ℝ) * (k : ℝ) := by dsimp [k₂]; norm_cast
    rw [← hk₂cast]
    exact hD
  have hmass := dyadic_exponential_mass_lt hk hb hDmass hs
  let e : Fin (Fintype.card (LayerIndex d (2 * q))) ≃ LayerIndex d (2 * q) :=
    (Fintype.equivFin (LayerIndex d (2 * q))).symm
  let D : ℝ := (Fintype.card (LayerIndex d (2 * q)) : ℝ)
  let δ : ℝ := (η / 2) * periodicNativeRadius d q 1 0
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact mul_pos (by positivity) (periodicNativeRadius_pos hq)
  have hDpos : 0 < D := by dsimp [D]; exact_mod_cast hcardpos
  have hεpos : 0 < η * periodicNativeRadius d q (1 / 2 : ℝ) (1 / 2 : ℝ) :=
    mul_pos hη (periodicNativeRadius_pos hq)
  have hconfq := hconf q hq
  have hcover := CameronMartinCover.nativeCameronMartin_externalCoveringNumber_gt
    e (t q) (η * periodicNativeRadius d q (1 / 2 : ℝ) (1 / 2 : ℝ))
    hεpos (ENNReal.ofReal (Real.exp (-b * (Fintype.card (LayerIndex d (2 * q)) : ℝ))))
    (2 ^ (k - 1)) hconfq hmass
  have hcover' : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber
        (⟨δ,
          le_of_lt hδpos⟩ : ℝ≥0)
        (CameronMartin.KdUnitCube d) := by
    have hradius :
        (⟨(η * periodicNativeRadius d q (1 / 2 : ℝ) (1 / 2 : ℝ)) /
          (2 * Real.sqrt (Fintype.card (LayerIndex d (2 * q)) : ℝ)), le_of_lt (div_pos hεpos (by positivity))⟩ : ℝ≥0) =
        ⟨δ, le_of_lt hδpos⟩ := by
      apply Subtype.ext
      change (η * periodicNativeRadius d q (1 / 2 : ℝ) (1 / 2 : ℝ)) /
          (2 * Real.sqrt (Fintype.card (LayerIndex d (2 * q)) : ℝ)) =
        (η / 2) * periodicNativeRadius d q 1 0
      -- The layer cardinal is `2^(2q)` times the hyperbolic shell count.
      have hcard : (Fintype.card (LayerIndex d (2 * q)) : ℝ) =
          (2 : ℝ) ^ (2 * q) * hyperbolicCount d (2 * q) := by
        rw [layerIndex_card d (2 * q) (by omega)]
        simp [hyperbolicCount]
      rw [hcard]
      unfold periodicNativeRadius
      have hroot : Real.sqrt ((2 : ℝ) ^ (2 * q) * hyperbolicCount d (2 * q)) =
          (2 : ℝ) ^ q * Real.sqrt (hyperbolicCount d (2 * q)) := by
        rw [Real.sqrt_mul (by positivity)]
        have hp : (2 : ℝ) ^ (2 * q) = ((2 : ℝ) ^ q) ^ 2 := by
          rw [← pow_mul]
          congr 1
          omega
        rw [hp, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      rw [hroot]
      rw [show -2 * (1 / 2 : ℝ) * (q : ℝ) = -(q : ℝ) by ring]
      rw [show -2 * (1 : ℝ) * (q : ℝ) = -2 * (q : ℝ) by ring]
      rw [Real.sqrt_eq_rpow]
      rw [show (hyperbolicCount d (2 * q) : ℝ) ^ (0 : ℝ) = 1 by simp]
      have hnatpow : (2 : ℝ) ^ q = (2 : ℝ) ^ (q : ℝ) := by
        rw [Real.rpow_natCast]
      rw [hnatpow]
      have hSpos : 0 < hyperbolicCount d (2 * q) := by
        unfold hyperbolicCount
        exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ 2 * q + d - 1)
      rw [Real.sqrt_eq_rpow]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hSpos)]
      have hpowright : (2 : ℝ) ^ (q : ℝ) * (2 : ℝ) ^ (-((q : ℝ) * 2)) =
          (2 : ℝ) ^ (-(q : ℝ)) := by
        rw [show -((q : ℝ) * 2) = -2 * (q : ℝ) by ring]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      exact hpowright.symm

    rw [hradius] at hcover
    exact_mod_cast hcover
  let p : ℝ := ((d - 1 : ℕ) : ℝ)
  let α : ℝ := p + (1 / 2 : ℝ)
  let a : ℝ := (1 / 2 : ℝ)
  let cD : ℝ := 1 / (Nat.factorial (d - 1) : ℝ)
  let R : ℝ := 4 * (d : ℝ) ^ 2
  let C : ℝ := nativeLogPowerConstant d α
  let c₀ : ℝ := (η / 2) * periodicLayerPowerConstant d 0
  let A : ℝ := (η / 2) * periodicNativeRateConstant d 1 0
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hk₂R : 1 ≤ (k₂ : ℝ) := by exact_mod_cast (show 1 ≤ k₂ by omega)
  have hr : 0 < (1 : ℝ) := by norm_num
  have hA : 0 < A := by
    dsimp [A]
    apply mul_pos
    · exact div_pos hη (by positivity)
    · exact periodicNativeRateConstant_pos hd 1 0
  have hR : 0 < R := by dsimp [R]; positivity
  have hcD : 0 < cD := by dsimp [cD]; positivity
  have hC : 0 < C := by dsimp [C]; exact nativeLogPowerConstant_pos hd _
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact mul_pos (by positivity) (periodicLayerPowerConstant_pos hd 0)
  have hDlower : cD * (2 : ℝ) ^ (2 * (q : ℝ)) *
      (q : ℝ) ^ p ≤ nativeDimension d (2 * q) := by
    have h := nativeDimension_polynomial_lower hd hq
    rw [show (2 : ℝ) * (q : ℝ) = ((2 * q : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_natCast]
    simpa [cD, p, q] using h
  have hDupper : nativeDimension d (2 * q) ≤ R * (k₂ : ℝ) := by
    simpa [R, q, k₂] using hbr.2.2.2
  have hk_le_k₂ : k ≤ k₂ := by
    calc
      k = 1 * k := by simp
      _ ≤ s * k := Nat.mul_le_mul_right k hsNat
  have hlogPower : (Real.log (k₂ : ℝ)) ^ α ≤ C * (q : ℝ) ^ α := by
    simpa [C, α, q, k₂] using nativeEntropyCrossing_log_power hd hk₂ α
  have hconst : A * (cD / R) ^ (-1 : ℝ) * C ≤ c₀ := by
    have hden : 0 < (cD / R) ^ (-1 : ℝ) * C := by positivity
    have hAeq : A = c₀ / ((cD / R) ^ (-1 : ℝ) * C) := by
      simp [A, c₀, cD, R, C, periodicNativeRateConstant, periodicLayerPowerConstant,
        nativeLogPowerConstant, α, p, a, mul_assoc]
      field_simp
    calc
      A * (cD / R) ^ (-1 : ℝ) * C =
          (c₀ / ((cD / R) ^ (-1 : ℝ) * C)) *
            ((cD / R) ^ (-1 : ℝ) * C) := by
              rw [hAeq]
              field_simp [hden.ne']
      _ ≤ c₀ := le_of_eq (div_mul_cancel₀ c₀ hden.ne')
  have hscale : c₀ * (2 : ℝ) ^ (-2 * (1 : ℝ) * (q : ℝ)) * (q : ℝ) ^ a ≤ δ := by
    have h := periodicLayerRadius_lower (d := d) (q := q) (r := (1 : ℝ))
      (β := (0 : ℝ)) hd hq
    have hm : 0 ≤ η / 2 := by positivity
    have hm' := mul_le_mul_of_nonneg_left h hm
    calc
      c₀ * (2 : ℝ) ^ (-2 * (1 : ℝ) * (q : ℝ)) * (q : ℝ) ^ a =
          (η / 2) * (periodicLayerPowerConstant d 0 * (2 : ℝ) ^ (-2 * (1 : ℝ) * (q : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ)) := by
            dsimp [c₀, a]
            ring
      _ ≤ δ := by simpa [δ, periodicNativeRadius] using hm'
  have hrate := periodic_layer_rate_transfer (d := d) (q := q) (k := k₂)
    (r := (1 : ℝ)) (a := a) (A := A) (R := R) (cD := cD) (C := C)
    (c₀ := c₀) (D := nativeDimension d (2 * q)) (δ := δ)
    hqR hk₂R hr hA hR hcD hC hc₀ hDlower hDupper
    (by simpa [α, p, a] using hlogPower) hconst hscale
  have hcoverRate := BrownianSharp.periodicEntropyNumber_ge_of_covering_gt k
    (CameronMartin.KdUnitCube d)
    ⟨δ, le_of_lt hδpos⟩ hcover'
  have hα : (1 : ℝ) * p + a = α := by
    dsimp [a, α]
    ring
  have hk₂cast : (k₂ : ℝ) = (s : ℝ) * (k : ℝ) := by dsimp [k₂]; norm_cast
  have hindex : (k₂ : ℝ) ^ (-1 : ℝ) = (s : ℝ) ^ (-1 : ℝ) * (k : ℝ) ^ (-1 : ℝ) := by
    rw [hk₂cast, Real.mul_rpow (by positivity) (by positivity)]
  have hlogmono : Real.log (k : ℝ) ≤ Real.log (k₂ : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < k by omega))
    exact_mod_cast hk_le_k₂
  have hαpos : 0 ≤ α := by dsimp [α, p]; nlinarith [hd]
  have hlogpowerlower : (Real.log (k : ℝ)) ^ α ≤ (Real.log (k₂ : ℝ)) ^ α := by
    apply Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))) hlogmono hαpos
  have hrate' : (A * (s : ℝ) ^ (-1 : ℝ)) * (k : ℝ) ^ (-1 : ℝ) *
      (Real.log (k : ℝ)) ^ α ≤ δ := by
    calc
      (A * (s : ℝ) ^ (-1 : ℝ)) * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ α =
          A * (k₂ : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ α := by rw [hindex]; ring
      _ ≤ A * (k₂ : ℝ) ^ (-1 : ℝ) * (Real.log (k₂ : ℝ)) ^ α :=
        mul_le_mul_of_nonneg_left hlogpowerlower (by positivity)
      _ ≤ δ := by
        rw [hα] at hrate
        exact hrate
  have hrateENN : ENNReal.ofReal ((A * (s : ℝ) ^ (-1 : ℝ)) * (k : ℝ) ^ (-1 : ℝ) *
      (Real.log (k : ℝ)) ^ α) ≤
      ENNReal.ofNNReal ⟨δ, le_of_lt hδpos⟩ := by
    have hnonneg : 0 ≤ (A * (s : ℝ) ^ (-1 : ℝ)) * (k : ℝ) ^ (-1 : ℝ) *
        (Real.log (k : ℝ)) ^ α := by positivity
    rw [ENNReal.ofReal_eq_coe_nnreal hnonneg]
    apply ENNReal.coe_le_coe.mpr
    exact_mod_cast hrate'
  have hfinal := hrateENN.trans hcoverRate
  have hαtarget : α = (d : ℝ) - 1 / 2 := by
    dsimp [α, p]
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ d)
    rw [hcast]
    ring
  have hsreal : (s : ℝ) = (max 1 ⌈(2 / b)⌉₊ : ℝ) := by simp [s]
  rw [hsreal, hαtarget] at hfinal
  have hcoeff : (η / 2) * periodicNativeRateConstant d 1 0 *
      (max 1 ⌈(2 / b)⌉₊ : ℝ) ^ (-1 : ℝ) =
      (η / (2 * (max 1 ⌈(2 / b)⌉₊ : ℝ))) * periodicNativeRateConstant d 1 0 := by
    rw [Real.rpow_neg_one]
    field_simp
  simp only [A] at hfinal
  rw [hcoeff] at hfinal
  exact hfinal

/-- Eventual form of the arbitrary-exponent confinement rate.  Its sole
analytic input is the actual PV-scale finite-grid confinement radius. -/
theorem native_entropy_rate_eventually_of_exponential_confinement
    {d : ℕ} (hd : 2 ≤ d) (b : ℝ) (hb : 0 < b) (η : ℝ) (hη : 0 < η)
    (M : ℕ → ℕ)
    (t : ∀ q : ℕ, Fin (M q) → BrownianCubeAnchor d)
    (hconf : ∀ q : ℕ, 0 < q →
      let D : ℝ := (Fintype.card (LayerIndex d (2 * q)) : ℝ)
      (Measure.pi
        (fun _ : Fin (Fintype.card (LayerIndex d (2 * q))) =>
          ProbabilityTheory.gaussianReal 0 1))
        {x | ‖rowEvaluation
          (CameronMartinCover.nativeGridMatrix
            (Fintype.equivFin (LayerIndex d (2 * q))).symm (t q)) x‖ ≤
            η * periodicNativeRadius d q (1 / 2 : ℝ) (1 / 2 : ℝ)} ≤
          ENNReal.ofReal (Real.exp (-b * D))) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal
        ((η / (2 * (max 1 ⌈(2 / b)⌉₊ : ℝ))) *
          periodicNativeRateConstant d 1 0 * (k : ℝ) ^ (-1 : ℝ) *
          (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2)) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) := by
  refine ⟨2, ?_⟩
  intro k hk
  exact native_entropy_rate_of_exponential_confinement
    hd b hb η hη M t hconf k hk


end BrownianSharp.CameronMartinRate
