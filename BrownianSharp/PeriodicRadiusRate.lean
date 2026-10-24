import BrownianSharp.PeriodicEntropy

/-! A numeric form of the native entropy scale conversion, separated from
covering budgets so confinement constants can be absorbed by an index multiple. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp

theorem periodicNativeRadius_ge_rate {d k : ℕ} (r β : ℝ)
    (hd : 2 ≤ d) (hk : 2 ≤ k) (hr : 0 < r) :
    periodicNativeRateConstant d r β * (k:ℝ)^(-r) *
      (Real.log (k:ℝ))^(r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ))) ≤
    periodicNativeRadius d (nativeEntropyCrossing d k (by omega)) r β := by
  let q := nativeEntropyCrossing d k (by omega)
  let p : ℝ := ((d - 1 : ℕ) : ℝ)
  let a : ℝ := 1 / 2 + β * p
  let α : ℝ := r * p + a
  let cD : ℝ := 1 / (Nat.factorial (d - 1) : ℝ)
  let R : ℝ := 4 * (d : ℝ) ^ 2
  let C : ℝ := nativeLogPowerConstant d α
  let c₀ : ℝ := periodicLayerPowerConstant d β
  let A : ℝ := periodicNativeRateConstant d r β
  let δ : ℝ≥0 := ⟨periodicNativeRadius d q r β,
    le_of_lt (periodicNativeRadius_pos (by
      exact (nativeEntropyCrossing_bracket hd hk).1))⟩
  have hbr := nativeEntropyCrossing_bracket hd hk
  have hq : 0 < (q : ℝ) := by exact_mod_cast hbr.1
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hR : 0 < R := by dsimp [R]; positivity
  have hcD : 0 < cD := by dsimp [cD]; positivity
  have hC : 0 < C := by dsimp [C, α, a, p]; exact nativeLogPowerConstant_pos hd _
  have hc₀ : 0 < c₀ := by dsimp [c₀]; exact periodicLayerPowerConstant_pos hd β
  have hA : 0 < A := by dsimp [A]; exact periodicNativeRateConstant_pos hd r β
  have hDlower : cD * (2 : ℝ) ^ (2 * (q : ℝ)) *
      (q : ℝ) ^ ((d - 1 : ℕ) : ℝ) ≤ nativeDimension d (2 * q) := by
    have h := nativeDimension_polynomial_lower hd hbr.1
    have hexp : 2 * (q : ℝ) = ((2 * q : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast]
    simpa [cD, q] using h
  have hDupper : nativeDimension d (2 * q) ≤ R * (k : ℝ) := by
    simpa [R, q, mul_comm] using hbr.2.2.2
  have hlogPower : (Real.log (k : ℝ)) ^ α ≤ C * (q : ℝ) ^ α := by
    simpa [C, α, a, p, q] using nativeEntropyCrossing_log_power hd hk α
  have hconst : A * (cD / R) ^ (-r) * C ≤ c₀ := by
    let T : ℝ := (cD / R) ^ (-r) * C
    have hden : 0 < T := by dsimp [T]; positivity
    have hAeq : A = c₀ / T := by
      dsimp [A, T, c₀, periodicNativeRateConstant, C, α, a, p, cD, R]
    calc
      A * (cD / R) ^ (-r) * C = (c₀ / T) * T := by
        rw [hAeq]
        dsimp [T]
        ring
      _ = c₀ := div_mul_cancel₀ _ hden.ne'
      _ ≤ c₀ := le_rfl
  have hscale : c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
      (q : ℝ) ^ a ≤ (δ : ℝ) := by
    have h := periodicLayerRadius_lower (r := r) (β := β) hd
      (by exact_mod_cast hbr.1 : 0 < q)
    change c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) * (q : ℝ) ^ a ≤
      periodicNativeRadius d q r β
    simpa [c₀, q, a, p, periodicNativeRadius] using h
  have hrate := periodic_layer_rate_transfer (d := d) (q := q) (k := k)
    (r := r) (a := a) (A := A) (R := R) (cD := cD) (C := C) (c₀ := c₀)
    (D := nativeDimension d (2 * q)) hq hkR hr hA hR hcD hC hc₀
    hDlower hDupper hlogPower hconst hscale
  have hδ : (δ:ℝ) = periodicNativeRadius d q r β := rfl
  rw [hδ] at hrate
  simpa [A, α, a, p, q] using hrate

end BrownianSharp
