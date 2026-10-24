import BrownianSharp.PeriodicCoverRate
import BrownianSharp.SharpCertified

/-! Numerical confinement budgets for the actual periodic Gaussian layers. -/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
namespace BrownianSharp

theorem nativeEntropyCrossing_multiple_eventually_ge {d s : ℕ}
    (hd : 2 ≤ d) (hs : 1 ≤ s) (N : ℕ) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      N ≤ nativeEntropyCrossing d (s*k) (by omega) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL := nativeLogScaleLower_pos hd
  have hev : ∀ᶠ k : ℕ in atTop,
      N ≤ nativeEntropyCrossing d (s*k) (by omega) := by
    filter_upwards [hlog.eventually_ge_atTop (nativeLogScaleLower d*((N:ℝ)+1)),
      eventually_ge_atTop 2] with k hlarge hk
    have hsk : 2 ≤ s*k := by nlinarith
    have hcross := (nativeEntropyCrossing_log_bounds hd hsk).1
    have hlogle : Real.log (k:ℝ) ≤ Real.log ((s*k:ℕ):ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0<k))
      have hsR : (1:ℝ)≤(s:ℝ) := by exact_mod_cast hs
      push_cast
      nlinarith
    have hNq : (N:ℝ) ≤ (nativeEntropyCrossing d (s*k) (by omega):ℝ) := by
      change Real.log ((s*k:ℕ):ℝ) ≤ nativeLogScaleLower d *
        (nativeEntropyCrossing d (s*k) (by omega):ℝ) at hcross
      nlinarith
    exact_mod_cast hNq
  obtain ⟨k₀,hk₀⟩ := eventually_atTop.1 hev
  exact ⟨max 2 k₀, le_max_left _ _, fun k hk => hk₀ k ((le_max_right _ _).trans hk)⟩

/-- The 2^-S admissible event budget is enough: the shell cardinality is
absorbed by the exponential native dimension. -/
theorem dyadic_exponential_mass_lt_shape_cutoff
    {k S s : ℕ} (hk : 2 ≤ k) {b D : ℝ} (hb : 0 < b)
    (hbs : 2 ≤ b*(s:ℝ))
    (hDk : (2*(s:ℝ))*(k:ℝ) ≤ D)
    (hDS : (2*(s:ℝ))*(S:ℝ) ≤ D) :
    ((2^(k-1):ℕ):ℝ≥0∞)*ENNReal.ofReal (Real.exp (-b*D)) <
      (1/2:ℝ≥0∞)^S := by
  have hD : (s:ℝ)*((k+S:ℕ):ℝ) ≤ D := by push_cast; nlinarith
  have hbig := CameronMartinRate.dyadic_exponential_mass_lt (by omega : 2≤k+S)
    hb hD hbs
  have hfactor : (2:ℝ≥0∞)^S * ((2^(k-1):ℕ):ℝ≥0∞) =
      ((2^(k+S-1):ℕ):ℝ≥0∞) := by
    norm_cast
    rw [← pow_add]
    congr 1
    omega
  by_contra hn
  have hle := le_of_not_gt hn
  have hone : (2:ℝ≥0∞)^S * (1/2:ℝ≥0∞)^S = 1 := by
    have hhalf : (2:ℝ≥0∞)*(1/2:ℝ≥0∞)=1 := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    rw [← mul_pow, hhalf, one_pow]
  have hbad : (1:ℝ≥0∞) ≤
      ((2^(k+S-1):ℕ):ℝ≥0∞)*ENNReal.ofReal (Real.exp (-b*D)) := by
    calc
      _ = (2:ℝ≥0∞)^S * (1/2:ℝ≥0∞)^S := hone.symm
      _ ≤ (2:ℝ≥0∞)^S *
          (((2^(k-1):ℕ):ℝ≥0∞)*ENNReal.ofReal (Real.exp (-b*D))) := by gcongr
      _ = _ := by rw [← mul_assoc, hfactor]
  have hthree : (3/4:ℝ≥0∞)<1 := by
    apply (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    norm_num
  exact (not_le_of_gt (hbig.trans hthree)) hbad

end BrownianSharp
