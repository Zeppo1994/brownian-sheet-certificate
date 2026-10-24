import BrownianSharp.PeriodicEntropy
import BrownianSharp.ShapeGrowth
import BrownianSharp.ExtendedStatements
import BrownianSharp.LayerIndex
import BrownianSharp.KolmogorovWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-! Conversion from an eventual dyadic layer-width estimate to the sharp
all-index mixed-smoothness rate. -/

open BrownianSharp HaarQuarter
open Filter
open scoped ENNReal
open scoped Topology

namespace BrownianSharp.DKLLWidthRateExtraction

noncomputable section

private theorem crossing_eventually_ge {d N : ℕ} (hd : 2 ≤ d) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      N ≤ nativeEntropyCrossing d k (by omega) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : 0 < nativeLogScaleLower d := nativeLogScaleLower_pos hd
  have hev : ∀ᶠ k : ℕ in atTop,
      N ≤ nativeEntropyCrossing d k (by omega) := by
    filter_upwards [hlog.eventually_ge_atTop
      (nativeLogScaleLower d * (N : ℝ)), eventually_ge_atTop 2] with k hlarge hk
    rw [nativeLogScaleLower] at hlarge
    have hcross := (nativeEntropyCrossing_log_bounds hd hk).1
    have hN : (N : ℝ) ≤ (nativeEntropyCrossing d k (by omega) : ℝ) := by
      apply (mul_le_mul_iff_of_pos_left hscale).1
      exact hlarge.trans hcross
    exact_mod_cast hN
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  exact ⟨max 2 k₀, le_max_left _ _, fun k hk => hk₀ k ((le_max_right _ _).trans hk)⟩

theorem all_index_width_rate_of_dyadic_layer_bound
    {d : ℕ} (hd : 2 ≤ d) (K : Set C(BrownianCubeAnchor d, ℝ))
    (B : ℝ) (hB : 0 < B) (n₀ : ℕ)
    (hupper : ∀ n : ℕ, n₀ ≤ n →
      TheoremD.Width.kolmogorovWidth K (4 * Fintype.card (LayerIndex d n)) ≤
        ENNReal.ofReal (B * Real.sqrt ((n : ℝ) + 1) / (2 : ℝ) ^ n)) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₁ : ℕ, 8 ≤ m₁ ∧
      ∀ m : ℕ, m₁ ≤ m →
        TheoremD.Width.kolmogorovWidth K m ≤
          ENNReal.ofReal (C * logarithmicIndexRate 1
            ((d : ℝ) - 1 / 2) m) := by
  let α : ℝ := (d : ℝ) - 1 / 2
  let Q : ℝ := nativeLogScaleUpper d
  let L : ℝ := 2 * Q + 1
  let C : ℝ := B * (32 * (d : ℝ) ^ 2) * L ^ α
  obtain ⟨k₀, hk₀, hcross⟩ := crossing_eventually_ge (d := d) (N := n₀ + 1) hd
  let m₀ : ℕ := max 8 (4 * k₀)
  refine ⟨C, ?_, m₀, ?_, ?_⟩
  · dsimp [C, L, Q, α]
    have hL : 0 < 2 * nativeLogScaleUpper d + 1 := by
      have hQ := nativeLogScaleUpper_pos hd
      positivity
    exact mul_pos (mul_pos hB (by positivity)) (Real.rpow_pos_of_pos hL _)
  · dsimp [m₀]
    omega
  · intro m hm
    have hm8 : 8 ≤ m := le_trans (by dsimp [m₀]; omega) hm
    let k : ℕ := m / 4
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hk₀m : k₀ ≤ k := by
      have hm₀k : 4 * k₀ ≤ m := by
        have : 4 * k₀ ≤ m₀ := by dsimp [m₀]; omega
        exact this.trans hm
      dsimp [k]
      omega
    let q : ℕ := nativeEntropyCrossing d k (by omega)
    have hqgrade : n₀ + 1 ≤ q := by
      simpa [q, k] using hcross k hk₀m
    have hbr := nativeEntropyCrossing_bracket hd hk
    have hqpos : 0 < q := by
      simpa [q] using hbr.1
    let n : ℕ := 2 * (q - 1)
    have hn : n₀ ≤ n := by dsimp [n]; omega
    have hprev : nativeDimension d n < (k : ℝ) := by
      simpa [n, q] using hbr.2.1
    have hn2 : n + 2 = 2 * q := by dsimp [n]; omega
    have hcurr : (k : ℝ) ≤ nativeDimension d (n + 2) := by
      rw [hn2]
      exact hbr.2.2.1
    have hstep₁ := nativeDimension_step_le (d := d) (n := n) (by omega)
    have hstep₂ := nativeDimension_step_le (d := d) (n := n + 1) (by omega)
    have hdimstep : nativeDimension d (n + 2) ≤
        (4 * (d : ℝ) ^ 2) * nativeDimension d n := by
      calc
        nativeDimension d (n + 2) ≤ (2 * (d : ℝ)) * nativeDimension d (n + 1) := by
          simpa [Nat.add_assoc] using hstep₂
        _ ≤ (2 * (d : ℝ)) * ((2 * (d : ℝ)) * nativeDimension d n) :=
          mul_le_mul_of_nonneg_left hstep₁ (by positivity)
        _ = (4 * (d : ℝ) ^ 2) * nativeDimension d n := by ring
    have hdimlower : (k : ℝ) / (4 * (d : ℝ) ^ 2) ≤ nativeDimension d n := by
      have hden : 0 < (4 : ℝ) * (d : ℝ) ^ 2 := by positivity
      apply (div_le_iff₀ hden).2
      calc
        (k : ℝ) ≤ nativeDimension d (n + 2) := hcurr
        _ ≤ (4 * (d : ℝ) ^ 2) * nativeDimension d n := hdimstep
        _ = nativeDimension d n * (4 * (d : ℝ) ^ 2) := by ring
    have hdivbound : (m : ℝ) < 4 * (k : ℝ) + 4 := by
      have hnat : m < 4 * (m / 4 + 1) := by omega
      exact_mod_cast hnat
    have hk_m : (m : ℝ) / 8 ≤ (k : ℝ) := by
      have hmR : 8 ≤ (m : ℝ) := by exact_mod_cast hm8
      dsimp [k]
      nlinarith
    have hDlower : (m : ℝ) / (32 * (d : ℝ) ^ 2) ≤ nativeDimension d n := by
      have hmul := div_le_div_of_nonneg_right hk_m
        (by positivity : 0 ≤ (4 : ℝ) * (d : ℝ) ^ 2)
      have hsimple : ((m : ℝ) / 8) / (4 * (d : ℝ) ^ 2) =
          (m : ℝ) / (32 * (d : ℝ) ^ 2) := by field_simp; ring
      rw [hsimple] at hmul
      exact hmul.trans hdimlower
    have hDpos : 0 < nativeDimension d n := by
      exact (div_pos (by positivity)
        (by positivity : 0 < (32 : ℝ) * (d : ℝ) ^ 2)).trans_le hDlower
    have hcard : (Fintype.card (LayerIndex d n) : ℝ) = nativeDimension d n := by
      rw [layerIndex_card d n (by omega)]
      simp [nativeDimension, hyperbolicCount]
    have hrank : 4 * Fintype.card (LayerIndex d n) ≤ m := by
      have hprev' : (Fintype.card (LayerIndex d n) : ℝ) < (k : ℝ) := by
        rw [hcard]
        exact hprev
      have hprevNat : Fintype.card (LayerIndex d n) < k := by exact_mod_cast hprev'
      omega
    have hwidth := hupper n hn
    have hmono := TheoremD.Width.kolmogorovWidth_antitone K hrank
    have hshape : hyperbolicCount d n ≤ ((n : ℝ) + 1) ^ (d - 1) :=
      hyperbolicCount_upper_shift (by omega) n
    have hDidentity : nativeDimension d n =
        (2 : ℝ) ^ n * hyperbolicCount d n := rfl
    have hlogm : 1 ≤ Real.log (m : ℝ) := by
      have hmexp : Real.exp 1 ≤ (m : ℝ) := by
        have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        have hmR : 3 ≤ (m : ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
        exact h3.le.trans hmR
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hmexp
    have hlogmk : Real.log (k : ℝ) ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log (by positivity)
      have : k ≤ m := by omega
      exact_mod_cast this
    have hqlog := (nativeEntropyCrossing_log_bounds hd hk).2
    have hqlog' : (q : ℝ) ≤ Q * Real.log (m : ℝ) := by
      have hqeq : q = nativeEntropyCrossing d k (by omega) := rfl
      rw [hqeq]
      calc
        (nativeEntropyCrossing d k (by omega) : ℝ) ≤
            nativeLogScaleUpper d * Real.log (k : ℝ) := hqlog
        _ ≤ Q * Real.log (m : ℝ) := by
          simpa [Q] using mul_le_mul_of_nonneg_left hlogmk
            (le_of_lt (nativeLogScaleUpper_pos hd))
    have hnlog : (n : ℝ) + 1 ≤ L * Real.log (m : ℝ) := by
      have hqcast : (n : ℝ) = 2 * ((q : ℝ) - 1) := by
        dsimp [n]
        simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ q)]
        push_cast
        ring
      rw [hqcast]
      dsimp [L]
      have hQpos : 0 ≤ Q := le_of_lt (nativeLogScaleUpper_pos hd)
      nlinarith [hqlog', hlogm]
    have hα : 0 ≤ α := by
      dsimp [α]
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hbasepos : 0 < (L * Real.log (m : ℝ)) := by
      have hLpos : 0 < L := by
        dsimp [L, Q]
        have hQ := nativeLogScaleUpper_pos hd
        positivity
      exact mul_pos hLpos (by linarith)
    have hnpow : ((n : ℝ) + 1) ^ α ≤ (L * Real.log (m : ℝ)) ^ α :=
      Real.rpow_le_rpow (by positivity) hnlog hα
    have hfactor : (L * Real.log (m : ℝ)) ^ α =
        L ^ α * (Real.log (m : ℝ)) ^ α := by
      have hLpos : 0 < L := by
        dsimp [L, Q]
        have hQ := nativeLogScaleUpper_pos hd
        linarith
      have hlogpos : 0 < Real.log (m : ℝ) := by linarith
      rw [Real.mul_rpow hLpos.le hlogpos.le]
    have hsqrtShape : Real.sqrt ((n : ℝ) + 1) *
        ((n : ℝ) + 1) ^ (d - 1) = ((n : ℝ) + 1) ^ α := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_add (by positivity)]
      congr 1
      dsimp [α]
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      ring
    have hrate_real : B * Real.sqrt ((n : ℝ) + 1) / (2 : ℝ) ^ n ≤
        C * logarithmicIndexRate 1 α m := by
      have hshapeDiv :
          Real.sqrt ((n : ℝ) + 1) / (2 : ℝ) ^ n ≤
            (((n : ℝ) + 1) ^ α) / nativeDimension d n := by
        have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
        have hSbound : Real.sqrt ((n : ℝ) + 1) * hyperbolicCount d n ≤
            ((n : ℝ) + 1) ^ α := by
          calc
            _ ≤ Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (d - 1) :=
              mul_le_mul_of_nonneg_left hshape (Real.sqrt_nonneg _)
            _ = ((n : ℝ) + 1) ^ α := hsqrtShape
        apply (div_le_div_iff₀ hpowpos hDpos).2
        rw [hDidentity]
        calc
          Real.sqrt ((n : ℝ) + 1) *
              ((2 : ℝ) ^ n * hyperbolicCount d n) =
              (Real.sqrt ((n : ℝ) + 1) * hyperbolicCount d n) * (2 : ℝ) ^ n := by ring
          _ ≤ ((n : ℝ) + 1) ^ α * (2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right hSbound (by positivity)
      have hrate1 :
          B * Real.sqrt ((n : ℝ) + 1) / (2 : ℝ) ^ n ≤
            B * (((n : ℝ) + 1) ^ α / nativeDimension d n) :=
        calc
          _ = B * (Real.sqrt ((n : ℝ) + 1) / (2 : ℝ) ^ n) := by ring
          _ ≤ B * (((n : ℝ) + 1) ^ α / nativeDimension d n) :=
            mul_le_mul_of_nonneg_left hshapeDiv hB.le
      have hdimInv : (nativeDimension d n)⁻¹ ≤
          (32 * (d : ℝ) ^ 2) / (m : ℝ) := by
        have hmpos : 0 < (m : ℝ) := by positivity
        have hdenpos : 0 < (32 : ℝ) * (d : ℝ) ^ 2 := by positivity
        calc
          (nativeDimension d n)⁻¹ ≤ 1 / ((m : ℝ) / (32 * (d : ℝ) ^ 2)) := by
            simpa [one_div] using
              (one_div_le_one_div hDpos (div_pos hmpos hdenpos)).2 hDlower
          _ = (32 * (d : ℝ) ^ 2) / (m : ℝ) := by field_simp
      have hrate2 : B * (((n : ℝ) + 1) ^ α / nativeDimension d n) ≤
          B * (32 * (d : ℝ) ^ 2) * (((n : ℝ) + 1) ^ α / (m : ℝ)) := by
        have hcoef : 0 ≤ B * ((n : ℝ) + 1) ^ α := by positivity
        calc
          _ = B * ((n : ℝ) + 1) ^ α * (nativeDimension d n)⁻¹ := by ring
          _ ≤ B * ((n : ℝ) + 1) ^ α * ((32 * (d : ℝ) ^ 2) / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hdimInv hcoef
          _ = B * (32 * (d : ℝ) ^ 2) * (((n : ℝ) + 1) ^ α / (m : ℝ)) := by ring
      have hrate3 : ((n : ℝ) + 1) ^ α ≤ L ^ α * (Real.log (m : ℝ)) ^ α := by
        rw [← hfactor]
        exact hnpow
      dsimp [C, logarithmicIndexRate]
      have hmpos : 0 < (m : ℝ) := by positivity
      have hrpow : (m : ℝ) ^ (-1 : ℝ) = (m : ℝ)⁻¹ := by
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ)), Real.rpow_one]
      calc
        _ ≤ B * (32 * (d : ℝ) ^ 2) *
            (L ^ α * (Real.log (m : ℝ)) ^ α) / (m : ℝ) := by
          calc
            B * Real.sqrt ((n : ℝ) + 1) / (2 : ℝ) ^ n ≤
              B * (((n : ℝ) + 1) ^ α / nativeDimension d n) := hrate1
            _ ≤ B * (32 * (d : ℝ) ^ 2) * (((n : ℝ) + 1) ^ α / (m : ℝ)) := hrate2
            _ ≤ B * (32 * (d : ℝ) ^ 2) *
                (L ^ α * (Real.log (m : ℝ)) ^ α / (m : ℝ)) := by
              apply mul_le_mul_of_nonneg_left
              · exact div_le_div_of_nonneg_right hrate3 (by positivity)
              · positivity
            _ = B * (32 * (d : ℝ) ^ 2) *
                (L ^ α * (Real.log (m : ℝ)) ^ α) / (m : ℝ) := by ring
        _ = (B * (32 * (d : ℝ) ^ 2) * L ^ α) *
            ((m : ℝ) ^ (-1 : ℝ) * (Real.log (m : ℝ)) ^ α) := by
              rw [hrpow]
              ring
    have hwidth' : TheoremD.Width.kolmogorovWidth K m ≤
        ENNReal.ofReal (C * logarithmicIndexRate 1 α m) := by
      exact hmono.trans (hwidth.trans (ENNReal.ofReal_le_ofReal hrate_real))
    simpa [α, cmIndexRate, logarithmicIndexRate] using hwidth'

end
end BrownianSharp.DKLLWidthRateExtraction
