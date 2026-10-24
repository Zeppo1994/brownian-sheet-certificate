import BrownianSharp.PeriodicEntropy
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.LayerIndex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
open Filter
open scoped ENNReal

namespace BrownianSharp.AlignmentIntegerTensorLowerRate

open BrownianSharp
open BrownianSharp.AlignmentFractionalApproximationNumbers

private theorem crossing_grade_eventually_ge {d N : ℕ} (hd : 2 ≤ d) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      N ≤ 2 * nativeEntropyCrossing d (2*k) (by omega) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let L := nativeLogScaleLower d
  have hL : 0 < L := nativeLogScaleLower_pos hd
  have hev : ∀ᶠ k : ℕ in atTop,
      N ≤ 2 * nativeEntropyCrossing d (2*k) (by omega) := by
    filter_upwards [hlog.eventually_ge_atTop (L * (N:ℝ)), eventually_ge_atTop 2]
      with k hlarge hk
    have hcross := (nativeEntropyCrossing_log_bounds hd (by omega : 2 ≤ 2*k)).1
    have hq : (N:ℝ) ≤ 2 * (nativeEntropyCrossing d (2*k) (by omega):ℝ) := by
      have hklog : Real.log (k:ℝ) ≤ Real.log ((2*k:ℕ):ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast (show k ≤ 2*k by omega)
      have hcross' : Real.log ((2*k:ℕ):ℝ) ≤
          L * (nativeEntropyCrossing d (2*k) (by omega):ℝ) := by
        simpa [L, nativeLogScaleLower] using hcross
      have hLlarge : L * (N:ℝ) ≤ Real.log (k:ℝ) := by
        simpa [L] using hlarge
      have hqN : (N:ℝ) ≤ (nativeEntropyCrossing d (2*k) (by omega):ℝ) := by
        have hLpos := hL
        nlinarith [hLlarge, hklog, hcross']
      exact_mod_cast (show (N:ℝ) ≤ 2*(nativeEntropyCrossing d (2*k) (by omega):ℝ) by nlinarith)
    exact_mod_cast hq
  obtain ⟨k₀,hk₀⟩ := eventually_atTop.1 hev
  exact ⟨max 2 k₀, le_max_left _ _, fun k hk =>
    hk₀ k ((le_max_right _ _).trans hk)⟩

/-- A layerwise approximation-number lower bound with scale `2^(-rN)`
implies its all-index rate. The layer estimate is assumed only eventually in
the layer grade, and its rank parameter ranges over the full layer. -/
theorem all_index_lower_of_layer_bound
    {d : ℕ} (hd : 2 ≤ d) (r c : ℝ) (hr : 1/2 < r) (hc : 0 < c)
    (N₀ : ℕ) (f : ℕ → ℝ≥0∞)
    (hlayer : ∀ N k : ℕ, N₀ ≤ N → 1 ≤ k →
      k ≤ Fintype.card (LayerIndex d N) →
      ENNReal.ofReal (c * (2:ℝ)^(-r*(N:ℝ)) *
        Real.sqrt (((Fintype.card (LayerIndex d N) - (k-1):ℕ):ℝ))) ≤ f k) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c₁ * (k:ℝ)^(-r+1/2) *
          (Real.log (k:ℝ))^(r*((d-1:ℕ):ℝ))) ≤ f k := by
  classical
  let F := ((d-1:ℕ):ℝ)
  let L := nativeLogScaleLower d
  let U := 8*(d:ℝ)^2
  let fact := (Nat.factorial (d-1):ℝ)
  let c₁ := c * (1/(U*fact))^r * (1/L)^(r*F)
  obtain ⟨k₀,hk₀,hgrade⟩ := crossing_grade_eventually_ge (d:=d) (N:=N₀) hd
  refine ⟨c₁, ?_, max k₀ 2, le_max_right _ _, ?_⟩
  · dsimp [c₁,L,U,fact]
    have hL := nativeLogScaleLower_pos hd
    have hU : 0 < 8*(d:ℝ)^2 := by positivity
    have hfact : 0 < (Nat.factorial (d-1):ℝ) := by positivity
    positivity
  · intro k hk
    have hk2 : 2 ≤ k := (le_max_right _ _).trans hk
    have hgrade' : N₀ ≤ 2*nativeEntropyCrossing d (2*k) (by omega) :=
      hgrade k ((le_max_left _ _).trans hk)
    let q := nativeEntropyCrossing d (2*k) (by omega)
    let N := 2*q
    let D := Fintype.card (LayerIndex d N)
    have hbr := nativeEntropyCrossing_bracket hd (by omega : 2 ≤ 2*k)
    have hqpos : 0 < q := by dsimp [q]; exact hbr.1
    have hDident : (D:ℝ) = nativeDimension d N := by
      dsimp [D,N]
      rw [layerIndex_card d (2*q) (by omega : 0<d)]
      simp [nativeDimension,hyperbolicCount]
    have hDlow : 2*(k:ℝ) ≤ (D:ℝ) := by
      rw [hDident]
      simpa [q] using hbr.2.2.1
    have hDhigh : (D:ℝ) ≤ U*(k:ℝ) := by
      calc
        (D:ℝ) = nativeDimension d (2*q) := by simpa [N,q] using hDident
        _ ≤ 4*(d:ℝ)^2*(2*(k:ℝ)) := by simpa [q] using hbr.2.2.2
        _ = U*(k:ℝ) := by dsimp [U]; ring
    have hDnat : 2*k ≤ D := by exact_mod_cast hDlow
    have hkD : k ≤ D := by omega
    have hqNat : 0 < q := hqpos
    have hpoly := nativeDimension_polynomial_lower (d:=d) (q:=q) hd hqNat
    have hpolyD : ((q:ℝ)^F / fact) * (2:ℝ)^N ≤ (D:ℝ) := by
      calc
        ((q:ℝ)^F / fact) * (2:ℝ)^N =
            (1/(Nat.factorial (d-1):ℝ)) * (2:ℝ)^(2*q) * (q:ℝ)^F := by
              dsimp [F]
              dsimp [fact,N]
              field_simp
        _ ≤ nativeDimension d (2*q) := by simpa [F,fact,N,q] using hpoly
        _ = (D:ℝ) := by simpa [N,q] using hDident.symm
    have hDpos : 0 < (D:ℝ) := lt_of_lt_of_le (by positivity : 0 < 2*(k:ℝ)) hDlow
    have hprod : (q:ℝ)^F * (2:ℝ)^N ≤ fact*(D:ℝ) := by
      have hfpos : 0 < fact := by dsimp [fact]; positivity
      calc
        (q:ℝ)^F * (2:ℝ)^N = fact * (((q:ℝ)^F / fact) * (2:ℝ)^N) := by
          field_simp [ne_of_gt hfpos]
        _ ≤ fact * (D:ℝ) := mul_le_mul_of_nonneg_left hpolyD hfpos.le
    have hdyad : (q:ℝ)^F / (fact*(D:ℝ)) ≤ ((2:ℝ)^N)⁻¹ := by
      have hdenpos : 0 < (2:ℝ)^N := by positivity
      apply (div_le_iff₀ (mul_pos (by positivity) hDpos)).2
      rw [inv_eq_one_div]
      field_simp [ne_of_gt hdenpos]
      nlinarith [hprod]
    have hqlog := (nativeEntropyCrossing_log_bounds hd (by omega : 2 ≤ 2*k)).1
    have hlogkpos : 0 < Real.log (k:ℝ) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < k)
    have hqloglower : (Real.log (k:ℝ))/L ≤ (q:ℝ) := by
      have hlog2k : Real.log (k:ℝ) ≤ Real.log ((2*k:ℕ):ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast (show k ≤ 2*k by omega)
      apply (div_le_iff₀ (nativeLogScaleLower_pos hd)).2
      have hcross : Real.log ((2*k:ℕ):ℝ) ≤ L*(q:ℝ) := by
        simpa [q,L,nativeLogScaleLower] using hqlog
      exact hlog2k.trans (by simpa [mul_comm] using hcross)
    have hdyadQ : (q:ℝ)^F / (fact*(D:ℝ)) ≤ (2:ℝ)^(-(N:ℝ)) := by
      have hInv : ((2:ℝ)^N)⁻¹ = (2:ℝ)^(-(N:ℝ)) := by
        rw [← Real.rpow_natCast (2:ℝ) N,
          Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
      exact hdyad.trans_eq hInv
    have hbase : ((Real.log (k:ℝ))/L)^F / (fact*U*(k:ℝ)) ≤ (2:ℝ)^(-(N:ℝ)) := by
      have hqpow : ((Real.log (k:ℝ))/L)^F ≤ (q:ℝ)^F := by
        have hb : 0 ≤ Real.log (k:ℝ) / L := div_nonneg hlogkpos.le
          (nativeLogScaleLower_pos hd).le
        exact Real.rpow_le_rpow hb hqloglower (by positivity)
      have hden : fact*(D:ℝ) ≤ fact*U*(k:ℝ) := by
        have hfpos : 0 ≤ fact := by dsimp [fact]; positivity
        calc
          fact*(D:ℝ) ≤ fact*(U*(k:ℝ)) := mul_le_mul_of_nonneg_left hDhigh hfpos
          _ = fact*U*(k:ℝ) := by ring
      have hratio' : ((Real.log (k:ℝ))/L)^F / (fact*U*(k:ℝ)) ≤
          (q:ℝ)^F / (fact*(D:ℝ)) := by
        have hnum := div_le_div_of_nonneg_right hqpow (by positivity : 0≤fact*U*(k:ℝ))
        have hden' : (q:ℝ)^F / (fact*U*(k:ℝ)) ≤
            (q:ℝ)^F / (fact*(D:ℝ)) := by
          exact div_le_div_of_nonneg_left (by positivity)
            (by positivity) hden
        exact hnum.trans hden'
      exact hratio'.trans hdyadQ
    have hscale : (2:ℝ)^(-r*(N:ℝ)) ≥
        (((Real.log (k:ℝ))/L)^F / (fact*U*(k:ℝ)))^r := by
      have hpower : ((2:ℝ)^(-(N:ℝ)))^r = (2:ℝ)^(-r*(N:ℝ)) := by
        rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
        congr 1 <;> ring
      rw [← hpower]
      have hbase0 : 0 ≤ ((Real.log (k:ℝ))/L)^F / (fact*U*(k:ℝ)) := by
        apply div_nonneg
        · exact Real.rpow_nonneg (div_nonneg hlogkpos.le (nativeLogScaleLower_pos hd).le) _
        · positivity
      exact Real.rpow_le_rpow hbase0 hbase (by linarith)
    have hN0 : N₀ ≤ N := by simpa [N,q] using hgrade'
    have hOneK : 1 ≤ k := by omega
    have hlayer := hlayer N k hN0 hOneK hkD
    have hgapNat : k ≤ D-(k-1) := by omega
    have hgap : (k:ℝ) ≤ ((D-(k-1):ℕ):ℝ) := by exact_mod_cast hgapNat
    have hsqrt : Real.sqrt (k:ℝ) ≤ Real.sqrt ((D-(k-1):ℕ):ℝ) :=
      Real.sqrt_le_sqrt hgap
    have hrate : c₁*(k:ℝ)^(-r+1/2)*(Real.log (k:ℝ))^(r*F) ≤
        c*(2:ℝ)^(-r*(N:ℝ))*Real.sqrt ((D-(k-1):ℕ):ℝ) := by
      dsimp [c₁]
      have hfacpow : (((Real.log (k:ℝ))/L)^F / (fact*U*(k:ℝ)))^r =
          (1/(fact*U))^r * (1/L)^(r*F) *
            (k:ℝ)^(-r) * (Real.log (k:ℝ))^(r*F) := by
        have hlogL : ((Real.log (k:ℝ) / L)^F)^r =
            (1/L)^(r*F) * (Real.log (k:ℝ))^(r*F) := by
          calc
            ((Real.log (k:ℝ) / L)^F)^r =
                (Real.log (k:ℝ) / L)^(F*r) := (Real.rpow_mul
                  (div_nonneg hlogkpos.le (nativeLogScaleLower_pos hd).le) F r).symm
            _ = (Real.log (k:ℝ))^(F*r) / L^(F*r) :=
              Real.div_rpow hlogkpos.le (nativeLogScaleLower_pos hd).le (F*r)
            _ = (1/L)^(r*F) * (Real.log (k:ℝ))^(r*F) := by
              rw [mul_comm F r]
              have hinv : (L^(r*F))⁻¹ = (1/L)^(r*F) := by
                have hdiv := Real.div_rpow (by norm_num : (0:ℝ)≤1)
                  (nativeLogScaleLower_pos hd).le (r*F)
                simpa [Real.one_rpow] using hdiv.symm
              rw [div_eq_mul_inv, hinv]
              ring
        have hden : (fact*U*(k:ℝ))^(-r) =
            (1/(fact*U))^r * (k:ℝ)^(-r) := by
          have hx : (fact*U)^(-r) = (1/(fact*U))^r := by
            have hdiv := Real.div_rpow (by norm_num : (0:ℝ)≤1)
              (by positivity : 0≤fact*U) r
            calc
              (fact*U)^(-r) = ((fact*U)^r)⁻¹ := by
                rw [Real.rpow_neg (by positivity)]
              _ = (1/(fact*U))^r := by
                simpa [Real.one_rpow] using hdiv.symm
          rw [show fact*U*(k:ℝ) = (fact*U)*(k:ℝ) by ring,
            Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
          rw [mul_inv, ← Real.rpow_neg (by positivity : 0≤fact*U), hx,
            ← Real.rpow_neg (by positivity : 0≤(k:ℝ))]
        have hnum0 : 0 ≤ (Real.log (k:ℝ) / L)^F :=
          Real.rpow_nonneg (div_nonneg hlogkpos.le (nativeLogScaleLower_pos hd).le) _
        have hden0 : 0 ≤ fact*U*(k:ℝ) := by positivity
        rw [Real.div_rpow hnum0 hden0 r,
          hlogL, div_eq_mul_inv,
          ← Real.rpow_neg (by positivity : 0≤fact*U*(k:ℝ)), hden]
        ring_nf
      have hscale' : (2:ℝ)^(-r*(N:ℝ)) ≥
          (1/(fact*U))^r * (1/L)^(r*F) *
            (k:ℝ)^(-r) * (Real.log (k:ℝ))^(r*F) := by
        rw [← hfacpow]
        exact hscale
      have hroot := mul_le_mul_of_nonneg_left hsqrt
        (by positivity : 0≤c*(2:ℝ)^(-r*(N:ℝ)))
      have hroot' : c*(2:ℝ)^(-r*(N:ℝ))*Real.sqrt (k:ℝ) ≤
          c*(2:ℝ)^(-r*(N:ℝ))*Real.sqrt ((D-(k-1):ℕ):ℝ) := by
        simpa [mul_assoc] using hroot
      have hpowk : (k:ℝ)^(-r+1/2) = (k:ℝ)^(-r)*Real.sqrt (k:ℝ) := by
        rw [Real.rpow_add (by positivity)]
        simp only [Real.sqrt_eq_rpow]
      calc
        c₁*(k:ℝ)^(-r+1/2)*(Real.log (k:ℝ))^(r*F) =
            c * ((1/(fact*U))^r * (1/L)^(r*F) *
              (k:ℝ)^(-r) * (Real.log (k:ℝ))^(r*F)) * Real.sqrt (k:ℝ) := by
                dsimp [c₁]
                rw [hpowk]
                ring
        _ ≤ c*(2:ℝ)^(-r*(N:ℝ))*Real.sqrt (k:ℝ) := by
              have hsc := mul_le_mul_of_nonneg_left hscale' hc.le
              have hsc' := mul_le_mul_of_nonneg_right hsc (Real.sqrt_nonneg (k:ℝ))
              simpa [mul_assoc] using hsc'
        _ ≤ _ := hroot'
    have hnonneg : 0 ≤ c*(2:ℝ)^(-r*(N:ℝ))*Real.sqrt ((D-(k-1):ℕ):ℝ) := by positivity
    exact (ENNReal.ofReal_le_ofReal hrate).trans hlayer

end BrownianSharp.AlignmentIntegerTensorLowerRate
