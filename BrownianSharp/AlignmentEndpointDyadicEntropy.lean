import BrownianSharp.ExtendedStatements
import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentCarlEntropyUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentEndpointDyadicEntropy

open BrownianSharp

private theorem logarithmicIndexRate_nonneg_of_two_le
    {s a : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ logarithmicIndexRate s a k := by
  unfold logarithmicIndexRate
  apply mul_nonneg
  · positivity
  · exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))) _

private theorem dyadic_rate_le_comparable_rate
    {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    {N k Q : ℕ} (hN : 2 ≤ N) (hNk : N ≤ k)
    (hkQ : (k : ℝ) ≤ (Q : ℝ) * (N : ℝ)) (hQ : 0 < Q) :
    logarithmicIndexRate s a N ≤ (Q : ℝ)^s * logarithmicIndexRate s a k := by
  have hNR : 0 < (N : ℝ) := by positivity
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast (show 0 < k from lt_of_lt_of_le (by omega : 0 < N) hNk)
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogK : 0 < Real.log (k : ℝ) := by
    apply Real.log_pos
    have hk' : (2 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show 2 ≤ k from le_trans hN hNk)
    linarith
  have hlogCmp : Real.log (N : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log hNR (by exact_mod_cast hNk)
  have hlogPow : (Real.log (N : ℝ))^a ≤ (Real.log (k : ℝ))^a :=
    Real.rpow_le_rpow hlogN.le hlogCmp ha
  have hdivide : (N : ℝ)⁻¹ ≤ (Q : ℝ) * (k : ℝ)⁻¹ := by
    have hmul : (k:ℝ) ≤ (Q:ℝ)*(N:ℝ) := hkQ
    field_simp
    nlinarith [hQR]
  have hinvpow : ((N : ℝ)⁻¹)^s ≤ ((Q : ℝ) * (k : ℝ)⁻¹)^s :=
    Real.rpow_le_rpow (by positivity) hdivide hs.le
  have hpowLeft : ((N : ℝ)⁻¹)^s = (N : ℝ)^(-s) := by
    calc
      ((N:ℝ)⁻¹)^s = (1/(N:ℝ))^s := by congr 2; field_simp
      _ = 1^s / (N:ℝ)^s := Real.div_rpow (by norm_num) hNR.le s
      _ = ((N:ℝ)^s)⁻¹ := by simp
      _ = (N:ℝ)^(-s) := by rw [Real.rpow_neg hNR.le]
  have hpowRight : ((Q : ℝ) * (k : ℝ)⁻¹)^s =
      (Q : ℝ)^s * (k : ℝ)^(-s) := by
    calc
      ((Q:ℝ)*(k:ℝ)⁻¹)^s = ((Q:ℝ)/(k:ℝ))^s := by congr 2
      _ = (Q:ℝ)^s / (k:ℝ)^s := Real.div_rpow hQR.le hkR.le s
      _ = (Q:ℝ)^s * ((k:ℝ)^s)⁻¹ := by ring
      _ = (Q:ℝ)^s * (k:ℝ)^(-s) := by rw [Real.rpow_neg hkR.le]
  unfold logarithmicIndexRate
  calc
    (N:ℝ)^(-s) * (Real.log (N:ℝ))^a =
        ((N:ℝ)⁻¹)^s * (Real.log (N:ℝ))^a := by rw [← hpowLeft]
    _ ≤ ((Q:ℝ)*(k:ℝ)⁻¹)^s * (Real.log (k:ℝ))^a := by
      exact mul_le_mul hinvpow hlogPow (Real.rpow_nonneg hlogN.le _) (by positivity)
    _ = (Q:ℝ)^s * ((k:ℝ)^(-s) * (Real.log (k:ℝ))^a) := by rw [hpowRight]; ring

theorem all_index_entropy_rate_of_dyadic_bound
    {F : ℕ → ENNReal} (hF : Antitone F)
    {s a B : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hB : 0 < B)
    (D L₀ : ℕ) (hD : 0 < D)
    (hdyadic : ∀ L : ℕ, L₀ ≤ L →
      F (D * 2^L + 1) ≤ ENNReal.ofReal
        (B * logarithmicIndexRate s a (2^L))) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        F k ≤ ENNReal.ofReal (C * logarithmicIndexRate s a k) := by
  let Lmin : ℕ := max L₀ 1
  let k₀ : ℕ := (D + 1) * 2^Lmin
  let Q : ℕ := 2 * (D + 1)
  let C : ℝ := B * (Q : ℝ)^s
  have hLmin : 1 ≤ Lmin := Nat.le_max_right _ _
  have hQpos : 0 < Q := by dsimp [Q]; omega
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos hB (Real.rpow_pos_of_pos (by exact_mod_cast hQpos) _)
  refine ⟨C,hCpos,k₀,?_ ,?_⟩
  · dsimp [k₀]
    have hpow : 2 ≤ 2^Lmin := by
      calc
        2 = 2^1 := by norm_num
        _ ≤ 2^Lmin := Nat.pow_le_pow_right (by omega) hLmin
    have hDtwo : 2 ≤ D+1 := by omega
    have hprod : 2 ≤ (D+1)*2^Lmin := by
      calc
        2 ≤ 2^Lmin := hpow
        _ ≤ (D+1)*2^Lmin := Nat.le_mul_of_pos_left _ (by omega)
    exact hprod
  · intro k hk
    let q : ℕ := k / (D+1)
    let L : ℕ := Nat.log2 q
    let N : ℕ := 2^L
    have hden : 0 < D+1 := by omega
    have hqLower : 2^Lmin ≤ q := by
      dsimp [q,k₀] at *
      apply (Nat.le_div_iff_mul_le hden).2
      simpa [Nat.mul_comm] using hk
    have hqpos : q ≠ 0 := by
      have hpowpos : 0 < 2^Lmin := by positivity
      omega
    have hNle : N ≤ q := by
      dsimp [N,L]
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 hqpos
    have hqLt : q < 2*N := by
      dsimp [N,L]
      have h := Nat.lt_pow_of_log_lt (by omega : 1 < 2)
        (Nat.lt_succ_self (Nat.log 2 q))
      simpa [Nat.pow_succ,Nat.log2_eq_log_two,Nat.mul_comm] using h
    have hLminL : Lmin ≤ L := by
      dsimp [L]
      rw [Nat.log2_eq_log_two]
      exact Nat.le_log_of_pow_le (by omega : 1 < 2) hqLower
    have hL₀L : L₀ ≤ L := le_trans (le_max_left _ _) hLminL
    have hNge : 2 ≤ N := by
      dsimp [N]
      have hL : 1 ≤ L := hLmin.trans hLminL
      calc
        2 = 2^1 := by norm_num
        _ ≤ 2^L := Nat.pow_le_pow_right (by omega) hL
    have hmul : (D+1)*q ≤ k := by
      dsimp [q]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self k (D+1)
    have hmul' : (D+1)*N ≤ k := (Nat.mul_le_mul_left (D+1) hNle).trans hmul
    have hmul'' : D*N+N ≤ k := by simpa [Nat.add_mul] using hmul'
    have hidxleNat : D*N+1 ≤ k := by
      have hDNpos : 0 < D*N := Nat.mul_pos hD (by omega)
      omega
    have hidxle : D*2^L+1 ≤ k := by simpa [N] using hidxleNat
    have hqsucc : q+1 ≤ 2*N := by omega
    have hkupNat : k < (D+1)*(q+1) := by
      have hmod : k % (D+1) < D+1 := Nat.mod_lt k hden
      have hdecomp : q*(D+1) + k % (D+1) = k := by
        simpa [q,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm] using Nat.mod_add_div k (D+1)
      have htarget : k < q*(D+1)+(D+1) := by omega
      simpa [Nat.mul_add,Nat.mul_comm,Nat.add_comm] using htarget
    have hkupNat' : k < Q*N := by
      calc
        k < (D+1)*(q+1) := hkupNat
        _ ≤ (D+1)*(2*N) := Nat.mul_le_mul_left (D+1) hqsucc
        _ = Q*N := by dsimp [Q]; ring
    have hkr : 2 ≤ k := by
      have hDNpos : 0 < D*N := Nat.mul_pos hD (by omega)
      have : 2 ≤ D*N+1 := by omega
      exact this.trans hidxleNat
    have hdyad := hdyadic L hL₀L
    have hFmono : F k ≤ F (D*2^L+1) := hF hidxle
    have hNleK : N ≤ k := by
      have hone : N ≤ (D+1)*N := by
        have hmulone := Nat.mul_le_mul_right N (by omega : 1 ≤ D+1)
        simpa using hmulone
      exact hone.trans hmul'
    have hkupReal : (k:ℝ) ≤ (Q:ℝ)*(N:ℝ) := by
      exact_mod_cast hkupNat'.le
    have hrate := dyadic_rate_le_comparable_rate hs ha hNge hNleK hkupReal hQpos
    have hscaled : B*logarithmicIndexRate s a N ≤ C*logarithmicIndexRate s a k := by
      have hrate' := mul_le_mul_of_nonneg_left hrate hB.le
      calc
        B*logarithmicIndexRate s a N ≤ B*((Q:ℝ)^s*logarithmicIndexRate s a k) := hrate'
        _ = C*logarithmicIndexRate s a k := by simp [C]; ring
    have hrateNonneg : 0 ≤ C*logarithmicIndexRate s a k :=
      mul_nonneg hCpos.le (logarithmicIndexRate_nonneg_of_two_le hkr)
    have hdyadic' : F (D*2^L+1) ≤
        ENNReal.ofReal (C*logarithmicIndexRate s a k) := by
      exact hdyad.trans (ENNReal.ofReal_le_ofReal hscaled)
    exact hFmono.trans hdyadic'

/-- Compose the fixed-multiple dyadic Carl estimate with the numerical
extraction above. A sharp eventual width upper rate therefore gives an
all-index entropy upper rate on the same compact-domain set. -/
theorem entropy_upper_all_indices_of_width_upper
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (K : Set X) {s a R C : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hR : 0 ≤ R) (hC : 0 < C) (m₀ : ℕ) (hm₀ : 2 ≤ m₀)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth K 0 ≤ ENNReal.ofReal R)
    (hwidth : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth K k ≤
        ENNReal.ofReal (C * logarithmicIndexRate s a k)) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k K ≤
        ENNReal.ofReal (C' * logarithmicIndexRate s a k) := by
  let L₀ : ℕ := max 2 (m₀.log2 + 1)
  have hL₀ : 2 ≤ L₀ := Nat.le_max_left _ _
  have hm₀pow : m₀ < 2^(m₀.log2+1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_of_log_lt (by omega : 1 < 2)
      (Nat.lt_succ_self (Nat.log 2 m₀))
  have hm₀pow' : ∀ L : ℕ, L₀ ≤ L → m₀ ≤ 2^L := by
    intro L hL
    have hlog : m₀.log2+1 ≤ L := by
      dsimp [L₀] at hL
      exact (le_max_right _ _).trans hL
    have hpow : 2^(m₀.log2+1) ≤ 2^L := Nat.pow_le_pow_right (by omega) hlog
    exact (Nat.le_of_lt hm₀pow).trans hpow
  obtain ⟨D,hD,B,hB,hdyad⟩ :=
    AlignmentCarlEntropyUpper.entropy_upper_at_dyadic_indices K s a R C hs ha hR hC
      m₀ hm₀ hzero (by intro k hk; exact hwidth k hk)
  have hdyad' : ∀ L : ℕ, L₀ ≤ L →
      HaarQuarter.TheoremD.entropyNumber (D*2^L+1) K ≤
        ENNReal.ofReal (B*logarithmicIndexRate s a (2^L)) := by
    intro L hL
    exact hdyad L (le_trans hL₀ hL) (hm₀pow' L hL)
  have hanti : Antitone (fun k : ℕ => HaarQuarter.TheoremD.entropyNumber k K) := by
    intro m n hmn
    exact AlignmentIsometricEntropy.entropyNumber_antitone K hmn
  exact all_index_entropy_rate_of_dyadic_bound hanti hs ha hB D L₀ hD hdyad'

end BrownianSharp.AlignmentEndpointDyadicEntropy
