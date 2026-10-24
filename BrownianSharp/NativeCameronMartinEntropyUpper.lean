import BrownianSharp.CarlRateExtraction
import BrownianSharp.ExtendedStatements
import Mathlib.Data.Nat.Log

/-! Entropy upper rates from sharp widths. Carl's dyadic multiscale cover is
first applied at index `96·2^L+1`; a binary-log choice then transfers the
bound to every sufficiently large index with the exact logarithmic power. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp

private theorem cmRate_nonneg {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    0 ≤ cmIndexRate d k := by
  unfold cmIndexRate logarithmicIndexRate
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have ha : 0 ≤ (d : ℝ) - 1 / 2 := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  positivity

private theorem cmIndexRate_lower_at_carl_index {d N : ℕ}
    (hd : 2 ≤ d) (hN : 4 ≤ N) :
    ((Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2)) /
      (97 * (N : ℝ)) ≤ cmIndexRate d (96 * N + 1) := by
  have hNR : 0 < (N : ℝ) := by positivity
  have hj : 2 ≤ 96 * N + 1 := by omega
  have hNle : (96 * N + 1 : ℕ) ≤ 97 * N := by omega
  have hNidx : N ≤ 96 * N + 1 := by omega
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlog : Real.log (N : ℝ) ≤ Real.log ((96 * N + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hNidx)
  have ha : 0 ≤ (d : ℝ) - 1 / 2 := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpow := Real.rpow_le_rpow hlogN hlog ha
  have hinv : (97 * (N : ℝ))⁻¹ ≤ ((96 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    have hden : ((96 * N + 1 : ℕ) : ℝ) ≤ 97 * (N : ℝ) := by exact_mod_cast hNle
    calc
      (97 * (N : ℝ))⁻¹ = 1 / (97 * (N : ℝ)) := by rw [inv_eq_one_div]
      _ ≤ 1 / ((96 * N + 1 : ℕ) : ℝ) := one_div_le_one_div_of_le (by positivity) hden
      _ = ((96 * N + 1 : ℕ) : ℝ)⁻¹ := by rw [inv_eq_one_div]
  have hmul := mul_le_mul hinv hpow (by positivity) (by positivity)
  rw [cmIndexRate, logarithmicIndexRate, Real.rpow_neg (by positivity), Real.rpow_one]
  have hidxcast : ((96 * N + 1 : ℕ) : ℝ) = 96 * (N : ℝ) + 1 := by push_cast; ring
  rw [hidxcast] at hmul ⊢
  have heq : (97 * (N : ℝ))⁻¹ * (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) =
      (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) / (97 * (N : ℝ)) := by ring
  rw [← heq]
  have hmul' := hmul
  rw [Real.rpow_neg (by positivity), Real.rpow_one] at hmul'
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'

private theorem entropyNumber_antitone_index {X : Type*} [PseudoEMetricSpace X]
    (K : Set X) {m n : ℕ} (hmn : m ≤ n) :
    HaarQuarter.TheoremD.entropyNumber n K ≤ HaarQuarter.TheoremD.entropyNumber m K := by
  unfold HaarQuarter.TheoremD.entropyNumber
  apply sInf_le_sInf
  intro ρ hρ
  rcases hρ with ⟨radius, hradius, hcover⟩
  refine ⟨radius, hradius, ?_⟩
  exact hcover.trans (by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.sub_le_sub_right hmn 1))

/-- Carl's finite dyadic cover and a sharp DKLL upper width bound yield the
matching entropy upper rate for all large indices. -/
theorem cameronMartin_entropy_upper_of_sharp_width_upper
    {d : ℕ} (hd : 2 ≤ d) (C : ℝ) (hC : 0 < C) (m₀ : ℕ) (hm₀ : 2 ≤ m₀)
    (hwidth : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (CameronMartin.KdUnitCube d) k ≤ ENNReal.ofReal (C * cmIndexRate d k)) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) ≤
        ENNReal.ofReal (C' * cmIndexRate d k) := by
  let α : ℝ := (d : ℝ) - 1 / 2
  let D : ℝ := (m₀ : ℝ) ^ 2 + 5 * C
  let C' : ℝ := 6208 * D
  let k₀ : ℕ := max (864 * m₀) 864
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C', hC', k₀, ?_⟩
  intro k hk
  let x : ℕ := k / 96 - 1
  let L : ℕ := Nat.log2 x
  let N : ℕ := 2 ^ L
  have hklarge : 864 * m₀ ≤ k := le_trans (Nat.le_max_left _ _) hk
  have hklarge2 : 864 ≤ k := le_trans (Nat.le_max_right _ _) hk
  have hxge : 8 * m₀ ≤ x := by dsimp [x]; omega
  have hx8 : 8 ≤ x := by dsimp [x]; omega
  have hxpos : x ≠ 0 := by omega
  have hNle : N ≤ x := by
    dsimp [N, L]
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hxpos
  have hxlt : x < 2 * N := by
    dsimp [N, L]
    have h := Nat.lt_pow_of_log_lt (by omega : 1 < 2)
      (Nat.lt_succ_self (Nat.log 2 x))
    simpa [Nat.pow_succ, Nat.log2_eq_log_two, Nat.mul_comm] using h
  have hNlo : 4 ≤ N := by omega
  have hm₀N : m₀ ≤ N := by omega
  have hidxle : 96 * N + 1 ≤ k := by
    have : N ≤ k / 96 - 1 := hNle
    omega
  have hidxlo : k / 4 ≤ 96 * N + 1 := by
    have hxlt' : k / 96 - 1 < 2 * N := by simpa [x] using hxlt
    omega
  have hNreal : 0 < (N : ℝ) := by positivity
  have hQ : 1 ≤ (Real.log (N : ℝ)) ^ α := by
    have hN3 : 3 ≤ N := by omega
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hlog : 1 ≤ Real.log (N : ℝ) := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (by positivity)
      have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
      exact le_trans hexp.le hN3R
    have hα : 1 ≤ α := by
      dsimp [α]
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    calc
      1 ≤ Real.log (N : ℝ) := hlog
      _ = (Real.log (N : ℝ)) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (Real.log (N : ℝ)) ^ α :=
        Real.rpow_le_rpow_of_exponent_le hlog hα
  have hLpos : 1 ≤ L := by
    by_contra hn
    have hL0 : L = 0 := by omega
    have hN1 : N = 1 := by simp [N, hL0]
    omega
  obtain ⟨B, hBformula, hBpos, hdyadic⟩ :=
    CarlRateExtraction.dyadic_width_budget_of_sharp_upper
      hd hm₀ hm₀N (by rfl) hLpos C hC hwidth
  have hwidthN := hwidth N hm₀N
  have hwidthFinite : HaarQuarter.TheoremD.Width.kolmogorovWidth
      (CameronMartin.KdUnitCube d) N ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwidthN
  let w : ℝ := (HaarQuarter.TheoremD.Width.kolmogorovWidth
    (CameronMartin.KdUnitCube d) N).toReal
  have hw : (HaarQuarter.TheoremD.Width.kolmogorovWidth
      (CameronMartin.KdUnitCube d) N).toReal ≤ C * cmIndexRate d N := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hwidthN
    have hrateNonneg := cmRate_nonneg hd (by omega : 2 ≤ N)
    have hnonneg : 0 ≤ C * cmIndexRate d N := mul_nonneg (le_of_lt hC) hrateNonneg
    simpa [ENNReal.toReal_ofReal hnonneg] using h
  have hrateN : cmIndexRate d N =
      (1 / (N : ℝ)) * (Real.log (N : ℝ)) ^ α := by
    unfold cmIndexRate logarithmicIndexRate
    rw [Real.rpow_neg hNreal.le, Real.rpow_one]
    dsimp [α]
    ring
  have hwterm : (N : ℝ) ^ 2 * w ≤ C * (N : ℝ) *
      (Real.log (N : ℝ)) ^ α := by
    calc
      _ ≤ (N : ℝ) ^ 2 * (C * cmIndexRate d N) :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = C * (N : ℝ) * (Real.log (N : ℝ)) ^ α := by rw [hrateN]; field_simp
  have hBbound : B ≤ D * (N : ℝ) *
      (Real.log (N : ℝ)) ^ α := by
    have hNident : (2 : ℝ) ^ L = (N : ℝ) := by norm_cast
    rw [hBformula, hNident]
    have hbase : (m₀ : ℝ) ^ 2 ≤ (m₀ : ℝ) ^ 2 * (N : ℝ) *
        (Real.log (N : ℝ)) ^ α := by
      have hm₀sq : 0 ≤ (m₀ : ℝ) ^ 2 := sq_nonneg _
      have hNge : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      have hNQ : 1 ≤ (N : ℝ) * (Real.log (N : ℝ)) ^ α := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hNQ hm₀sq]
    nlinarith [hbase, hwterm]
  have hCarl := CarlRateExtraction.entropy_le_of_dyadic_width_bound
    (K := CameronMartin.KdUnitCube d) B hBpos hdyadic
  have hCarlReal : 4 * B / (4 : ℝ) ^ L ≤
      4 * D * ((Real.log (N : ℝ)) ^ α / (N : ℝ)) := by
    have hpow : (4 : ℝ) ^ L = (N : ℝ) ^ 2 := by
      calc
        (4 : ℝ) ^ L = ((2 : ℝ) ^ 2) ^ L := by norm_num
        _ = (2 : ℝ) ^ (2 * L) := by rw [← pow_mul]
        _ = (2 : ℝ) ^ (L * 2) := by congr 1 <;> omega
        _ = ((2 : ℝ) ^ L) ^ 2 := by rw [← pow_mul]
        _ = (N : ℝ) ^ 2 := by rw [show (2 : ℝ) ^ L = (N : ℝ) by norm_cast]
    rw [hpow]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    rw [div_le_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)]
    field_simp [hN0]
    nlinarith [hBbound]
  have hCarlRate : 4 * B / (4 : ℝ) ^ L ≤
      1552 * D * cmIndexRate d (96 * N + 1) := by
    have hlow := cmIndexRate_lower_at_carl_index hd hNlo
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hratio : (Real.log (N : ℝ)) ^ α / (N : ℝ) =
        97 * ((Real.log (N : ℝ)) ^ α / (97 * (N : ℝ))) := by field_simp [hN0]
    calc
      _ ≤ 4 * D * ((Real.log (N : ℝ)) ^ α / (N : ℝ)) := hCarlReal
      _ = 388 * D * ((Real.log (N : ℝ)) ^ α / (97 * (N : ℝ))) := by rw [hratio]; ring
      _ ≤ 388 * D * cmIndexRate d (96 * N + 1) := by
        exact mul_le_mul_of_nonneg_left hlow (by positivity [D])
      _ ≤ 1552 * D * cmIndexRate d (96 * N + 1) := by
        have hratepos := cmRate_nonneg hd (by omega : 2 ≤ 96 * N + 1)
        dsimp [D]
        nlinarith [hC, sq_nonneg (m₀ : ℝ)]
  have hEntropyCarl :
      HaarQuarter.TheoremD.entropyNumber (96 * N + 1)
        (CameronMartin.KdUnitCube d) ≤
      ENNReal.ofReal (1552 * D * cmIndexRate d (96 * N + 1)) := by
    exact hCarl.trans (ENNReal.ofReal_le_ofReal hCarlRate)
  have hmono := entropyNumber_antitone_index
    (K := CameronMartin.KdUnitCube d) hidxle
  have hrateCompare : cmIndexRate d (96 * N + 1) ≤
      4 * cmIndexRate d k := by
    have hj : 2 ≤ 96 * N + 1 := by omega
    have hk2 : 2 ≤ k := by omega
    have hjR : (96 * N + 1 : ℕ) ≤ k := hidxle
    have hlog : Real.log ((96 * N + 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hjR)
    have hlog0 : 0 ≤ Real.log ((96 * N + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 96 * N + 1))
    have hpow : Real.log ((96 * N + 1 : ℕ) : ℝ) ^ ((d : ℝ) - 1 / 2) ≤
        Real.log (k : ℝ) ^ ((d : ℝ) - 1 / 2) :=
      Real.rpow_le_rpow hlog0 hlog (by
        have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith)
    have hinv : 1 / ((96 * N + 1 : ℕ) : ℝ) ≤ 4 / (k : ℝ) := by
      have hj4 : k ≤ (96 * N + 1) * 4 := by omega
      have hjLower : (k : ℝ) / 4 ≤ ((96 * N + 1 : ℕ) : ℝ) := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
        exact_mod_cast hj4
      have hrec := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (k : ℝ) / 4) hjLower
      have heq : 1 / ((k : ℝ) / 4) = 4 / (k : ℝ) := by field_simp
      rw [heq] at hrec
      exact hrec
    have hmul := mul_le_mul hinv hpow (by positivity) (by positivity)
    have hratej : cmIndexRate d (96 * N + 1) =
        ((96 * N + 1 : ℕ) : ℝ)⁻¹ * Real.log ((96 * N + 1 : ℕ) : ℝ) ^ ((d : ℝ) - 1 / 2) := by
      unfold cmIndexRate logarithmicIndexRate
      rw [Real.rpow_neg (by positivity), Real.rpow_one]
    have hratek : cmIndexRate d k =
        (k : ℝ)⁻¹ * Real.log (k : ℝ) ^ ((d : ℝ) - 1 / 2) := by
      unfold cmIndexRate logarithmicIndexRate
      rw [Real.rpow_neg (by positivity), Real.rpow_one]
    rw [hratej]
    calc
      _ ≤ 4 * (k : ℝ)⁻¹ * Real.log (k : ℝ) ^ ((d : ℝ) - 1 / 2) := by
        simpa [div_eq_mul_inv] using hmul
      _ = 4 * cmIndexRate d k := by rw [hratek]; ring
  have hfinal := le_trans hmono hEntropyCarl
  have hCscale : 1552 * D ≤ C' := by dsimp [C']; nlinarith [hC, sq_nonneg (m₀ : ℝ)]
  have hratejpos := cmRate_nonneg hd (by omega : 2 ≤ 96 * N + 1)
  have hfinalRate : 1552 * D * cmIndexRate d (96 * N + 1) ≤ C' * cmIndexRate d k := by
    calc
      _ ≤ 1552 * D * (4 * cmIndexRate d k) :=
        mul_le_mul_of_nonneg_left hrateCompare (by positivity [D])
      _ = C' * cmIndexRate d k := by dsimp [C', D]; ring
  exact hfinal.trans (ENNReal.ofReal_le_ofReal hfinalRate)

end BrownianSharp
