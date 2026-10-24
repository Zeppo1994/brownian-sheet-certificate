import BrownianSharp.AlignmentEndpointWidthExtraction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open BrownianSharp

namespace BrownianSharp.AlignmentEndpointRateInverse

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

/-- Invert a power-log rate with explicit uniform constants. The chosen index
is a ceiling of a small multiple of the target scale; its logarithm stays
between fixed multiples of `log (1/ε)`. -/
theorem exists_index_for_power_log_rate
    {s a c : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hc : 0 < c)
    (k₀ : ℕ) :
    ∃ b ε₀ : ℝ, 0 < b ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ k : ℕ, max 2 k₀ ≤ k ∧
        b * (ε⁻¹)^(1/s) * (Real.log ε⁻¹)^(a/s) ≤ (k:ℝ) ∧
        ε ≤ c * (k:ℝ)^(-s) * (Real.log (k:ℝ))^a := by
  let θ : ℝ := c * (2*s)^(-a)
  let b : ℝ := min (1/2) (θ^(1/s)/2)
  have hθ : 0<θ := by
    dsimp [θ]
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hb : 0<b := by
    dsimp [b]
    exact lt_min (by norm_num) (div_pos (Real.rpow_pos_of_pos hθ _) (by norm_num))
  have hbhalf : b≤1/2 := min_le_left _ _
  have hbθ : (2*b)^s≤θ := by
    have h2b : 0≤2*b := by positivity
    have hle : 2*b≤θ^(1/s) := by
      dsimp [b]
      have := min_le_right (1/2) (θ^(1/s)/2)
      nlinarith
    have hpow := Real.rpow_le_rpow h2b hle hs.le
    have heq : (θ^(1/s))^s=θ := by
      rw [← Real.rpow_mul hθ.le]
      rw [show (1/s)*s=1 by field_simp, Real.rpow_one]
    rw [heq] at hpow
    exact hpow
  have hconst : (2*b)^s*(2*s)^a≤c := by
    have h2s : 0<2*s := by positivity
    have hpowpos : 0<(2*s)^a := Real.rpow_pos_of_pos h2s _
    have hθeq : θ*(2*s)^a=c := by
      dsimp [θ]
      rw [Real.rpow_neg (by positivity)]
      field_simp
    calc
      (2*b)^s*(2*s)^a≤θ*(2*s)^a :=
        mul_le_mul_of_nonneg_right hbθ (by positivity)
      _=c := hθeq
  let K : ℕ := max 2 k₀
  let L₀ : ℝ := max 1 (max (-2*s*Real.log b) (s*Real.log ((K:ℝ)/b)))
  let ε₀ : ℝ := Real.exp (-L₀)
  refine ⟨b,ε₀,hb,Real.exp_pos _,?_⟩
  intro ε hε hε₀
  let L : ℝ := Real.log ε⁻¹
  let T : ℝ := (ε⁻¹)^(1/s)*L^(a/s)
  have hL₀ : L₀≤L := by
    have hεbound : ε≤Real.exp (-L₀) := by simpa [ε₀] using hε₀
    have hlogε : Real.log ε≤-L₀ := by
      calc
        Real.log ε≤Real.log (Real.exp (-L₀)) :=
          Real.log_le_log hε hεbound
        _=-L₀ := Real.log_exp _
    dsimp [L]
    rw [Real.log_inv]
    linarith
  have hL1 : 1≤L := le_trans (le_max_left _ _) hL₀
  have hLpos : 0<L := by linarith
  have hLlog : Real.log L≤L := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hLneglogb : -2*s*Real.log b≤L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL₀)
  have hLKlog : s*Real.log ((K:ℝ)/b)≤L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL₀)
  have hTpos : 0<T := by
    dsimp [T]
    exact mul_pos (Real.rpow_pos_of_pos (inv_pos.mpr hε) _) (Real.rpow_pos_of_pos hLpos _)
  have hTlower : Real.exp (L/s)≤T := by
    have hpowL : 1≤L^(a/s) := Real.one_le_rpow hL1 (by positivity)
    have hexp : Real.exp (L/s)=(ε⁻¹)^(1/s) := by
      rw [Real.rpow_def_of_pos (inv_pos.mpr hε)]
      congr 1
      dsimp [L]
      rw [Real.log_inv]
      ring
    rw [hexp]
    dsimp [T]
    nlinarith [mul_nonneg (by positivity : 0≤(ε⁻¹)^(1/s)) (sub_nonneg.mpr hpowL)]
  have hKlower : (K:ℝ)≤b*T := by
    have harg : Real.log ((K:ℝ)/b)≤L/s := by
      exact (le_div_iff₀ hs).2 (by simpa [mul_comm] using hLKlog)
    have hexp : ((K:ℝ)/b)≤Real.exp (L/s) := by
      rw [← Real.exp_log (div_pos (by exact_mod_cast (show 0<K by dsimp [K]; omega)) hb)]
      exact Real.exp_le_exp.mpr harg
    have hmul : (K:ℝ)≤b*Real.exp (L/s) := by
      have := mul_le_mul_of_nonneg_left hexp hb.le
      have hbneq : b≠0 := ne_of_gt hb
      field_simp at this ⊢
      nlinarith
    exact hmul.trans (mul_le_mul_of_nonneg_left hTlower hb.le)
  have hTge1 : 1≤b*T := by
    have hK1 : (1:ℝ)≤(K:ℝ) := by exact_mod_cast (by dsimp [K]; omega : 1≤K)
    exact hK1.trans hKlower
  let k : ℕ := ⌈b*T⌉₊
  have hklo : b*T≤(k:ℝ) := by dsimp [k]; exact Nat.le_ceil _
  have hkup : (k:ℝ)≤2*b*T := by
    have hceil := Nat.ceil_lt_add_one (show 0≤b*T by positivity)
    have hkR : (k:ℝ)<b*T+1 := by simpa [k] using hceil
    nlinarith [hTge1]
  have hkK : K≤k := by
    have hKle : (K:ℝ)≤(k:ℝ) := hKlower.trans hklo
    exact_mod_cast hKle
  have hk2 : 2≤k := (le_max_left _ _).trans hkK
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hlogklo : L/(2*s)≤Real.log (k:ℝ) := by
    have hblow : b*Real.exp (L/s)≤(k:ℝ) :=
      (mul_le_mul_of_nonneg_left hTlower hb.le).trans hklo
    have hlogmono := Real.log_le_log (mul_pos hb (Real.exp_pos _)) hblow
    have hlogmul : Real.log (b*Real.exp (L/s))=Real.log b+L/s := by
      rw [Real.log_mul hb.ne' (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    rw [hlogmul] at hlogmono
    have hLcond : -2*s*Real.log b≤L := hLneglogb
    have hquot : -Real.log b≤L/(2*s) := by
      apply (le_div_iff₀ (by positivity : 0<2*s)).2
      nlinarith [hLcond]
    have hdiff : L/s-L/(2*s)=L/(2*s) := by field_simp; ring
    calc
      L/(2*s) = L/s-L/(2*s) := by rw [hdiff]
      _ ≤ Real.log b+L/s := by linarith
      _ ≤ Real.log (k:ℝ) := hlogmono
  have hlogkpos : 0<Real.log (k:ℝ) := by
    have hspos : 0<2*s := by positivity
    exact (div_pos hLpos hspos).trans_le hlogklo
  have hlogkhi : Real.log (k:ℝ)≤((1+a)/s)*L := by
    have hkup' : (k:ℝ)≤T := by
      have h2b : 2*b≤1 := by nlinarith [hbhalf]
      calc
        (k:ℝ)≤2*b*T := hkup
        _≤T := by nlinarith [hTpos,h2b]
    have hlogmono := Real.log_le_log hkpos hkup'
    have hlogT : Real.log T=(1/s)*L+(a/s)*Real.log L := by
      dsimp [T]
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (inv_pos.mpr hε) _))
        (ne_of_gt (Real.rpow_pos_of_pos hLpos _)),
        Real.log_rpow (inv_pos.mpr hε), Real.log_rpow hLpos, Real.log_inv]
      have hLexpr : L=-Real.log ε := by
        dsimp [L]
        rw [Real.log_inv]
      rw [hLexpr]
    rw [hlogT] at hlogmono
    have hnum : L+a*Real.log L≤(1+a)*L := by nlinarith [ha,hLlog]
    have hrateNum : (L+a*Real.log L)/s≤((1+a)*L)/s :=
      div_le_div_of_nonneg_right hnum (le_of_lt hs)
    have heq : (1/s)*L+(a/s)*Real.log L=(L+a*Real.log L)/s := by field_simp
    calc
      Real.log (k:ℝ)≤(1/s)*L+(a/s)*Real.log L := hlogmono
      _=(L+a*Real.log L)/s := heq
      _≤((1+a)*L)/s := hrateNum
      _=((1+a)/s)*L := by ring
  have hTpow : T^s=ε⁻¹*L^a := by
    dsimp [T]
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
    rw [show (1/s)*s=1 by field_simp, show (a/s)*s=a by field_simp]
    simp
  have hkpown : (2*b*T)^(-s)≤(k:ℝ)^(-s) := by
    have hkpow : (k:ℝ)^s≤(2*b*T)^s :=
      Real.rpow_le_rpow hkpos.le hkup hs.le
    have hpos1 : 0<(k:ℝ)^s := Real.rpow_pos_of_pos hkpos _
    have hpos2 : 0<(2*b*T)^s := Real.rpow_pos_of_pos (by positivity) _
    have hinv : 1/((2*b*T)^s)≤1/((k:ℝ)^s) :=
      (one_div_le_one_div hpos2 hpos1).2 hkpow
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    simpa [one_div] using hinv
  have hlogpow : (L/(2*s))^a≤(Real.log (k:ℝ))^a :=
    Real.rpow_le_rpow (by positivity) hlogklo ha
  have hrateLower : ε≤c*(k:ℝ)^(-s)*(Real.log (k:ℝ))^a := by
    have hprod : ε≤c*(2*b*T)^(-s)*(L/(2*s))^a := by
      have hconst' : (2*b)^s*(2*s)^a≤c := hconst
      have hTpow' : (2*b*T)^s=(2*b)^s*(ε⁻¹*L^a) := by
        rw [Real.mul_rpow (by positivity) (by positivity), hTpow]
      have hmain : (2*b*T)^(-s)*(L/(2*s))^a =
          ε/((2*b)^s*(2*s)^a) := by
        rw [Real.rpow_neg (by positivity), hTpow', Real.div_rpow (by positivity) (by positivity)]
        field_simp
      have hden : 0<(2*b)^s*(2*s)^a := mul_pos (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_pos_of_pos (by positivity) _)
      have hcoef : ε≤c*(ε/((2*b)^s*(2*s)^a)) := by
        field_simp
        nlinarith [hconst']
      calc
        ε≤c*(ε/((2*b)^s*(2*s)^a)) := hcoef
        _=c*(2*b*T)^(-s)*(L/(2*s))^a := by rw [← hmain]; ring
    calc
      ε≤c*(2*b*T)^(-s)*(L/(2*s))^a := hprod
      _≤c*(k:ℝ)^(-s)*(L/(2*s))^a := by
        calc
          _ = (c*(2*b*T)^(-s))*(L/(2*s))^a := by ring
          _ ≤ (c*(k:ℝ)^(-s))*(L/(2*s))^a :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkpown hc.le) (by positivity)
          _ = _ := by ring
      _≤c*(k:ℝ)^(-s)*(Real.log (k:ℝ))^a :=
        mul_le_mul_of_nonneg_left hlogpow (by positivity)
  refine ⟨k,?_,?_ ,hrateLower⟩
  · simpa [K] using hkK
  · calc
      b*(ε⁻¹)^(1/s)*(Real.log ε⁻¹)^(a/s) = b*((ε⁻¹)^(1/s)*(Real.log ε⁻¹)^(a/s)) := by ring
      _≤(k:ℝ) := by simpa [T,L] using hklo

end
end BrownianSharp.AlignmentEndpointRateInverse
