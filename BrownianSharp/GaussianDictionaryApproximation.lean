import BrownianSharp.GaussianKGGDictionary
import BrownianSharp.FiniteDictionaryReindex
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open scoped BigOperators RealInnerProductSpace ENNReal

namespace BrownianSharp.GaussianRIP

private def dictionaryLogScale (M : ℕ) : ℝ :=
  Real.log (258 * ((M : ℝ) + 1))

private theorem dictionaryLogScale_pos (M : ℕ) : 0 < dictionaryLogScale M := by
  apply Real.log_pos
  have hM : 0 ≤ (M : ℝ) := by positivity
  nlinarith

private theorem dictionaryLogScale_le (M : ℕ) :
    dictionaryLogScale M ≤ 9 * Real.log (2 * (M : ℝ) + 2) := by
  have hbase : 258 * ((M : ℝ) + 1) ≤ (2 * (M : ℝ) + 2) ^ 9 := by
    let X : ℝ := 2 * ((M : ℝ) + 1)
    have hX : 2 ≤ X := by
      dsimp [X]
      have hM : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
      nlinarith
    have hXpow : (2 : ℝ) ^ 8 ≤ X ^ 8 := by gcongr
    calc
      258 * ((M : ℝ) + 1) ≤ 512 * ((M : ℝ) + 1) := by nlinarith
      _ = 256 * X := by dsimp [X]; ring
      _ ≤ X * X ^ 8 := by
        have h := mul_le_mul_of_nonneg_left hXpow (show 0 ≤ X by linarith)
        norm_num at h ⊢
        nlinarith
      _ = X ^ 9 := by rw [pow_succ]; ring
      _ = (2 * (M : ℝ) + 2) ^ 9 := by congr 1 <;> ring
  calc
    dictionaryLogScale M ≤ Real.log ((2 * (M : ℝ) + 2) ^ 9) :=
      Real.log_le_log (by positivity) hbase
    _ = 9 * Real.log (2 * (M : ℝ) + 2) := by rw [Real.log_pow]; norm_num

private theorem dictionaryLogScale_ge_log_two (M : ℕ) :
    Real.log 2 ≤ dictionaryLogScale M := by
  apply Real.log_le_log (by norm_num)
  have hM : 0 ≤ (M : ℝ) := by positivity
  nlinarith

private theorem dictionary_target_log_pos (M : ℕ) :
    0 < Real.log (2 * (M : ℝ) + 2) := by
  apply Real.log_pos
  have hM : 0 ≤ (M : ℝ) := by positivity
  have : (2 : ℝ) ≤ 2 * (M : ℝ) + 2 := by nlinarith
  exact lt_of_lt_of_le (by norm_num) this

private theorem dictionary_rip_budget (M m s : ℕ) (hs : 1 ≤ s)
    (hlarge : 20000 * dictionaryLogScale M ≤ (m : ℝ))
    (hsupper : (s : ℝ) ≤ (m : ℝ) / (10000 * dictionaryLogScale M)) :
    ((M + 1) ^ s : ℝ) * (Nat.ceil (129 ^ s : ℝ) : ℝ) *
      (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1 := by
  have hscale : 0 < dictionaryLogScale M := dictionaryLogScale_pos M
  have hBpos : 0 < 258 * ((M : ℝ) + 1) := by positivity
  have hceil : (Nat.ceil (129 ^ s : ℝ) : ℝ) ≤ 2 * (129 : ℝ) ^ s := by
    have hpow : 1 ≤ (129 : ℝ) ^ s := one_le_pow₀ (by norm_num)
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ (129 : ℝ) ^ s by positivity)
    nlinarith
  have hcount : ((M + 1) ^ s : ℝ) * (Nat.ceil (129 ^ s : ℝ) : ℝ) ≤
      Real.exp ((s : ℝ) * dictionaryLogScale M) := by
    have hpow : 2 ≤ (2 : ℝ) ^ s := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (s - 1) := one_le_pow₀ (by norm_num)
      have hs' : 1 ≤ s := hs
      have heq : (2 : ℝ) ^ s = 2 * 2 ^ (s - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hs']
        rw [pow_add]
        ring
      rw [heq]
      nlinarith
    have hsum : ((M + 1) ^ s : ℝ) * (Nat.ceil (129 ^ s : ℝ) : ℝ) ≤
        (258 * ((M : ℝ) + 1)) ^ s := by
      calc
        _ ≤ ((M + 1 : ℝ) ^ s) * (2 * (129 : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_left hceil (by positivity)
        _ = 2 * (((M : ℝ) + 1) * 129) ^ s := by rw [mul_pow]; ring
        _ ≤ (2 : ℝ) ^ s * (((M : ℝ) + 1) * 129) ^ s :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = (2 * (((M : ℝ) + 1) * 129)) ^ s := by rw [← mul_pow]
        _ = (258 * ((M : ℝ) + 1)) ^ s := by congr 1; ring
    calc
      _ ≤ (258 * ((M : ℝ) + 1)) ^ s := hsum
      _ = Real.exp ((s : ℝ) * dictionaryLogScale M) := by
        rw [dictionaryLogScale, Real.exp_nat_mul, Real.exp_log hBpos]
  have hlogbudget : (s : ℝ) * dictionaryLogScale M ≤ (m : ℝ) / 10000 := by
    have hmul := mul_le_mul_of_nonneg_right hsupper hscale.le
    have hden : (10000 * dictionaryLogScale M) ≠ 0 := ne_of_gt (mul_pos (by norm_num) hscale)
    field_simp at hmul ⊢
    nlinarith
  have htail : Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100) ≤
      2 * Real.exp (-(m : ℝ) / 100) := by
    have harg : -(m : ℝ) / 16 ≤ -(m : ℝ) / 100 := by
      have hm : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    have he := Real.exp_le_exp.mpr harg
    linarith
  have hexp :
      Real.exp ((s : ℝ) * dictionaryLogScale M) *
        (2 * Real.exp (-(m : ℝ) / 100)) ≤
      2 * Real.exp (-((99 : ℝ) / 10000) * (m : ℝ)) := by
    have harg : (s : ℝ) * dictionaryLogScale M - (m : ℝ) / 100 ≤
        -((99 : ℝ) / 10000) * (m : ℝ) := by nlinarith [hlogbudget]
    calc
      _ = 2 * (Real.exp ((s : ℝ) * dictionaryLogScale M) *
          Real.exp (-(m : ℝ) / 100)) := by ring
      _ = 2 * Real.exp ((s : ℝ) * dictionaryLogScale M - (m : ℝ) / 100) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ 2 * Real.exp (-((99 : ℝ) / 10000) * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  have hlog2 : Real.log 2 ≤ dictionaryLogScale M := dictionaryLogScale_ge_log_two M
  have hstrong : Real.log 2 < ((99 : ℝ) / 10000) * (m : ℝ) := by
    have hm := hlarge
    have hLpos := hscale
    have hm' : (m : ℝ) ≥ 20000 * Real.log 2 := by nlinarith
    nlinarith [Real.log_two_gt_d9]
  have hfinal : 2 * Real.exp (-((99 : ℝ) / 10000) * (m : ℝ)) < 1 := by
    have he : Real.exp (-((99 : ℝ) / 10000) * (m : ℝ)) < Real.exp (-Real.log 2) :=
      Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (2 : ℝ) > 0)] at he
    nlinarith
  calc
    _ ≤ Real.exp ((s : ℝ) * dictionaryLogScale M) *
        (2 * Real.exp (-(m : ℝ) / 100)) := by
          exact mul_le_mul hcount htail (by positivity) (by positivity)
    _ ≤ 2 * Real.exp (-((99 : ℝ) / 10000) * (m : ℝ)) := hexp
    _ < 1 := hfinal

private theorem dictionary_floor_bounds (M m : ℕ)
    (hlarge : 20000 * dictionaryLogScale M ≤ (m : ℝ)) :
    let s : ℕ := ⌊(m : ℝ) / (10000 * dictionaryLogScale M)⌋₊
    1 ≤ s ∧
      (s : ℝ) ≤ (m : ℝ) / (10000 * dictionaryLogScale M) ∧
      (m : ℝ) / (20000 * dictionaryLogScale M) ≤ (s : ℝ) := by
  dsimp
  let q : ℝ := (m : ℝ) / (10000 * dictionaryLogScale M)
  have hq : 2 ≤ q := by
    dsimp [q]
    have hden : 0 < 10000 * dictionaryLogScale M :=
      mul_pos (by norm_num) (dictionaryLogScale_pos M)
    rw [le_div_iff₀ hden]
    nlinarith [hlarge]
  have hfloorlo := Nat.floor_le (show 0 ≤ q by positivity)
  have hfloorhi := Nat.self_sub_floor_lt_one (a := q)
  have hfloorpos : 1 ≤ ⌊q⌋₊ := by
    have : (1 : ℝ) ≤ (⌊q⌋₊ : ℝ) := by linarith
    exact_mod_cast this
  have hhalf : q / 2 ≤ (⌊q⌋₊ : ℝ) := by nlinarith
  exact ⟨hfloorpos, by simpa [q] using hfloorlo,
    by
      have hqeq : q / 2 = (m : ℝ) / (20000 * dictionaryLogScale M) := by
        dsimp [q]
        ring
      simpa [hqeq] using hhalf⟩

/-- Unconditional finite dictionary KGG estimate. A sparse Gaussian embedding is
used when the target rank exceeds a fixed multiple of `log M`; at smaller
ranks the zero subspace already has the required logarithmic error. -/
theorem finDictionaryApproximation_gaussian :
    BrownianSharp.FinDictionaryApproximation 10000 := by
  intro N M m v R hR hbound
  classical
  by_cases hsmall : (m : ℝ) < 20000 * dictionaryLogScale M
  · refine ⟨⊥, ?_, ?_⟩
    · simp
    · intro x hx
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hnorm : ‖WithLp.toLp ∞ (fun i : Fin M => inner ℝ x (v i))‖ ≤ R := by
        by_cases hM : M = 0
        · subst M
          simp [PiLp.norm_eq_ciSup, hR]
        · letI : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero hM⟩⟩
          rw [PiLp.norm_eq_ciSup]
          apply ciSup_le
          intro i
          simp only [PiLp.toLp_apply]
          rw [Real.norm_eq_abs]
          calc
            |inner ℝ x (v i)| ≤ ‖x‖ * ‖v i‖ := abs_real_inner_le_norm _ _
            _ ≤ 1 * R := mul_le_mul hx (hbound i) (norm_nonneg _) (by norm_num)
            _ = R := one_mul _
      have hlogbound : (m : ℝ) + 1 ≤ 180018 * Real.log (2 * (M : ℝ) + 2) := by
        have hL := dictionaryLogScale_le M
        have hLlower := dictionaryLogScale_ge_log_two M
        have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
          linarith [Real.log_two_gt_d9]
        have hlogpos := dictionary_target_log_pos M
        have hone : (1 : ℝ) ≤ 2 * dictionaryLogScale M := by
          have := dictionaryLogScale_ge_log_two M
          linarith [Real.log_two_gt_d9]
        calc
          (m : ℝ) + 1 ≤ 20000 * dictionaryLogScale M + 1 := by linarith
          _ ≤ 20002 * dictionaryLogScale M := by nlinarith
            _ ≤ 180018 * Real.log (2 * (M : ℝ) + 2) := by nlinarith [hL]
      have hsqrt : (1 : ℝ) ≤ 10000 * Real.sqrt
          (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := by
        have hnum := dictionary_target_log_pos M
        have hden : 0 < (m : ℝ) + 1 := by positivity
        have hfrac : (1 / 180018 : ℝ) ≤
            Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1) := by
          rw [le_div_iff₀ hden]
          nlinarith [hlogbound]
        have hsqrtnonneg : 0 ≤ Real.sqrt
            (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := Real.sqrt_nonneg _
        have hsqrtlower : Real.sqrt (1 / 180018 : ℝ) ≤ Real.sqrt
            (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := Real.sqrt_le_sqrt hfrac
        have hnumcmp : (1 : ℝ) ≤ 10000 * Real.sqrt (1 / 180018 : ℝ) := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
          rw [show 10000 * (1 / Real.sqrt 180018) =
              10000 / Real.sqrt 180018 by ring]
          rw [one_le_div_iff]
          left
          constructor
          · exact Real.sqrt_pos.2 (by norm_num)
          · have hsqrtle : Real.sqrt 180018 ≤ 10000 := by
              nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 180018)]
            exact hsqrtle
        nlinarith
      calc
        ‖WithLp.toLp ∞ (fun i : Fin M => inner ℝ x (v i)) - 0‖ ≤ R := by simpa using hnorm
        _ ≤ 10000 * R * Real.sqrt
            (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := by
          calc
            R = 1 * R := by ring
            _ ≤ (10000 * Real.sqrt
                (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1))) * R :=
              mul_le_mul_of_nonneg_right hsqrt hR
            _ = _ := by ring
  · have hlarge : 20000 * dictionaryLogScale M ≤ (m : ℝ) := le_of_not_gt hsmall
    let s : ℕ := ⌊(m : ℝ) / (10000 * dictionaryLogScale M)⌋₊
    have hsdata := dictionary_floor_bounds M m hlarge
    have hs : 1 ≤ s := by simpa [s] using hsdata.1
    have hsupper : (s : ℝ) ≤ (m : ℝ) / (10000 * dictionaryLogScale M) := by
      simpa [s] using hsdata.2.1
    have hslower : (m : ℝ) / (20000 * dictionaryLogScale M) ≤ (s : ℝ) := by
      simpa [s] using hsdata.2.2
    have hbudget := dictionary_rip_budget M m s hs hlarge hsupper
    by_cases hRpos : R = 0
    · refine ⟨⊥, ?_, ?_⟩
      · simp
      · intro x hx
        refine ⟨0, Submodule.zero_mem _, ?_⟩
        have hv0 : ∀ i, v i = 0 := by
          intro i
          have := hbound i
          rw [hRpos] at this
          exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
        have hfeature : dictionaryFeatureMap v x = 0 := by
          ext i
          simp [dictionaryFeatureMap_apply_coord, hv0]
        have hval : WithLp.toLp ∞ (fun i : Fin M => inner ℝ x (v i)) = 0 := by
          ext i
          simp [hv0]
        simp [hval, hRpos]
    · have hRstrict : 0 < R := lt_of_le_of_ne hR (Ne.symm hRpos)
      have hden : 0 < (m : ℝ) := by
        have hLpos := dictionaryLogScale_pos M
        nlinarith [hlarge]
      obtain ⟨V, hVrank, hVapprox⟩ := exists_dictionary_width_subspace
        (m := m) (N := N) (M := M) (s := s) (by exact_mod_cast hden) hs v R hRstrict hbound hbudget
      refine ⟨V, hVrank, ?_⟩
      intro x hx
      obtain ⟨y, hy, herr⟩ := hVapprox x hx
      refine ⟨y, hy, ?_⟩
      have hlog := dictionaryLogScale_le M
      have hlogpos := dictionary_target_log_pos M
      have hrecip : 1 / (s : ℝ) ≤
          360000 * Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1) := by
        have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
        have hmpos : 0 < (m : ℝ) := by positivity
        have hL := dictionaryLogScale_le M
        have hrecip0 : 1 / (s : ℝ) ≤ 20000 * dictionaryLogScale M / (m : ℝ) := by
          rw [div_le_div_iff₀ hspos hmpos]
          have hlower' : (m : ℝ) ≤ 20000 * dictionaryLogScale M * (s : ℝ) := by
            simpa [mul_comm] using
              (div_le_iff₀ (mul_pos (by norm_num) (dictionaryLogScale_pos M))).mp hslower
          nlinarith [hlower']
        have hmone : 1 ≤ (m : ℝ) := by
          exact_mod_cast hmpos
        have hmplus : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by nlinarith
        calc
          1 / (s : ℝ) ≤ 20000 * dictionaryLogScale M / (m : ℝ) := hrecip0
          _ ≤ 180000 * Real.log (2 * (M : ℝ) + 2) / (m : ℝ) := by
            apply (div_le_div_iff₀ hmpos hmpos).2
            nlinarith [hL]
          _ ≤ 360000 * Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1) := by
            apply (div_le_div_iff₀ hmpos (by positivity)).2
            have hmul := mul_le_mul_of_nonneg_left hmplus
              (mul_nonneg (le_of_lt hlogpos) (by norm_num : (0 : ℝ) ≤ 180000))
            nlinarith
      have hscale : 2 * (Real.sqrt 50 * R / Real.sqrt (s : ℝ)) ≤
          10000 * R * Real.sqrt
            (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := by
        have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
        have hlogpos := dictionary_target_log_pos M
        have hr := Real.sqrt_le_sqrt hrecip
        have hsqrtid : Real.sqrt (1 / (s : ℝ)) = 1 / Real.sqrt (s : ℝ) := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
        have hconst : 2 * Real.sqrt 50 * Real.sqrt 360000 ≤ 10000 := by
          have hs50 : Real.sqrt 50 ≤ 8 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 50)]
          have hs360 : Real.sqrt 360000 = 600 := by
            apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
            norm_num
          rw [hs360]
          nlinarith [hs50]
        have hr' : Real.sqrt (1 / (s : ℝ)) ≤
            Real.sqrt 360000 * Real.sqrt
              (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := by
          have heq : 360000 * Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1) =
              360000 * (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := by ring
          rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 360000)] at hr
          exact hr
        calc
          2 * (Real.sqrt 50 * R / Real.sqrt (s : ℝ)) =
              2 * Real.sqrt 50 * R * Real.sqrt (1 / (s : ℝ)) := by
                rw [hsqrtid]
                ring
          _ ≤ 2 * Real.sqrt 50 * R * (Real.sqrt 360000 * Real.sqrt
              (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1))) :=
                mul_le_mul_of_nonneg_left hr' (by positivity)
          _ ≤ 10000 * R * Real.sqrt
              (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1)) := by
                have hmul := mul_le_mul_of_nonneg_right hconst
                  (mul_nonneg hR (Real.sqrt_nonneg
                    (Real.log (2 * (M : ℝ) + 2) / ((m : ℝ) + 1))))
                nlinarith
      exact herr.trans hscale

end BrownianSharp.GaussianRIP

end
