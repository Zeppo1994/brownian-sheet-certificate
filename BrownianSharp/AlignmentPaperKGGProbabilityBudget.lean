import BrownianSharp.GaussianKGGDictionary
import Mathlib.Tactic

/-! Explicit logarithmic rank conditions for the already proved finite
Gaussian dictionary theorem. No probabilistic assertion is imported here. -/
noncomputable section
namespace BrownianSharp.AlignmentPaperKGGProbabilityBudget

/-- Rank of order s log(M+1) makes the exact finite dictionary failure budget
strictly less than one. The numerical constant is deliberately inessential. -/
theorem dictionary_budget_lt_one {M m s : ℕ} (hs : 1 ≤ s)
    (hm : 200*(s:ℝ)*(Real.log ((M:ℝ)+1)+Real.log 129+1) ≤ (m:ℝ)) :
    ((M+1)^s:ℝ) * (Nat.ceil (129^s:ℝ):ℝ) *
      (Real.exp (-(m:ℝ)/16)+Real.exp (-(m:ℝ)/100)) < 1 := by
  have hM : 0 < (M:ℝ)+1 := by positivity
  have hM1 : 1 ≤ (M:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have hlogM : 0 ≤ Real.log ((M:ℝ)+1) := Real.log_nonneg hM1
  have hlog129 : 0 ≤ Real.log (129:ℝ) := Real.log_nonneg (by norm_num)
  have hsR : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have hs0 : 0 ≤ (s:ℝ) := by positivity
  have hceil : (Nat.ceil (129^s:ℝ):ℝ) = (129:ℝ)^s := by
    rw [show (129:ℝ)^s = ((129^s:ℕ):ℝ) by norm_cast, Nat.ceil_natCast]
  rw [hceil]
  let L : ℝ := Real.log ((M:ℝ)+1)+Real.log 129
  have hL : 0 ≤ L := add_nonneg hlogM hlog129
  have hexp : ((M+1)^s:ℝ)*(129:ℝ)^s = Real.exp ((s:ℝ)*L) := by
    rw [show (s:ℝ)*L = (s:ℝ)*Real.log ((M:ℝ)+1)+
        (s:ℝ)*Real.log 129 by dsimp [L]; ring, Real.exp_add,
      Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hM, Real.exp_log (by norm_num : (0:ℝ)<129)]
  rw [hexp]
  have hdecay : Real.exp (-(m:ℝ)/16) ≤ Real.exp (-(m:ℝ)/100) := by
    apply Real.exp_le_exp.mpr
    have : (0:ℝ) ≤ (m:ℝ) := by positivity
    linarith
  have harg : (s:ℝ)*L - (m:ℝ)/100 ≤ -2 := by
    change 200*(s:ℝ)*(L+1) ≤ (m:ℝ) at hm
    have hprod : 0 ≤ (s:ℝ)*L := mul_nonneg hs0 hL
    nlinarith
  have hfinal : 2*Real.exp (-2) < 1 := by
    have hlarge := Real.add_one_le_exp (2:ℝ)
    have hprod : Real.exp (-2)*Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hpos := Real.exp_pos (-2:ℝ)
    nlinarith
  calc
    Real.exp ((s:ℝ)*L) *
        (Real.exp (-(m:ℝ)/16)+Real.exp (-(m:ℝ)/100)) ≤
      Real.exp ((s:ℝ)*L) * (2*Real.exp (-(m:ℝ)/100)) := by
        gcongr
        linarith
    _ = 2*Real.exp ((s:ℝ)*L - (m:ℝ)/100) := by
      rw [show -(m:ℝ)/100 = -((m:ℝ)/100) by ring, Real.exp_sub, Real.exp_neg]
      ring
    _ ≤ 2*Real.exp (-2) := by gcongr
    _ < 1 := hfinal

/-- Choose the sparsity parameter from an actual available rank, retaining
both a strict probability budget and the lower bound needed for its error. -/
theorem exists_dictionary_budget_parameter {M m : ℕ}
    (hm : 400*(Real.log ((M:ℝ)+1)+Real.log 129+1) ≤ (m:ℝ)) :
    ∃ s : ℕ, 1 ≤ s ∧
      (m:ℝ)/(400*(Real.log ((M:ℝ)+1)+Real.log 129+1)) ≤ (s:ℝ) ∧
      ((M+1)^s:ℝ) * (Nat.ceil (129^s:ℝ):ℝ) *
        (Real.exp (-(m:ℝ)/16)+Real.exp (-(m:ℝ)/100)) < 1 := by
  let L : ℝ := Real.log ((M:ℝ)+1)+Real.log 129+1
  have hlogM : 0 ≤ Real.log ((M:ℝ)+1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hlog129 : 0 ≤ Real.log (129:ℝ) := Real.log_nonneg (by norm_num)
  have hL : 0 < L := by dsimp [L]; linarith
  let x : ℝ := (m:ℝ)/(200*L)
  let s : ℕ := Nat.floor x
  have hx2 : 2 ≤ x := by
    apply (le_div_iff₀ (by positivity : 0 < 200*L)).2
    change 400*L ≤ (m:ℝ) at hm
    nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hfloor : (s:ℝ) ≤ x := Nat.floor_le hx0
  have hfloorLower : x < (s:ℝ)+1 := Nat.lt_floor_add_one x
  have hs : 1 ≤ s := by
    apply (Nat.le_floor_iff' (by norm_num : (1:ℕ) ≠ 0)).2
    norm_num only [Nat.cast_one]
    linarith
  have hbudget : 200*(s:ℝ)*L ≤ (m:ℝ) := by
    have hmuls := (mul_le_mul_of_nonneg_right hfloor
      (show 0 ≤ 200*L by positivity))
    have hxeq : x*(200*L) = (m:ℝ) := by
      dsimp [x]
      exact div_mul_cancel₀ _ (by positivity)
    rw [hxeq] at hmuls
    nlinarith
  refine ⟨s,hs,?_,dictionary_budget_lt_one hs hbudget⟩
  have hratio : (m:ℝ)/(400*L) = x/2 := by
    dsimp [x]
    field_simp
    <;> ring
  change (m:ℝ)/(400*L) ≤ (s:ℝ)
  rw [hratio]
  linarith

end BrownianSharp.AlignmentPaperKGGProbabilityBudget
