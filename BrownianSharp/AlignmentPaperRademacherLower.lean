import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-! Finite sign averages for the square-function lower-moment estimate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace BrownianSharp.AlignmentPaperRademacherLower

def sign (b : Bool) : ℝ := if b then 1 else -1

def signRow {n : ℕ} (a : Fin n → ℝ) (ε : Fin n → Bool) : ℝ :=
  ∑ i, a i * sign (ε i)

theorem expect_bool (F : Bool → ℝ) :
    (𝔼 b : Bool, F b) = (F false + F true)/2 := by
  norm_num [Finset.expect, NNRat.smul_def]
  ring

theorem signRow_cons {n : ℕ} (a : Fin (n+1) → ℝ)
    (b : Bool) (ε : Fin n → Bool) :
    signRow a (Fin.cons b ε) = a 0 * sign b + signRow (fun i => a i.succ) ε := by
  simp [signRow, Fin.sum_univ_succ]

theorem expect_signs_succ {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ) :
    (𝔼 ε : Fin (n+1) → Bool, F ε) =
      𝔼 ε : Fin n → Bool, (F (Fin.cons false ε) + F (Fin.cons true ε))/2 := by
  let e : (Bool × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) :=
    Fin.insertNthEquiv (fun _ => Bool) 0
  have he : (𝔼 ε : Fin (n+1) → Bool, F ε) =
      𝔼 z : Bool × (Fin n → Bool), F (Fin.cons z.1 z.2) := by
    apply Fintype.expect_equiv e.symm
    intro ε
    congr 1
    change ε = Fin.cons (ε 0) (fun i => ε i.succ)
    exact (Fin.cons_self_tail ε).symm
  rw [he]
  have hprod := Finset.expect_product (Finset.univ : Finset Bool)
    (Finset.univ : Finset (Fin n → Bool))
    (fun z => F (Fin.cons z.1 z.2))
  rw [Finset.univ_product_univ] at hprod
  rw [hprod, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro ε _hε
  exact expect_bool (fun b => F (Fin.cons b ε))

theorem signRow_second_moment {n : ℕ} (a : Fin n → ℝ) :
    (𝔼 ε : Fin n → Bool, signRow a ε ^ 2) = ∑ i, a i ^ 2 := by
  induction n with
  | zero => simp [signRow]
  | succ n ih =>
    rw [expect_signs_succ]
    have heq : (fun ε : Fin n → Bool =>
        (signRow a (Fin.cons false ε)^2 + signRow a (Fin.cons true ε)^2)/2) =
        (fun ε => a 0^2 + signRow (fun i => a i.succ) ε ^ 2) := by
      funext ε
      rw [signRow_cons, signRow_cons]
      simp only [sign, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [heq, Finset.expect_add_distrib, Fintype.expect_const, ih, Fin.sum_univ_succ]

theorem signRow_fourth_moment_le {n : ℕ} (a : Fin n → ℝ) :
    (𝔼 ε : Fin n → Bool, signRow a ε ^ 4) ≤ 3 * (∑ i, a i ^ 2) ^ 2 := by
  induction n with
  | zero => simp [signRow]
  | succ n ih =>
    rw [expect_signs_succ]
    have heq : (fun ε : Fin n → Bool =>
        (signRow a (Fin.cons false ε)^4 + signRow a (Fin.cons true ε)^4)/2) =
        (fun ε => a 0^4 + 6*a 0^2*signRow (fun i => a i.succ) ε ^ 2 +
          signRow (fun i => a i.succ) ε ^ 4) := by
      funext ε
      rw [signRow_cons, signRow_cons]
      simp only [sign, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [heq]
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect,
      Fintype.expect_const, signRow_second_moment, Fin.sum_univ_succ]
    have h := ih (fun i => a i.succ)
    nlinarith [sq_nonneg (a 0 ^ 2)]

/-- A finite second/fourth-moment argument gives a lower mass bound on
values at least half the second moment. -/
theorem finite_second_fourth_tail_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {v : ℝ} (hv : 0 < v)
    (h₂ : (𝔼 ε : Ω, f ε ^ 2) = v)
    (h₄ : (𝔼 ε : Ω, f ε ^ 4) ≤ 3*v^2) :
    (1/12 : ℝ) ≤ 𝔼 ε : Ω, if v/2 ≤ f ε^2 then (1 : ℝ) else 0 := by
  classical
  let w : Ω → ℝ := fun ε => if v/2 ≤ f ε^2 then 1 else 0
  let u : Ω → ℝ := fun ε => if v/2 ≤ f ε^2 then f ε^2 else 0
  let l : Ω → ℝ := fun ε => if v/2 ≤ f ε^2 then 0 else f ε^2
  let e : ℝ := 𝔼 ε : Ω, w ε
  have he : 0 ≤ e := Finset.expect_nonneg (fun ε _ => by dsimp [w]; split_ifs <;> positivity)
  have hlow : (𝔼 ε : Ω, l ε) ≤ v/2 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro ε _
    dsimp [l]
    split_ifs with h
    · exact (half_pos hv).le
    · exact (lt_of_not_ge h).le
  have hsplit : (𝔼 ε : Ω, f ε^2) = (𝔼 ε : Ω, u ε) + 𝔼 ε : Ω, l ε := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro ε _
    dsimp [u,l]
    split_ifs <;> ring
  have hu : v/2 ≤ 𝔼 ε : Ω, u ε := by linarith only [h₂, hsplit, hlow]
  have hc := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
    (fun ε => f ε^2) w
  have hleft : (𝔼 ε : Ω, f ε^2*w ε) = 𝔼 ε : Ω, u ε := by
    apply Finset.expect_congr rfl
    intro ε _
    dsimp [u,w]
    split_ifs <;> ring
  have hright : (𝔼 ε : Ω, w ε^2) = e := by
    apply Finset.expect_congr rfl
    intro ε _
    dsimp [w]
    split_ifs <;> norm_num
  rw [hleft, hright] at hc
  have hfour : (𝔼 ε : Ω, (f ε^2)^2) ≤ 3*v^2 := by
    simpa only [← pow_mul] using h₄
  have hbound : (𝔼 ε : Ω, u ε)^2 ≤ 3*v^2*e :=
    hc.trans (mul_le_mul_of_nonneg_right hfour he)
  have hsquare : (v/2)^2 ≤ (𝔼 ε : Ω, u ε)^2 :=
    (sq_le_sq₀ (half_pos hv).le (by linarith only [hu,hv])).2 hu
  have hscaled : v^2*(1/4 : ℝ) ≤ v^2*(3*e) := by nlinarith only [hsquare,hbound]
  have hcancel : (1/4 : ℝ) ≤ 3*e :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hv)).mp hscaled
  change (1/12 : ℝ) ≤ e
  linarith

theorem finite_moment_lower_of_second_fourth {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {v p : ℝ} (hv : 0 < v) (hp : 0 < p)
    (h₂ : (𝔼 ε : Ω, f ε ^ 2) = v)
    (h₄ : (𝔼 ε : Ω, f ε ^ 4) ≤ 3*v^2) :
    v^(p/2) ≤ (12*(2 : ℝ)^(p/2)) * (𝔼 ε : Ω, |f ε|^p) := by
  classical
  let w : Ω → ℝ := fun ε => if v/2 ≤ f ε^2 then 1 else 0
  let amp : ℝ := (v/2)^(p/2)
  have hamp : 0 ≤ amp := Real.rpow_nonneg (half_pos hv).le _
  have htail : (1/12 : ℝ) ≤ 𝔼 ε : Ω, w ε :=
    finite_second_fourth_tail_lower f hv h₂ h₄
  have hpoint (ε : Ω) : amp*w ε ≤ |f ε|^p := by
    dsimp [w]
    split_ifs with h
    · rw [mul_one]
      have hpow : (f ε^2)^(p/2) = |f ε|^p := by
        rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg (f ε))]
        congr 1
        ring
      exact (Real.rpow_le_rpow (half_pos hv).le h (by linarith)).trans_eq hpow
    · rw [mul_zero]
      exact Real.rpow_nonneg (abs_nonneg _) _
  have hmean : amp*(𝔼 ε : Ω, w ε) ≤ 𝔼 ε : Ω, |f ε|^p := by
    rw [Finset.mul_expect]
    exact Finset.expect_le_expect (fun ε _ => hpoint ε)
  have hsmall : amp/12 ≤ 𝔼 ε : Ω, |f ε|^p := by
    have h := mul_le_mul_of_nonneg_left htail hamp
    nlinarith only [h,hmean]
  calc
    v^(p/2) = (2 : ℝ)^(p/2)*amp := by
      dsimp [amp]
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (half_pos hv).le]
      congr 1
      ring
    _ ≤ (2 : ℝ)^(p/2)*(12*(𝔼 ε : Ω, |f ε|^p)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsmall]) (by positivity)
    _ = _ := by ring

/-- Dimension-independent finite-sign lower moment (a quantitative
Khintchine inequality sufficient for all p>0). -/
theorem signRow_lower_moment {n : ℕ} (a : Fin n → ℝ) {p : ℝ} (hp : 0 < p) :
    (∑ i, a i^2)^(p/2) ≤
      (12*(2 : ℝ)^(p/2)) * (𝔼 ε : Fin n → Bool, |signRow a ε|^p) := by
  have hv : 0 ≤ ∑ i, a i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hz : (∑ i, a i^2) = 0
  · rw [hz,Real.zero_rpow (by linarith : p/2 ≠ 0)]
    apply mul_nonneg (by positivity)
    exact Finset.expect_nonneg (fun ε _ => Real.rpow_nonneg (abs_nonneg _) p)
  · exact finite_moment_lower_of_second_fourth (signRow a)
      (lt_of_le_of_ne hv (Ne.symm hz)) hp (signRow_second_moment a)
      (signRow_fourth_moment_le a)

def complexSignRow {n : ℕ} (a : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i, (sign (ε i) : ℂ) * a i

theorem complexSignRow_re {n : ℕ} (a : Fin n → ℂ) (ε : Fin n → Bool) :
    (complexSignRow a ε).re = signRow (fun i => (a i).re) ε := by
  simp [complexSignRow,signRow,mul_comm]

theorem complexSignRow_im {n : ℕ} (a : Fin n → ℂ) (ε : Fin n → Bool) :
    (complexSignRow a ε).im = signRow (fun i => (a i).im) ε := by
  simp [complexSignRow,signRow,mul_comm]

/-- Complex coefficients require only twice the real lower-moment constant. -/
theorem complexSignRow_lower_moment {n : ℕ} (a : Fin n → ℂ)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (∑ i, ‖a i‖^2)^(p/2) ≤
      (24*(2 : ℝ)^(p/2)) * (𝔼 ε : Fin n → Bool, ‖complexSignRow a ε‖^p) := by
  have hsplit : (∑ i, ‖a i‖^2) = (∑ i, (a i).re^2) + (∑ i, (a i).im^2) := by
    simp_rw [Complex.sq_norm,Complex.normSq_apply,← sq]
    rw [Finset.sum_add_distrib]
  have hK : 0 ≤ 12*(2 : ℝ)^(p/2) := by positivity
  have hR : (∑ i, (a i).re^2)^(p/2) ≤
      (12*(2 : ℝ)^(p/2))*(𝔼 ε : Fin n → Bool, ‖complexSignRow a ε‖^p) := by
    apply (signRow_lower_moment (fun i => (a i).re) hp).trans
    apply mul_le_mul_of_nonneg_left _ hK
    apply Finset.expect_le_expect
    intro ε _
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    rw [← complexSignRow_re]
    exact Complex.abs_re_le_norm _
  have hI : (∑ i, (a i).im^2)^(p/2) ≤
      (12*(2 : ℝ)^(p/2))*(𝔼 ε : Fin n → Bool, ‖complexSignRow a ε‖^p) := by
    apply (signRow_lower_moment (fun i => (a i).im) hp).trans
    apply mul_le_mul_of_nonneg_left _ hK
    apply Finset.expect_le_expect
    intro ε _
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    rw [← complexSignRow_im]
    exact Complex.abs_im_le_norm _
  rw [hsplit]
  calc
    _ ≤ (∑ i, (a i).re^2)^(p/2) + (∑ i, (a i).im^2)^(p/2) :=
      Real.rpow_add_le_add_rpow (Finset.sum_nonneg (fun i _ => sq_nonneg _))
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by linarith) (by linarith)
    _ ≤ _ := by nlinarith only [hR,hI]

theorem expect_rpow_le_rpow_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ ε, 0 ≤ f ε) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (𝔼 ε : Ω, (f ε)^q) ≤ (𝔼 ε : Ω, f ε)^q := by
  have hcard : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := (Real.concaveOn_rpow hq0 hq1).le_map_centerMass
    (t := (Finset.univ : Finset Ω)) (w := fun _ => (1 : ℝ)) (p := f)
    (fun _ _ => by norm_num)
    (by simpa using hcard)
    (fun ε _ => hf ε)
  simpa only [Finset.centerMass,Function.comp_def,one_smul,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    smul_eq_mul,Fintype.expect_eq_sum_div_card,div_eq_mul_inv,mul_comm] using h

theorem complexSignRow_second_moment {n : ℕ} (a : Fin n → ℂ) :
    (𝔼 ε : Fin n → Bool, ‖complexSignRow a ε‖^2) = ∑ i, ‖a i‖^2 := by
  simp_rw [Complex.sq_norm,Complex.normSq_apply,← sq,
    complexSignRow_re,complexSignRow_im]
  rw [Finset.expect_add_distrib,signRow_second_moment,signRow_second_moment,
    Finset.sum_add_distrib]

/-- The matching upper moment for p≤2 is finite Jensen applied to the
actual second moment. Together with the lower bound it permits finite
Hilbert-family extensions of scalar Lp bounds. -/
theorem complexSignRow_upper_moment {n : ℕ} (a : Fin n → ℂ)
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    (𝔼 ε : Fin n → Bool, ‖complexSignRow a ε‖^p) ≤ (∑ i, ‖a i‖^2)^(p/2) := by
  have h := expect_rpow_le_rpow_expect
    (fun ε : Fin n → Bool => ‖complexSignRow a ε‖^2)
    (fun ε => sq_nonneg _) (by linarith : 0 ≤ p/2) (by linarith : p/2 ≤ 1)
  rw [complexSignRow_second_moment] at h
  have heq (ε : Fin n → Bool) : (‖complexSignRow a ε‖^2)^(p/2) =
      ‖complexSignRow a ε‖^p := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  simpa only [heq] using h

end BrownianSharp.AlignmentPaperRademacherLower
