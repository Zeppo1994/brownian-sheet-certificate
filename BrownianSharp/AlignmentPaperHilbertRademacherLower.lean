import BrownianSharp.AlignmentPaperRademacherLower
import BrownianSharp.AlignmentPaperAnchoredLpAggregateBudget
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Dimension-free lower Rademacher moments for finite Hilbert rows. The
mixed-norm step is the already proved finite block Minkowski inequality. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPaperHilbertRademacherLower
open BrownianSharp.AlignmentPaperRademacherLower
open BrownianSharp.AlignmentPaperAnchoredLpAggregateBudget

private theorem uniform_integral_eq_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (f : Ω → ℝ) :
    (∫ x, f x ∂(PMF.uniformOfFintype Ω).toMeasure) = 𝔼 x : Ω, f x := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,Fintype.expect_eq_sum_div_card]
  rw [← Finset.mul_sum]
  ring

theorem hilbertRow_lower_moment {m n : ℕ} (a : Fin m → Fin n → ℂ)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (∑ s, ∑ i, ‖a i s‖^2)^(p/2) ≤
      (24*(2:ℝ)^(p/2)) *
        (𝔼 ε : Fin m → Bool,
          (∑ s, ‖complexSignRow (fun i => a i s) ε‖^2)^(p/2)) := by
  classical
  let Ω := Fin m → Bool
  letI : MeasurableSpace Ω := ⊤
  let ν : Measure Ω := (PMF.uniformOfFintype Ω).toMeasure
  let X : Fin n → Ω → ℝ := fun s ε => ‖complexSignRow (fun i => a i s) ε‖
  let S : Ω → ℝ := fun ε => Real.sqrt (∑ s, X s ε^2)
  have hsum0 (ε : Ω) : 0 ≤ ∑ s, X s ε^2 :=
    Finset.sum_nonneg fun s _ => sq_nonneg _
  have hSnonneg : ∀ᵐ ε ∂ν, 0 ≤ S ε := ae_of_all _ fun _ => Real.sqrt_nonneg _
  have hSsq : ∀ᵐ ε ∂ν, ∑ s, |X s ε|^2 ≤ S ε^2 := by
    filter_upwards with ε
    simp only [S,sq_abs,Real.sq_sqrt (hsum0 ε)]
    exact le_rfl
  have hM := finite_block_lp_square_budget (μ := ν) hp hp2 X S
    (fun _ => Integrable.of_finite) Integrable.of_finite hSnonneg hSsq
  have hXi (s : Fin n) : (∫ ε, |X s ε|^p ∂ν) =
      𝔼 ε : Ω, ‖complexSignRow (fun i => a i s) ε‖^p := by
    rw [show ν = (PMF.uniformOfFintype Ω).toMeasure by rfl,
      uniform_integral_eq_expect]
    apply Finset.expect_congr rfl
    intro ε _
    simp [X]
  have hSpow (ε : Ω) : S ε^p =
      (∑ s, ‖complexSignRow (fun i => a i s) ε‖^2)^(p/2) := by
    dsimp [S,X]
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul (hsum0 ε)]
    congr 1
    ring
  have hSint : (∫ ε, S ε^p ∂ν) =
      𝔼 ε : Ω, (∑ s, ‖complexSignRow (fun i => a i s) ε‖^2)^(p/2) := by
    simp_rw [hSpow]
    exact uniform_integral_eq_expect _
  simp_rw [hXi] at hM
  rw [hSint] at hM
  let K : ℝ := 24*(2:ℝ)^(p/2)
  let V : Fin n → ℝ := fun s => ∑ i, ‖a i s‖^2
  let B : Fin n → ℝ := fun s => 𝔼 ε : Ω, ‖complexSignRow (fun i => a i s) ε‖^p
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV (s : Fin n) : 0 ≤ V s := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB (s : Fin n) : 0 ≤ B s :=
    Finset.expect_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _
  have hcancel : (p/2)*(2/p) = 1 := by field_simp
  have hcancel' : (2/p)*(p/2) = 1 := by field_simp
  have hterm (s : Fin n) : V s ≤ K^(2/p) * (B s)^(2/p) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (hV s) _)
      (complexSignRow_lower_moment (fun i => a i s) hp hp2) (by positivity : 0 ≤ 2/p)
    rw [← Real.rpow_mul (hV s),hcancel,Real.rpow_one,
      Real.mul_rpow hK (hB s)] at h
    exact h
  have hsum : (∑ s, V s) ≤ K^(2/p) * ∑ s, (B s)^(2/p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => hterm s
  have hpower := Real.rpow_le_rpow (Finset.sum_nonneg fun s _ => hV s) hsum
    (by positivity : 0 ≤ p/2)
  rw [Real.mul_rpow (Real.rpow_nonneg hK _) (Finset.sum_nonneg fun s _ =>
    Real.rpow_nonneg (hB s) _),← Real.rpow_mul hK,hcancel',Real.rpow_one] at hpower
  calc
    (∑ s, ∑ i, ‖a i s‖^2)^(p/2) ≤ K*(∑ s, (B s)^(2/p))^(p/2) := hpower
    _ ≤ K * (𝔼 ε : Ω,
        (∑ s, ‖complexSignRow (fun i => a i s) ε‖^2)^(p/2)) :=
      mul_le_mul_of_nonneg_left hM hK
    _ = _ := rfl

end BrownianSharp.AlignmentPaperHilbertRademacherLower
