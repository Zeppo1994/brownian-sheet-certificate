import BrownianSharp.AlignmentPaperSmoothKernelDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-! Real-line translation control for the actual smooth periodic kernels. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperKernelTranslation

open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPaperFejerPointwise
open BrownianSharp.AlignmentPaperSmoothKernelDerivative
open BrownianSharp.ScalarKernelL1
open BrownianSharp.ScalarAtomVariance
open HaarQuarter.TrigonometricHaarExtraction

private theorem character_add (x y : ℝ) :
    character 1 (x+y) = character 1 x * character 1 y := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem characterChord_add_le (x y : ℝ) :
    characterChord (x+y) ≤ characterChord x + characterChord y := by
  unfold characterChord
  rw [character_add]
  have hdecomp : character 1 x * character 1 y - 1 =
      (character 1 x - 1) * character 1 y + (character 1 y - 1) := by ring
  rw [hdecomp]
  calc
    _ ≤ ‖(character 1 x - 1) * character 1 y‖ +
        ‖character 1 y - 1‖ := norm_add_le _ _
    _ = _ := by simp [character_norm]

theorem characterChord_sub_le (x y : ℝ) :
    characterChord x ≤ characterChord (x+y) + characterChord y := by
  unfold characterChord
  rw [character_add]
  have hdecomp : character 1 x - 1 =
      (character 1 x * character 1 y - 1) - character 1 x * (character 1 y - 1) := by ring
  rw [hdecomp]
  calc
    _ ≤ ‖character 1 x * character 1 y - 1‖ +
        ‖character 1 x * (character 1 y - 1)‖ := norm_sub_le _ _
    _ = _ := by simp [character_norm, add_comm]

theorem characterChord_le_two_pi_abs (x : ℝ) :
    characterChord x ≤ 2*Real.pi*|x| := by
  unfold characterChord character
  have harg : (2:ℂ) * (Real.pi:ℂ) * (((1:ℤ):ℝ):ℂ) * (x:ℂ) * Complex.I =
      Complex.I*((2*Real.pi*x:ℝ):ℂ) := by push_cast; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    ‖2 * Real.sin (2*Real.pi*x/2)‖ = ‖2 * Real.sin (Real.pi*x)‖ := by
      congr 2
      ring_nf
    ‖2 * Real.sin (Real.pi*x)‖ = 2*|Real.sin (Real.pi*x)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    _ ≤ 2*|Real.pi*x| := by
      exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = 2*Real.pi*|x| := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

theorem characterChord_sub_lipschitz (x y : ℝ) :
    |characterChord (x+y)-characterChord x| ≤ 2*Real.pi*|y| := by
  have h₁ := characterChord_add_le x y
  have h₂ := characterChord_sub_le x y
  have h₃ := characterChord_le_two_pi_abs y
  rw [abs_le]
  constructor <;> linarith

def smoothResolutionKernelCurve (s : ℕ) (x : ℝ) : ℂ :=
  scalarBlockKernel smoothResolutionCutoff s (x:UnitAddCircle)

theorem smoothResolutionKernelCurve_differentiable (s : ℕ) :
    Differentiable ℝ (smoothResolutionKernelCurve s) := by
  have hchar : ∀ n : ℤ, Differentiable ℝ (fun x : ℝ => character n x) := by
    intro n
    unfold character
    fun_prop
  have heq : smoothResolutionKernelCurve s = fun x : ℝ =>
      ∑ n ∈ scalarFrequencyBox s,
        (scalarBlock smoothResolutionCutoff s (n:ℝ) : ℂ) * character n x := by
    funext x
    change (AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel
        smoothResolutionCutoff s) (x:UnitAddCircle) = _
    rw [AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel]
    unfold ScalarKernelL1.polynomialKernel
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    have hfourier : fourier (T := (1:ℝ)) n (x:UnitAddCircle) = character n x := by
      simpa [addCircleCharacter] using addCircleCharacter_coe n x
    change (scalarBlock smoothResolutionCutoff s (n:ℝ) : ℂ) *
      fourier n (x:UnitAddCircle) = _
    exact congrArg (fun z : ℂ =>
      (scalarBlock smoothResolutionCutoff s (n:ℝ) : ℂ) * z) hfourier
  rw [heq]
  exact Differentiable.fun_sum fun n hn => (hchar n).const_mul _

private theorem circleChord_coe (x : ℝ) :
    circleCharacterChord (x:UnitAddCircle) = characterChord x := by
  unfold circleCharacterChord characterChord
  rw [show fourier (T := (1:ℝ)) 1 (x:UnitAddCircle) = character 1 x by
    simpa [addCircleCharacter] using addCircleCharacter_coe (1:ℤ) x]

theorem smoothResolutionKernelCurve_local_translate
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C * (2:ℝ)^(2*s) /
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (s : ℕ) (x h : ℝ) (hD : 0 < characterChord x)
    (hh : 0 ≤ h) (hsmall : h ≤ characterChord x/(4*Real.pi)) :
    ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
      4*C*h*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2) := by
  let D := characterChord x
  let q := (2:ℝ)^s
  have hq : 0 ≤ q := by positivity
  have hden0 : 0 < 1+(q*D)^2 := by positivity
  have hbound : ∀ t ∈ Set.Ico x (x+h),
      ‖deriv (smoothResolutionKernelCurve s) t‖ ≤
        4*C*q^(2:ℕ)/(1+(q*D)^2) := by
    intro t ht
    have ht' : x ≤ t ∧ t < x+h := by simpa [Set.mem_Ico] using ht
    have htlo : 0 ≤ t-x := by linarith
    have hthi : t-x ≤ h := by linarith
    have hch := characterChord_sub_lipschitz x (t-x)
    have habs : |t-x| ≤ h := by rw [abs_of_nonneg htlo]; exact hthi
    have hsmall' : 2*Real.pi*h ≤ D/2 := by
      have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 4*Real.pi)
      have hmul' : 4*Real.pi*h ≤ D := by
        calc
          4*Real.pi*h ≤ 4*Real.pi*(D/(4*Real.pi)) := hmul
          _ = D := by field_simp
      nlinarith
    have hch' : |characterChord t-D| ≤ 2*Real.pi*h := by
      have htmp := hch.trans (mul_le_mul_of_nonneg_left habs (by positivity))
      simpa [D, add_sub_cancel] using htmp
    have hlow : D/2 ≤ characterChord t := by
      rw [abs_le] at hch'
      linarith
    have hcircle := circleChord_coe t
    have hqd : q*D/2 ≤ q*characterChord t := by
      have := mul_le_mul_of_nonneg_left hlow hq
      nlinarith
    have hden : 1+(q*D)^2 ≤ 4*(1+(q*characterChord t)^2) := by
      have hrel : q*D ≤ 2*(q*characterChord t) := by nlinarith [hqd]
      have hqD : 0 ≤ q*D := mul_nonneg hq (le_of_lt hD)
      have hqt : 0 ≤ q*characterChord t :=
        mul_nonneg hq (le_trans (by positivity) hlow)
      nlinarith [sq_nonneg (q*D), sq_nonneg (q*characterChord t)]
    have hleft := hderiv s t
    have hpow : (2:ℝ)^(2*s)=((2:ℝ)^s)^2 := by
      rw [show 2*s=s*2 by omega, pow_mul]
    have hcmp : C*q^2/(1+(q*characterChord t)^2) ≤
        4*C*q^2/(1+(q*D)^2) := by
      rw [div_le_div_iff₀ (by positivity) hden0]
      have hnonneg : 0 ≤ C*q^2 := by positivity
      nlinarith
    have hleft' : ‖deriv (smoothResolutionKernelCurve s) t‖ ≤
        C*q^2/(1+(q*characterChord t)^2) := by
      have hleft2 := hleft
      rw [hpow] at hleft2
      simpa [q, hcircle, pow_two, mul_comm, mul_left_comm, mul_assoc] using hleft2
    have hfinal := hleft'.trans hcmp
    simpa [q, hpow, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      hfinal
  have hf := smoothResolutionKernelCurve_differentiable s
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=x) (b:=x+h)
    (fun t ht => (hf t).hasDerivAt.hasDerivWithinAt)
    hbound
  have hxend : x+h ∈ Set.Icc x (x+h) := by simp [hh]
  have hresult := hmvt (x+h) hxend
  convert hresult using 1
  dsimp [D, q]
  ring

theorem smoothResolutionKernelCurve_local_translate_abs
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C * (2:ℝ)^(2*s) /
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (s : ℕ) (x h : ℝ) (hD : 0 < characterChord x)
    (hsmall : |h| ≤ characterChord x/(8*Real.pi)) :
    ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
      8*C*(|h|)*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2) := by
  by_cases hh : 0 ≤ h
  · have hsmall' : h ≤ characterChord x/(4*Real.pi) := by
      calc
        h ≤ characterChord x/(8*Real.pi) := by
          simpa [abs_of_nonneg hh] using hsmall
        _ ≤ characterChord x/(4*Real.pi) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hD, Real.pi_pos]
    have hpos := smoothResolutionKernelCurve_local_translate C hC hderiv s x h
      hD hh hsmall'
    have habs : |h|=h := abs_of_nonneg hh
    rw [habs]
    calc
      ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
          4*C*h*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2) := hpos
      _ ≤ 8*C*h*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hA : 0 ≤ C*h*(2:ℝ)^(2*s) := by positivity
        nlinarith
  · have hhneg : h < 0 := lt_of_not_ge hh
    let y := x+h
    let k := -h
    have hk : 0 ≤ k := by dsimp [k]; linarith
    have habs : |h|=k := by simp [k, abs_of_neg hhneg]
    have hksmall : k ≤ characterChord x/(8*Real.pi) := by
      rw [← habs]
      exact hsmall
    have hyclose : |characterChord y-characterChord x| ≤ 2*Real.pi*k := by
      have := characterChord_sub_lipschitz x h
      simpa [y, habs] using this
    have hDylow : 3*characterChord x/4 ≤ characterChord y := by
      rw [abs_le] at hyclose
      have hmul := mul_le_mul_of_nonneg_left hksmall (by positivity : 0 ≤ 8*Real.pi)
      have hmul' : 8*Real.pi*k ≤ characterChord x := by
        calc
          8*Real.pi*k ≤ 8*Real.pi*(characterChord x/(8*Real.pi)) := hmul
          _ = characterChord x := by field_simp
      nlinarith [Real.pi_pos]
    have hDy : 0 < characterChord y := by linarith
    have hkDy : k ≤ characterChord y/(4*Real.pi) := by
      have hxbound : 8*Real.pi*k ≤ characterChord x := by
        calc
          8*Real.pi*k ≤ 8*Real.pi*(characterChord x/(8*Real.pi)) :=
            mul_le_mul_of_nonneg_left hksmall (by positivity)
          _ = characterChord x := by field_simp
      have h4pk : 4*Real.pi*k ≤ characterChord y := by nlinarith
      apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).2
      nlinarith
    have hlocal := smoothResolutionKernelCurve_local_translate C hC hderiv s y k
      hDy hk hkDy
    have hyidentity : y+k=x := by dsimp [y,k]; ring
    have hDcmp : 1+(((2:ℝ)^s)*characterChord x)^2 ≤
        2*(1+(((2:ℝ)^s)*characterChord y)^2) := by
      have hratio : characterChord x ≤ (4/3:ℝ)*characterChord y := by nlinarith
      have hq : 0 ≤ (2:ℝ)^s := by positivity
      have hqx : (2:ℝ)^s*characterChord x ≤
          (4/3)*((2:ℝ)^s*characterChord y) := by nlinarith
      have hxnonneg : 0 ≤ (2:ℝ)^s*characterChord x := by positivity
      have hynonneg : 0 ≤ (2:ℝ)^s*characterChord y := by positivity
      have hsq : ((2:ℝ)^s*characterChord x)^2 ≤
          ((4/3)*((2:ℝ)^s*characterChord y))^2 := by
        nlinarith [hqx, hxnonneg, hynonneg]
      nlinarith [hsq, sq_nonneg ((2:ℝ)^s*characterChord y)]
    have hdenx : 0 < 1+(((2:ℝ)^s)*characterChord x)^2 := by positivity
    have hdenY : 0 < 1+(((2:ℝ)^s)*characterChord y)^2 := by positivity
    have hnum : 0 ≤ 4*C*k*(2:ℝ)^(2*s) := by positivity
    have hratio :
        4*C*k*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord y)^2) ≤
        8*C*k*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2) := by
      rw [div_le_div_iff₀ hdenY hdenx]
      nlinarith [hnum, hDcmp]
    rw [hyidentity] at hlocal
    rw [norm_sub_rev]
    calc
      ‖smoothResolutionKernelCurve s x-smoothResolutionKernelCurve s y‖ ≤
          4*C*k*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord y)^2) := hlocal
      _ ≤ 8*C*k*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2) := hratio
      _ = 8*C*(|h|)*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2) := by rw [← habs]

theorem smoothResolutionKernelCurve_difference_min
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C₁*(2:ℝ)^(2*s)/
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (s : ℕ) (x h : ℝ) (hD : 0 < characterChord x)
    (hsmall : |h| ≤ characterChord x/(8*Real.pi)) :
    ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
      min
        (3*C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord x)^2))
        (8*C₁*(|h|)*(2:ℝ)^(2*s)/(1+(((2:ℝ)^s)*characterChord x)^2)) := by
  have hlocal := smoothResolutionKernelCurve_local_translate_abs C₁ hC₁ hderiv
    s x h hD hsmall
  have hq : 0 ≤ (2:ℝ)^s := by positivity
  have hden : 0 < 1+(((2:ℝ)^s)*characterChord x)^2 := by positivity
  have hcircleX := circleChord_coe x
  have hsizeX : ‖smoothResolutionKernelCurve s x‖ ≤
      C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord x)^2) := by
    simpa [smoothResolutionKernelCurve, hcircleX] using hsize s (x:UnitAddCircle)
  have hdist := characterChord_sub_lipschitz x h
  have hchordY : 3*characterChord x/4 ≤ characterChord (x+h) := by
    rw [abs_le] at hdist
    have hmult := mul_le_mul_of_nonneg_left hsmall
      (by positivity : 0 ≤ 8*Real.pi)
    have hbound : 8*Real.pi*|h| ≤ characterChord x := by
      calc
        8*Real.pi*|h| ≤ 8*Real.pi*(characterChord x/(8*Real.pi)) := hmult
        _ = characterChord x := by field_simp
    nlinarith [Real.pi_pos]
  have hcircleY := circleChord_coe (x+h)
  have hratio : characterChord x ≤ (4/3:ℝ)*characterChord (x+h) := by nlinarith
  have hqY : (2:ℝ)^s*characterChord x ≤
      (4/3)*((2:ℝ)^s*characterChord (x+h)) := by nlinarith
  have hdenCmp : 1+(((2:ℝ)^s)*characterChord x)^2 ≤
      2*(1+(((2:ℝ)^s)*characterChord (x+h))^2) := by
    have hxnonneg : 0 ≤ (2:ℝ)^s*characterChord x := by positivity
    have hynonneg : 0 ≤ (2:ℝ)^s*characterChord (x+h) := by
      exact mul_nonneg hq (by
        unfold characterChord
        exact norm_nonneg _)
    have hsq : ((2:ℝ)^s*characterChord x)^2 ≤
        ((4/3)*((2:ℝ)^s*characterChord (x+h)))^2 := by nlinarith
    nlinarith [hsq, sq_nonneg ((2:ℝ)^s*characterChord (x+h))]
  have hsizeY : ‖smoothResolutionKernelCurve s (x+h)‖ ≤
      2*C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord x)^2) := by
    have hsY := hsize s ((x+h):UnitAddCircle)
    have hcircleY' :
        circleCharacterChord ((x:UnitAddCircle)+(h:UnitAddCircle)) =
          characterChord (x+h) := by
      simpa only [← AddCircle.coe_add] using hcircleY
    have hsY' :
        ‖scalarBlockKernel smoothResolutionCutoff s ((x+h):UnitAddCircle)‖ ≤
          C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord (x+h))^2) := by
      simpa [hcircleY'] using hsY
    simpa [smoothResolutionKernelCurve] using
      (calc
        ‖scalarBlockKernel smoothResolutionCutoff s ((x+h):UnitAddCircle)‖ ≤
            C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord (x+h))^2) := hsY'
        _ ≤ 2*C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord x)^2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hcoef : 0 ≤ C₀*(2:ℝ)^s := mul_nonneg hC₀ hq
          calc
            C₀*(2:ℝ)^s*(1+(((2:ℝ)^s)*characterChord x)^2) ≤
                C₀*(2:ℝ)^s*(2*(1+(((2:ℝ)^s)*characterChord (x+h))^2)) :=
              mul_le_mul_of_nonneg_left hdenCmp hcoef
            _ = 2*C₀*(2:ℝ)^s*(1+(((2:ℝ)^s)*characterChord (x+h))^2) := by ring)
  have hsizeDiff :
      ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
        3*C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord x)^2) := by
    calc
      _ ≤ ‖smoothResolutionKernelCurve s (x+h)‖+
          ‖smoothResolutionKernelCurve s x‖ := norm_sub_le _ _
      _ ≤ 2*C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord x)^2)+
          C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord x)^2) :=
            add_le_add hsizeY hsizeX
      _ = _ := by ring
  exact le_min hsizeDiff hlocal

end BrownianSharp.AlignmentPaperKernelTranslation
