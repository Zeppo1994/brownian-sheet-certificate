import BrownianSharp.AlignmentFractionalKernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentFractionalSemigroup

open BrownianSharp.AlignmentFractionalKernel

/-- Real beta-kernel integral, normalized by the gamma identity. -/
theorem beta_power_integral {a α β : ℝ} (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in (0:ℝ)..a, x ^ (β-1) * (a-x) ^ (α-1)) =
      Real.Gamma β * Real.Gamma α / Real.Gamma (α+β) * a ^ (α+β-1) := by
  have hαc : 0 < (α:ℂ).re := by simpa using hα
  have hβc : 0 < (β:ℂ).re := by simpa using hβ
  have hEq : Set.EqOn
      (fun x : ℝ => ((x ^ (β-1) * (a-x) ^ (α-1) : ℝ) : ℂ))
      (fun x : ℝ => (x:ℂ) ^ ((β:ℂ)-1) * ((a:ℂ)-(x:ℂ)) ^ ((α:ℂ)-1))
      (Set.uIoo 0 a) := by
    intro x hx
    have hx0 : 0 < x := by simpa [Set.uIoo, ha.le] using hx.1
    have hxa : 0 < a-x := by
      have hxlt : x < a := by simpa [Set.uIoo, ha.le] using hx.2
      linarith
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt hx0),
      Complex.ofReal_cpow (le_of_lt hxa), Complex.ofReal_sub, Complex.ofReal_one]
  have hleft : (∫ x in (0:ℝ)..a, ((x ^ (β-1) * (a-x) ^ (α-1) : ℝ) : ℂ)) =
      (a:ℂ) ^ ((β:ℂ)+(α:ℂ)-1) * Complex.betaIntegral β α := by
    calc
      (∫ x in (0:ℝ)..a, ((x ^ (β-1) * (a-x) ^ (α-1) : ℝ) : ℂ)) =
          ∫ x in (0:ℝ)..a, (x:ℂ)^((β:ℂ)-1) * ((a:ℂ)-(x:ℂ))^((α:ℂ)-1) :=
        intervalIntegral.integral_congr_uIoo hEq
      _ = (a:ℂ)^((β:ℂ)+(α:ℂ)-1) * Complex.betaIntegral β α :=
        Complex.betaIntegral_scaled (β:ℂ) (α:ℂ) ha
  have hcast : (∫ x in (0:ℝ)..a,
      ((x ^ (β-1) * (a-x) ^ (α-1) : ℝ) : ℂ)) =
      Complex.ofReal (∫ x in (0:ℝ)..a, x ^ (β-1) * (a-x) ^ (α-1)) := by
    exact intervalIntegral.integral_ofReal
  rw [hcast] at hleft
  have hbeta := Complex.betaIntegral_eq_Gamma_mul_div (β:ℂ) (α:ℂ) hβc hαc
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hbeta
  have hpow : (a:ℂ) ^ ((β:ℂ)+(α:ℂ)-1) = Complex.ofReal (a ^ (α+β-1)) := by
    calc
      (a:ℂ) ^ ((β:ℂ)+(α:ℂ)-1) = (a:ℂ) ^ ((α+β-1:ℝ):ℂ) := by
        congr 1
        push_cast
        ring
      _ = Complex.ofReal (a ^ (α+β-1)) := (Complex.ofReal_cpow ha.le _).symm
  have hfinal : Complex.ofReal
      (Real.Gamma β * Real.Gamma α / Real.Gamma (α+β) * a ^ (α+β-1)) =
      Complex.ofReal (∫ x in (0:ℝ)..a, x ^ (β-1) * (a-x) ^ (α-1)) := by
    rw [hleft, hpow, hbeta]
    push_cast
    ring
  exact Complex.ofReal_injective hfinal.symm


/-- Riemann--Liouville integration of a positive power. -/
theorem rlIntegral_rpow {a γ t : ℝ} (ha : 0 < a) (hγ : 0 < γ) (ht : 0 < t) :
    rlIntegral a (fun u => u ^ (γ-1)) t =
      Real.Gamma γ / Real.Gamma (a+γ) * t ^ (a+γ-1) := by
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGsum : Real.Gamma (a+γ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos ha hγ)).ne'
  unfold rlIntegral kernel
  calc
    (∫ u in (0:ℝ)..t, (Real.Gamma a)⁻¹ * (t-u)^(a-1) * u^(γ-1)) =
        (Real.Gamma a)⁻¹ * (∫ u in (0:ℝ)..t,
          u^(γ-1) * (t-u)^(a-1)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    _ = (Real.Gamma a)⁻¹ *
        (Real.Gamma γ * Real.Gamma a / Real.Gamma (a+γ) * t^(a+γ-1)) := by
      rw [beta_power_integral ht ha hγ]
    _ = Real.Gamma γ / Real.Gamma (a+γ) * t^(a+γ-1) := by
      field_simp [hGa, hGsum]


/-- Semigroup identity on polynomial monomial atoms. This is an actual
Riemann--Liouville composition theorem, not merely a rate-level interface. -/
theorem rlIntegral_semigroup_natPow {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (m : ℕ) :
    rlIntegral a (fun s => rlIntegral b (fun u => u ^ (m:ℝ)) s) t =
      rlIntegral (a+b) (fun u => u ^ (m:ℝ)) t := by
  let γ : ℝ := (m:ℝ) + 1
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hβγ : 0 < b+γ-1 := by dsimp [γ]; linarith
  have hαβγ : 0 < a+b+γ-1 := by dsimp [γ]; linarith
  have hpow : γ-1 = (m:ℝ) := by dsimp [γ]; ring
  have hinner : Set.EqOn
      (fun s => rlIntegral b (fun u => u^(m:ℝ)) s)
      (fun s => Real.Gamma γ / Real.Gamma (b+γ) * s^(b+γ-1))
      (Set.uIcc (0:ℝ) t) := by
    intro s hs
    have hs0 : 0 ≤ s := by simpa [Set.uIcc, min_eq_left ht.le, max_eq_right ht.le] using hs.1
    by_cases hspos : 0 < s
    · have hfun : (fun u : ℝ => u^(m:ℝ)) = fun u => u^(γ-1) := by
        funext u
        rw [← hpow]
      rw [hfun]
      change rlIntegral b (fun u => u^(γ-1)) s = _
      exact rlIntegral_rpow hb hγ hspos
    · have hsEq : s = 0 := le_antisymm (le_of_not_gt hspos) hs0
      subst s
      simp [rlIntegral, Real.zero_rpow (ne_of_gt hβγ)]
  have houter :
      (∫ s in (0:ℝ)..t, kernel a (t-s) *
          rlIntegral b (fun u => u^(m:ℝ)) s) =
        (Real.Gamma γ / Real.Gamma (b+γ)) *
          rlIntegral a (fun s => s^(b+γ-1)) t := by
    calc
      (∫ s in (0:ℝ)..t, kernel a (t-s) *
          rlIntegral b (fun u => u^(m:ℝ)) s) =
          ∫ s in (0:ℝ)..t, kernel a (t-s) *
            (Real.Gamma γ / Real.Gamma (b+γ) * s^(b+γ-1)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change kernel a (t-s) * rlIntegral b (fun u => u^(m:ℝ)) s =
          kernel a (t-s) * (Real.Gamma γ / Real.Gamma (b+γ) * s^(b+γ-1))
        have hh := hinner hs
        change rlIntegral b (fun u => u^(m:ℝ)) s =
          Real.Gamma γ / Real.Gamma (b+γ) * s^(b+γ-1) at hh
        rw [hh]
      _ = (Real.Gamma γ / Real.Gamma (b+γ)) *
          rlIntegral a (fun s => s^(b+γ-1)) t := by
        unfold rlIntegral kernel
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s hs
        ring
  rw [show rlIntegral a (fun s => rlIntegral b (fun u => u^(m:ℝ)) s) t =
      (∫ s in (0:ℝ)..t, kernel a (t-s) * rlIntegral b (fun u => u^(m:ℝ)) s) by rfl]
  have hfun : (fun u : ℝ => u^(m:ℝ)) = fun u => u^(γ-1) := by
    funext u
    rw [← hpow]
  have hleft := rlIntegral_rpow ha (add_pos hb hγ) ht
  have hright := rlIntegral_rpow (add_pos ha hb) hγ ht
  rw [← hfun] at hright
  rw [houter, hleft, hright]
  have hG1 : Real.Gamma (b+γ) ≠ 0 := (Real.Gamma_pos_of_pos (add_pos hb hγ)).ne'
  have hG2 : Real.Gamma ((a+b)+γ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos (add_pos ha hb) hγ)).ne'
  field_simp [hG1, hG2]
  <;> ring

end BrownianSharp.AlignmentFractionalSemigroup
