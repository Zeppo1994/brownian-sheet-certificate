import BrownianSharp.GaussianCDFCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Chain calculus for the Gaussian quantile heat profile. -/

open Filter Set
open scoped Topology

namespace BrownianSharp

private noncomputable abbrev gaussianQuantile := Concentration.standardGaussianQuantile
private noncomputable abbrev gaussianProfile := standardGaussianIsoperimetricProfile

/-- The second derivative of the standard Gaussian quantile is
`Φ⁻¹(u) / I(u)^2`, where `I(u)=φ(Φ⁻¹(u))`. -/
theorem hasDerivAt_deriv_standardGaussianQuantile {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (deriv gaussianQuantile)
      (gaussianQuantile u / (gaussianProfile u) ^ 2) u := by
  have hprof := hasDerivAt_standardGaussianIsoperimetricProfile hu0 hu1
  have hprofne : gaussianProfile u ≠ 0 :=
    ne_of_gt (standardGaussianIsoperimetricProfile_pos hu0 hu1)
  have hinv := hprof.inv hprofne
  have hlocal : (fun v : ℝ => deriv gaussianQuantile v) =ᶠ[𝓝 u]
      (fun v => (gaussianProfile v)⁻¹) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
    exact (hasDerivAt_standardGaussianQuantile hv.1 hv.2).deriv
  have h := hinv.congr_of_eventuallyEq hlocal
  convert h using 1 <;> simp [gaussianQuantile, gaussianProfile,
    standardGaussianIsoperimetricProfile]

/-- Second-derivative chain rule for the Gaussian quantile along a scalar
curve whose values remain in the open unit interval. -/
theorem deriv_deriv_gaussianQuantile_comp
    (uLine dU : ℝ → ℝ) (d2U : ℝ)
    (hrange : ∀ s, 0 < uLine s ∧ uLine s < 1)
    (hfirst : ∀ s, HasDerivAt uLine (dU s) s)
    (hsecond : HasDerivAt dU d2U 0) :
    deriv (deriv (fun s => gaussianQuantile (uLine s))) 0 =
      gaussianQuantile (uLine 0) / (gaussianProfile (uLine 0)) ^ 2 * (dU 0) ^ 2 +
        (gaussianProfile (uLine 0))⁻¹ * d2U := by
  let Q := gaussianQuantile
  let I := gaussianProfile
  have hqfirstAt (s : ℝ) : deriv Q (uLine s) = (I (uLine s))⁻¹ :=
    (hasDerivAt_standardGaussianQuantile (hrange s).1 (hrange s).2).deriv
  have hqfirst_fun : deriv Q ∘ uLine = (fun s => (I (uLine s))⁻¹) := by
    funext s
    exact hqfirstAt s
  have hderivEq : deriv (fun s : ℝ => Q (uLine s)) =
      (fun s => dU s * (I (uLine s))⁻¹) := by
    funext s
    have hq := hasDerivAt_standardGaussianQuantile (hrange s).1 (hrange s).2
    have hc := HasDerivAt.comp s hq (hfirst s)
    calc
      deriv (fun r => Q (uLine r)) s =
          (gaussianProfile (uLine s))⁻¹ * dU s := by
        simpa [Function.comp_def, gaussianQuantile, gaussianProfile,
          standardGaussianIsoperimetricProfile] using hc.deriv
      _ = dU s * (I (uLine s))⁻¹ := by ring
  have hqsecond := hasDerivAt_deriv_standardGaussianQuantile
    (u := uLine 0) (hrange 0).1 (hrange 0).2
  have hqcomp := HasDerivAt.comp (0 : ℝ) hqsecond (hfirst 0)
  have hprod := hqcomp.mul hsecond
  rw [hderivEq]
  have hprod' := hprod.deriv
  rw [hqfirst_fun] at hprod'
  change deriv (dU * (fun s => (I (uLine s))⁻¹)) 0 = _
  simpa [Q, I, pow_two, mul_assoc, mul_left_comm, mul_comm] using hprod'

/-- Differentiability, not only the value of the second derivative, for a
Gaussian quantile composed with a twice differentiable scalar profile. This
strong form supplies the second-variation hypothesis in the paired maximum
principle. -/
theorem hasDerivAt_deriv_gaussianQuantile_comp
    (uLine dU : ℝ → ℝ) (d2U : ℝ)
    (hrange : ∀ s, 0 < uLine s ∧ uLine s < 1)
    (hfirst : ∀ s, HasDerivAt uLine (dU s) s)
    (hsecond : HasDerivAt dU d2U 0) :
    HasDerivAt (fun s => deriv (fun r => gaussianQuantile (uLine r)) s)
      (gaussianQuantile (uLine 0) /
        (gaussianProfile (uLine 0)) ^ 2 * (dU 0) ^ 2 +
        (gaussianProfile (uLine 0))⁻¹ * d2U) 0 := by
  let Q := gaussianQuantile
  let I := gaussianProfile
  have hqfirst_fun : deriv Q ∘ uLine = (fun s => (I (uLine s))⁻¹) := by
    funext s
    exact (hasDerivAt_standardGaussianQuantile (hrange s).1 (hrange s).2).deriv
  have hderivEq : deriv (fun s : ℝ => Q (uLine s)) =
      (fun s => dU s * (I (uLine s))⁻¹) := by
    funext s
    have hq := hasDerivAt_standardGaussianQuantile (hrange s).1 (hrange s).2
    have hc := HasDerivAt.comp s hq (hfirst s)
    calc
      deriv (fun r => Q (uLine r)) s = (I (uLine s))⁻¹ * dU s := by
        simpa [Function.comp_def, Q, I, gaussianQuantile, gaussianProfile,
          standardGaussianIsoperimetricProfile] using hc.deriv
      _ = dU s * (I (uLine s))⁻¹ := by ring
  have hqsecond := hasDerivAt_deriv_standardGaussianQuantile
    (u := uLine 0) (hrange 0).1 (hrange 0).2
  have hqcomp := HasDerivAt.comp (0 : ℝ) hqsecond (hfirst 0)
  have hprod := hqcomp.mul hsecond
  rw [hqfirst_fun] at hprod
  have htarget : (fun s => deriv (fun r => Q (uLine r)) s) =
      (fun s => (I (uLine s))⁻¹ * dU s) := by
    funext s
    rw [hderivEq]
    ring
  have hprod' := hprod.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => congrFun htarget s))
  simpa [Q, I, pow_two, mul_assoc, mul_left_comm, mul_comm] using hprod'

/-- If a smooth scalar mass profile solves the heat equation, its Gaussian
quantile solves Borell's nonlinear heat equation. The hypotheses are given
along each coordinate line so this lemma is directly reusable for finite
products. -/
theorem gaussianQuantile_transformed_heat_equation
    {κ : Type*} [Fintype κ]
    (uTime : ℝ → ℝ) (uLine : κ → ℝ → ℝ)
    (dU : κ → ℝ → ℝ) (d2U : κ → ℝ) (u0 uT t : ℝ)
    (hrange : 0 < u0 ∧ u0 < 1)
    (hrangeLine : ∀ i s, 0 < uLine i s ∧ uLine i s < 1)
    (htimeValue : uTime t = u0)
    (htime : HasDerivAt uTime uT t)
    (hspaceValue : ∀ i, uLine i 0 = u0)
    (hfirst : ∀ i s, HasDerivAt (uLine i) (dU i s) s)
    (hsecond : ∀ i, HasDerivAt (dU i) (d2U i) 0)
    (hheat : uT = (∑ i, d2U i) / 2) :
    deriv (fun s => gaussianQuantile (uTime s)) t =
      (∑ i, deriv (deriv (fun s => gaussianQuantile (uLine i s))) 0 -
        gaussianQuantile u0 *
          (∑ i, (deriv (fun s => gaussianQuantile (uLine i s)) 0) ^ 2)) / 2 := by
  let Q := gaussianQuantile
  let I := gaussianProfile
  let iv := (I u0)⁻¹
  let c := Q u0 / (I u0) ^ 2
  have hIpos : 0 < I u0 := standardGaussianIsoperimetricProfile_pos hrange.1 hrange.2
  have hQtime : HasDerivAt (fun s => Q (uTime s)) (iv * uT) t := by
    have hq : HasDerivAt Q iv (uTime t) := by
      rw [htimeValue]
      exact hasDerivAt_standardGaussianQuantile hrange.1 hrange.2
    have h := HasDerivAt.comp t hq htime
    simpa [Function.comp_def] using h
  have htimeDeriv : deriv (fun s => Q (uTime s)) t = iv * uT := hQtime.deriv
  have hgrad (i : κ) : deriv (fun s => Q (uLine i s)) 0 = iv * dU i 0 := by
    have hq : HasDerivAt Q iv (uLine i 0) := by
      rw [hspaceValue i]
      exact hasDerivAt_standardGaussianQuantile hrange.1 hrange.2
    have h := HasDerivAt.comp (0 : ℝ) hq (hfirst i 0)
    simpa [Function.comp_def, iv] using h.deriv
  have hhess (i : κ) :
      deriv (deriv (fun s => Q (uLine i s))) 0 =
        c * (dU i 0) ^ 2 + iv * d2U i := by
    have h := deriv_deriv_gaussianQuantile_comp (uLine i) (dU i)
      (d2U i) (hrangeLine i) (hfirst i) (hsecond i)
    simpa [Q, I, iv, c, hspaceValue i] using h
  have hsumHess :
      (∑ i, deriv (deriv (fun s => Q (uLine i s))) 0) =
        c * (∑ i, (dU i 0) ^ 2) + iv * (∑ i, d2U i) := by
    calc
      (∑ i, deriv (deriv (fun s => Q (uLine i s))) 0) =
          ∑ i, (c * (dU i 0) ^ 2 + iv * d2U i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hhess i
      _ = c * (∑ i, (dU i 0) ^ 2) + iv * (∑ i, d2U i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsumGrad :
      (∑ i, (deriv (fun s => Q (uLine i s)) 0) ^ 2) =
        iv ^ 2 * (∑ i, (dU i 0) ^ 2) := by
    calc
      (∑ i, (deriv (fun s => Q (uLine i s)) 0) ^ 2) =
          ∑ i, (iv * dU i 0) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hgrad i]
      _ = ∑ i, (iv ^ 2 * (dU i 0) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = iv ^ 2 * (∑ i, (dU i 0) ^ 2) := by rw [Finset.mul_sum]
  have hc : c = Q u0 * iv ^ 2 := by
    dsimp [c, iv]
    field_simp
  rw [htimeDeriv, hsumHess, hsumGrad, hheat, hc]
  ring

end BrownianSharp
