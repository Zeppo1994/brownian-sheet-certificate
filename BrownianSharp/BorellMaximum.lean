import BrownianSharp.GaussianCDFCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# The potential-term maximum principle in Borell's heat-flow proof

This module isolates the elementary parabolic contradiction used in Borell's
proof of Ehrhard. The remaining analytic work is to establish the stated
negative-minimum certificate for the Ornstein--Uhlenbeck interpolation; that
certificate is not postulated as an Ehrhard or concentration inequality.
-/

open Set
open Filter
open scoped Topology

namespace BrownianSharp

/-- At a local minimum, the second derivative (when expressed through
`deriv (deriv f)`) cannot be negative. The proof reduces to the standard
second-derivative sufficiency theorem: a negative second derivative would
make the same point a local maximum, forcing the function to be locally
constant and hence its second derivative to vanish. -/
theorem deriv_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hcont : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra hneg
  have hsecond : deriv (deriv f) x < 0 := lt_of_not_ge hneg
  have hfirst : deriv f x = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax f x := isLocalMax_of_deriv_deriv_neg hsecond hfirst hcont
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hdeq : deriv f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hd := heq.deriv
    simpa using hd
  have hdd : deriv (deriv f) x = deriv (fun _ : ℝ => (0 : ℝ)) x := hdeq.deriv_eq
  simp at hdd
  linarith

/-- At the right endpoint of a time interval, a differentiable function that
attains its minimum over the interval has nonpositive derivative. The proof
uses the left-sided slope limit, so it also applies when the minimum occurs at
the terminal time. -/
theorem hasDerivAt_nonpos_of_minOn_Icc_left
    {f : ℝ → ℝ} {f' t T : ℝ}
    (hf : HasDerivAt f f' t) (ht : 0 < t) (htT : t ≤ T)
    (hmin : ∀ s ∈ Set.Icc (0 : ℝ) T, f t ≤ f s) :
    f' ≤ 0 := by
  have hleft : ∀ᶠ s in 𝓝[<] t, slope f t s ≤ 0 := by
    have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
    filter_upwards [inter_mem_nhdsWithin (Set.Iio t) hIoi] with s hs
    have hspos : 0 < s := hs.2
    have hst : s < t := hs.1
    have hsT : s ≤ T := le_trans hst.le htT
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hspos.le, hsT⟩
    have hnum : 0 ≤ f s - f t := sub_nonneg.mpr (hmin s hsIcc)
    have hden : s - t < 0 := sub_neg.mpr hst
    rw [slope_def_field]
    exact div_nonpos_of_nonneg_of_nonpos hnum hden.le
  have htend : Tendsto (slope f t) (𝓝[<] t) (𝓝 f') :=
    hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t)
  exact le_of_tendsto htend hleft

/-- Move both Gaussian input blocks by the same amount in one coordinate.
These are precisely the directions along which the second variation of
Borell's interpolation is nonnegative at a spatial minimum. -/
noncomputable def pairedCoordinateMove {κ : Type*} [DecidableEq κ]
    (z : (κ → ℝ) × (κ → ℝ))
    (i : κ) (s : ℝ) : (κ → ℝ) × (κ → ℝ) :=
  (Function.update z.1 i (z.1 i + s), Function.update z.2 i (z.2 i + s))

/-- Move only the first Gaussian block in one coordinate. -/
noncomputable def firstBlockMove {κ : Type*} [DecidableEq κ]
    (z : (κ → ℝ) × (κ → ℝ)) (i : κ) (s : ℝ) :=
  (Function.update z.1 i (z.1 i + s), z.2)

/-- Move only the second Gaussian block in one coordinate. -/
noncomputable def secondBlockMove {κ : Type*} [DecidableEq κ]
    (z : (κ → ℝ) × (κ → ℝ)) (i : κ) (s : ℝ) :=
  (z.1, Function.update z.2 i (z.2 i + s))

/-- A coordinate update is the corresponding affine line in the product
vector space. -/
theorem update_eq_add_smul_single {κ : Type*} [DecidableEq κ]
    (x : κ → ℝ) (i : κ) (s : ℝ) :
    Function.update x i (x i + s) = x + s • Pi.single i (1 : ℝ) := by
  classical
  ext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

/-- The spatial part of Borell's two-point interpolation. -/
noncomputable def borellCombination {κ : Type*}
    (a b : ℝ) (H F G : (κ → ℝ) → ℝ)
    (z : (κ → ℝ) × (κ → ℝ)) : ℝ :=
  H (a • z.1 + b • z.2) - a * F z.1 - b * G z.2

/-- Time-dependent Borell interpolation, matching the difference used in the
Gaussian heat comparison. -/
noncomputable def borellCombinationFamily {κ : Type*}
    (a b : ℝ) (H F G : ℝ → (κ → ℝ) → ℝ)
    (t : ℝ) (z : (κ → ℝ) × (κ → ℝ)) : ℝ :=
  H t (a • z.1 + b • z.2) - a * F t z.1 - b * G t z.2

/-- Time derivative of the two-point interpolation is the same linear
combination of the three component time derivatives. -/
theorem hasDerivAt_borellCombinationFamily
    {κ : Type*}
    (a b : ℝ) (H F G : ℝ → (κ → ℝ) → ℝ)
    (t dH dF dG : ℝ) (z : (κ → ℝ) × (κ → ℝ))
    (hH : HasDerivAt (fun s => H s (a • z.1 + b • z.2)) dH t)
    (hF : HasDerivAt (fun s => F s z.1) dF t)
    (hG : HasDerivAt (fun s => G s z.2) dG t) :
    HasDerivAt (fun s => borellCombinationFamily a b H F G s z)
      (dH - a * dF - b * dG) t := by
  have h := hH.sub (hF.const_mul a)
  have hh := h.sub (hG.const_mul b)
  convert hh using 1 <;> (try ext s) <;>
    simp [borellCombinationFamily] <;> ring_nf

/-- Coordinate first derivatives in the two independent blocks. -/
noncomputable def firstBlockPartial {κ : Type*} [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ)) (i : κ) :=
  deriv (fun s => f (firstBlockMove z i s)) 0

noncomputable def secondBlockPartial {κ : Type*} [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ)) (i : κ) :=
  deriv (fun s => f (secondBlockMove z i s)) 0

/-- First-coordinate chain rule for Borell's combination, stated in the
directional form supplied by smoothness of the three scalar functions. -/
theorem firstBlockPartial_borellCombination
    {κ : Type*} [DecidableEq κ]
    (a b : ℝ) (H F G : (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ)) (i : κ)
    (dH dF : ℝ)
    (hH : HasDerivAt (fun r : ℝ => H (a • z.1 + b • z.2 + r • Pi.single i (1 : ℝ))) dH (0 : ℝ))
    (hF : HasDerivAt (fun r : ℝ => F (z.1 + r • Pi.single i (1 : ℝ))) dF (0 : ℝ)) :
    firstBlockPartial (borellCombination a b H F G) z i = a * dH - a * dF := by
  classical
  let w := a • z.1 + b • z.2
  let e : κ → ℝ := Pi.single i (1 : ℝ)
  have hscale : HasDerivAt (fun s : ℝ => a * s) a (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  have hHcomp : HasDerivAt (fun s : ℝ => H (w + (a * s) • e))
      (a * dH) (0 : ℝ) := by
    have hH0 : HasDerivAt
        (fun r : ℝ => H (a • z.1 + b • z.2 + r • Pi.single i (1 : ℝ))) dH (a * 0) := by
      simpa using hH
    have h := HasDerivAt.comp (0 : ℝ) hH0 hscale
    simpa [Function.comp_def, w, e, mul_comm] using h
  have hFcomp : HasDerivAt (fun s : ℝ => F (z.1 + s • e)) dF (0 : ℝ) := by
    simpa [e] using hF
  have harg : ∀ s : ℝ,
      a • Function.update z.1 i (z.1 i + s) + b • z.2 = w + (a * s) • e := by
    intro s
    rw [update_eq_add_smul_single]
    dsimp [w, e]
    module
  have hFarg : ∀ s : ℝ,
      Function.update z.1 i (z.1 i + s) = z.1 + s • e := by
    intro s
    rw [update_eq_add_smul_single]
  have hderiv := hHcomp.sub (hFcomp.const_mul a)
  have hderiv' := hderiv.sub_const (b * G z.2)
  have hfun : (fun s : ℝ =>
      borellCombination a b H F G (firstBlockMove z i s)) =
      (fun s => H (w + (a * s) • e) - a * F (z.1 + s • e) - b * G z.2) := by
    funext s
    simp only [borellCombination, firstBlockMove]
    rw [harg s, hFarg s]
  change deriv (fun s : ℝ => borellCombination a b H F G (firstBlockMove z i s)) 0 = _
  rw [hfun]
  exact hderiv'.deriv

/-- Second-coordinate chain rule for Borell's combination. -/
theorem secondBlockPartial_borellCombination
    {κ : Type*} [DecidableEq κ]
    (a b : ℝ) (H F G : (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ)) (i : κ)
    (dH dG : ℝ)
    (hH : HasDerivAt (fun r : ℝ => H (a • z.1 + b • z.2 + r • Pi.single i (1 : ℝ))) dH (0 : ℝ))
    (hG : HasDerivAt (fun r : ℝ => G (z.2 + r • Pi.single i (1 : ℝ))) dG (0 : ℝ)) :
    secondBlockPartial (borellCombination a b H F G) z i = b * dH - b * dG := by
  classical
  let w := a • z.1 + b • z.2
  let e : κ → ℝ := Pi.single i (1 : ℝ)
  have hscale : HasDerivAt (fun s : ℝ => b * s) b (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul b
  have hH0 : HasDerivAt
      (fun r : ℝ => H (a • z.1 + b • z.2 + r • Pi.single i (1 : ℝ))) dH (b * 0) := by
    simpa using hH
  have hHcomp : HasDerivAt (fun s : ℝ => H (w + (b * s) • e))
      (b * dH) (0 : ℝ) := by
    have h := HasDerivAt.comp (0 : ℝ) hH0 hscale
    simpa [Function.comp_def, w, e, mul_comm] using h
  have hGcomp : HasDerivAt (fun s : ℝ => G (z.2 + s • e)) dG (0 : ℝ) := by
    simpa [e] using hG
  have harg : ∀ s : ℝ,
      a • z.1 + b • Function.update z.2 i (z.2 i + s) = w + (b * s) • e := by
    intro s
    rw [update_eq_add_smul_single]
    dsimp [w, e]
    module
  have hGarg : ∀ s : ℝ,
      Function.update z.2 i (z.2 i + s) = z.2 + s • e := by
    intro s
    rw [update_eq_add_smul_single]
  have hderiv := hHcomp.sub (hGcomp.const_mul b)
  have hderiv' := hderiv.sub_const (a * F z.1)
  have hfun : (fun s : ℝ =>
      borellCombination a b H F G (secondBlockMove z i s)) =
      (fun s => H (w + (b * s) • e) - a * F z.1 - b * G (z.2 + s • e)) := by
    funext s
    simp only [borellCombination, secondBlockMove]
    rw [harg s, hGarg s]
  change deriv (fun s : ℝ => borellCombination a b H F G (secondBlockMove z i s)) 0 = _
  rw [hfun]
  have horder : (fun s : ℝ => H (w + (b * s) • e) - a * F z.1 - b * G (z.2 + s • e)) =
      (fun s => (H (w + (b * s) • e) - b * G (z.2 + s • e)) - a * F z.1) := by
    funext s
    ring
  rw [horder]
  exact hderiv'.deriv

/-- Spatial criticality means that all coordinate derivatives in both blocks
vanish. Borell's interpolation equation reduces to its potential-only form at
such points; away from them its drift terms must be retained. -/
def pairedGaussianCritical {κ : Type*} [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ)) : Prop :=
  (∀ i, firstBlockPartial f z i = 0) ∧ (∀ i, secondBlockPartial f z i = 0)

/-- Algebra at a spatial minimum for Borell's two-point interpolation.

The derivative and Laplacian identities are deliberately listed as hypotheses:
they are the chain-rule calculations for
`H(a x + b y) - a F(x) - b G(y)`. The theorem then combines them with the
three transformed heat equations. In particular, the potential-only equation
is obtained only at critical points; this is where the two gradients agree.
This separation makes it impossible to accidentally use that equation away
from a minimum. -/
theorem borellCriticalPoint_potential_equation
    {κ : Type*} [Fintype κ]
    (a b H F G Hlap Flap Glap Ht Ft Gt Vt Vlap Vval : ℝ)
    (dH dF dG : κ → ℝ)
    (firstPartial secondPartial : κ → ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcritical₁ : ∀ i, firstPartial i = a * dH i - a * dF i)
    (hcritical₂ : ∀ i, secondPartial i = b * dH i - b * dG i)
    (hcrit₁ : ∀ i, firstPartial i = 0)
    (hcrit₂ : ∀ i, secondPartial i = 0)
    (hHt : Ht = (Hlap - H * (∑ i, dH i ^ 2)) / 2)
    (hFt : Ft = (Flap - F * (∑ i, dF i ^ 2)) / 2)
    (hGt : Gt = (Glap - G * (∑ i, dG i ^ 2)) / 2)
    (hVt : Vt = Ht - a * Ft - b * Gt)
    (hVlap : Vlap = Hlap - a * Flap - b * Glap)
    (hVval : Vval = H - a * F - b * G) :
    Vt = (Vlap - Vval * (∑ i, dF i ^ 2)) / 2 := by
  have hgradHF : ∀ i, dH i = dF i := by
    intro i
    have hz : a * (dH i - dF i) = 0 := by
      calc
        a * (dH i - dF i) = a * dH i - a * dF i := by ring
        _ = firstPartial i := (hcritical₁ i).symm
        _ = 0 := hcrit₁ i
    rcases mul_eq_zero.mp hz with hzero | heq
    · exact (ha hzero).elim
    · exact sub_eq_zero.mp heq
  have hgradHG : ∀ i, dH i = dG i := by
    intro i
    have hz : b * (dH i - dG i) = 0 := by
      calc
        b * (dH i - dG i) = b * dH i - b * dG i := by ring
        _ = secondPartial i := (hcritical₂ i).symm
        _ = 0 := hcrit₂ i
    rcases mul_eq_zero.mp hz with hzero | heq
    · exact (hb hzero).elim
    · exact sub_eq_zero.mp heq
  have hsqHF : (∑ i, dH i ^ 2) = ∑ i, dF i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hgradHF i]
  have hsqHG : (∑ i, dH i ^ 2) = ∑ i, dG i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hgradHG i]
  have hsqGF : (∑ i, dG i ^ 2) = ∑ i, dF i ^ 2 := by
    calc
      (∑ i, dG i ^ 2) = ∑ i, dH i ^ 2 := hsqHG.symm
      _ = ∑ i, dF i ^ 2 := hsqHF
  rw [hVt, hHt, hFt, hGt, hVlap, hVval, hsqHF, hsqGF]
  ring
/-- Every global minimum is spatially critical, coordinate by coordinate. -/
theorem pairedGaussianCritical_of_globalMin
    {κ : Type*} [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ))
    (hmin : ∀ w, f z ≤ f w) :
    pairedGaussianCritical f z := by
  constructor
  · intro i
    have hlocal : IsLocalMin (fun s => f (firstBlockMove z i s)) 0 := by
      unfold IsLocalMin IsMinFilter
      filter_upwards [] with s
      simpa [firstBlockMove] using hmin (firstBlockMove z i s)
    exact hlocal.deriv_eq_zero
  · intro i
    have hlocal : IsLocalMin (fun s => f (secondBlockMove z i s)) 0 := by
      unfold IsLocalMin IsMinFilter
      filter_upwards [] with s
      simpa [secondBlockMove] using hmin (secondBlockMove z i s)
    exact hlocal.deriv_eq_zero

/-- Restriction of a scalar function on two Gaussian blocks to the paired
coordinate line through `z`. -/
noncomputable def pairedCoordinateLine {κ : Type*} [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ)
    (z : (κ → ℝ) × (κ → ℝ)) (i : κ) : ℝ → ℝ :=
  fun s => f (pairedCoordinateMove z i s)

/-- Second derivative along one paired coordinate direction. -/
noncomputable def pairedCoordinateSecond {κ : Type*} [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ)
    (z : (κ → ℝ) × (κ → ℝ)) (i : κ) : ℝ :=
  deriv (deriv (pairedCoordinateLine f z i)) 0

/-- The diagonal Laplacian used in the Borell minimum calculation. -/
noncomputable def pairedCoordinateLaplacian {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ)) : ℝ :=
  ∑ i : κ, pairedCoordinateSecond f z i

/-- Diagonal second-variation identity for Borell's combination. The linewise
first-derivative hypotheses express ordinary C² regularity of the component
functions. The condition `a+b=1` is exactly what makes the coupled direction
move the argument of `H` at unit speed. -/
theorem pairedCoordinateSecond_borellCombination
    {κ : Type*} [DecidableEq κ]
    (a b : ℝ) (H F G : (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ)) (i : κ)
    (dH dF dG : ℝ → ℝ) (d2H d2F d2G : ℝ)
    (hab : a + b = 1)
    (hHfirst : ∀ s, HasDerivAt (fun r : ℝ => H (a • z.1 + b • z.2 + r • Pi.single i (1 : ℝ))) (dH s) s)
    (hFfirst : ∀ s, HasDerivAt (fun r : ℝ => F (z.1 + r • Pi.single i (1 : ℝ))) (dF s) s)
    (hGfirst : ∀ s, HasDerivAt (fun r : ℝ => G (z.2 + r • Pi.single i (1 : ℝ))) (dG s) s)
    (hHsecond : HasDerivAt dH d2H 0)
    (hFsecond : HasDerivAt dF d2F 0)
    (hGsecond : HasDerivAt dG d2G 0) :
    pairedCoordinateSecond (borellCombination a b H F G) z i =
      d2H - a * d2F - b * d2G := by
  classical
  let e : κ → ℝ := Pi.single i (1 : ℝ)
  let w : κ → ℝ := a • z.1 + b • z.2
  let LH : ℝ → ℝ := fun s => H (w + s • e)
  let LF : ℝ → ℝ := fun s => F (z.1 + s • e)
  let LG : ℝ → ℝ := fun s => G (z.2 + s • e)
  let D : ℝ → ℝ := fun s => dH s - a * dF s - b * dG s
  have harg : ∀ s : ℝ,
      a • Function.update z.1 i (z.1 i + s) +
          b • Function.update z.2 i (z.2 i + s) = w + s • e := by
    intro s
    rw [update_eq_add_smul_single, update_eq_add_smul_single]
    dsimp [w, e]
    ext k
    by_cases hk : k = i
    · subst k
      simp
      linear_combination s * hab
    · simp [hk]
  have hline : pairedCoordinateLine (borellCombination a b H F G) z i =
      (fun s => LH s - a * LF s - b * LG s) := by
    funext s
    simp only [pairedCoordinateLine, borellCombination, pairedCoordinateMove,
      LH, LF, LG]
    rw [harg s]
    rw [update_eq_add_smul_single, update_eq_add_smul_single]
  have hfirst : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => LH r - a * LF r - b * LG r) (D s) s := by
    intro s
    have hh := (hHfirst s).sub ((hFfirst s).const_mul a)
    have hhh := hh.sub ((hGfirst s).const_mul b)
    convert hhh using 1 <;> simp [LH, LF, LG, D]
  have hD : HasDerivAt D (d2H - a * d2F - b * d2G) 0 := by
    have hh := hHsecond.sub (hFsecond.const_mul a)
    have hhh := hh.sub (hGsecond.const_mul b)
    convert hhh using 1 <;> simp [D]
  have hderivLine : deriv (fun s : ℝ => LH s - a * LF s - b * LG s) = D := by
    funext s
    exact (hfirst s).deriv
  rw [pairedCoordinateSecond, hline, hderivLine]
  exact hD.deriv

/-- Summed diagonal Laplacian formula for the Borell combination. -/
theorem pairedCoordinateLaplacian_borellCombination
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a b : ℝ) (H F G : (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ))
    (dH dF dG : κ → ℝ → ℝ) (d2H d2F d2G : κ → ℝ)
    (hab : a + b = 1)
    (hHfirst : ∀ i s, HasDerivAt
      (fun r : ℝ => H (a • z.1 + b • z.2 + r • Pi.single i (1 : ℝ))) (dH i s) s)
    (hFfirst : ∀ i s, HasDerivAt
      (fun r : ℝ => F (z.1 + r • Pi.single i (1 : ℝ))) (dF i s) s)
    (hGfirst : ∀ i s, HasDerivAt
      (fun r : ℝ => G (z.2 + r • Pi.single i (1 : ℝ))) (dG i s) s)
    (hHsecond : ∀ i, HasDerivAt (dH i) (d2H i) 0)
    (hFsecond : ∀ i, HasDerivAt (dF i) (d2F i) 0)
    (hGsecond : ∀ i, HasDerivAt (dG i) (d2G i) 0) :
    pairedCoordinateLaplacian (borellCombination a b H F G) z =
      ∑ i, (d2H i - a * d2F i - b * d2G i) := by
  classical
  unfold pairedCoordinateLaplacian
  apply Finset.sum_congr rfl
  intro i hi
  exact pairedCoordinateSecond_borellCombination a b H F G z i
    (dH i) (dF i) (dG i) (d2H i) (d2F i) (d2G i) hab
    (hHfirst i) (hFfirst i) (hGfirst i)
    (hHsecond i) (hFsecond i) (hGsecond i)

/-- The diagonal Laplacian is nonnegative at every global minimum of a
continuous function. This proves the spatial second-variation part of the
maximum-principle test, rather than assuming the Laplacian sign. -/
theorem pairedCoordinateLaplacian_nonneg_at_globalMin
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : (κ → ℝ) × (κ → ℝ) → ℝ) (z : (κ → ℝ) × (κ → ℝ))
    (hf : Continuous f)
    (hmin : ∀ w, f z ≤ f w) :
    0 ≤ pairedCoordinateLaplacian f z := by
  classical
  unfold pairedCoordinateLaplacian
  apply Finset.sum_nonneg
  intro i hi
  apply deriv_deriv_nonneg_of_isLocalMin
  · unfold IsLocalMin IsMinFilter pairedCoordinateLine
    filter_upwards [] with s
    have h := hmin (pairedCoordinateMove z i s)
    simpa [pairedCoordinateMove] using h
  · have hline : Continuous (pairedCoordinateLine f z i) := by
      unfold pairedCoordinateLine pairedCoordinateMove
      apply hf.comp
      apply Continuous.prodMk
      · apply continuous_pi
        intro k
        by_cases hki : k = i
        · subst k
          simp
          fun_prop
        · simp [Function.update_of_ne hki]
          exact continuous_const
      · apply continuous_pi
        intro k
        by_cases hki : k = i
        · subst k
          simp
          fun_prop
        · simp [Function.update_of_ne hki]
          exact continuous_const
    exact hline.continuousAt

/-- Discharge the minimum-test part of the parabolic argument for functions
of two finite Gaussian coordinate blocks. The time derivative uses the
one-sided endpoint test; the spatial Laplacian is proved nonnegative by the
paired-coordinate second-derivative lemma above. -/
theorem pairedGaussian_parabolic_minimum_tests
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T ε t : ℝ) (z : (κ → ℝ) × (κ → ℝ))
    (V Vt Vlap : ℝ → (κ → ℝ) × (κ → ℝ) → ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (htpos : 0 < t)
    (hVtime : HasDerivAt (fun s => V s z) (Vt t z) t)
    (hVcont : Continuous (V t))
    (hVlap : Vlap t z = pairedCoordinateLaplacian (fun w => V t w) z)
    (hglobal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ w,
    V t z + ε * Real.exp t ≤ V s w + ε * Real.exp s) :
    pairedGaussianCritical (fun w => V t w) z ∧
      Vt t z + ε * Real.exp t ≤ 0 ∧ 0 ≤ Vlap t z := by
  have htimeDeriv : HasDerivAt (fun s => V s z + ε * Real.exp s)
      (Vt t z + ε * Real.exp t) t := by
    have h := hVtime.add ((Real.hasDerivAt_exp t).const_mul ε)
    convert h using 1
  have htimeMin : ∀ s ∈ Set.Icc (0 : ℝ) T,
      V t z + ε * Real.exp t ≤ V s z + ε * Real.exp s := by
    intro s hs
    exact hglobal s hs z
  have htime := hasDerivAt_nonpos_of_minOn_Icc_left htimeDeriv htpos ht.2 htimeMin
  have hspaceMin : ∀ w, (V t z + ε * Real.exp t) ≤ V t w + ε * Real.exp t := by
    intro w
    simpa using hglobal t ht w
  have hspaceCont : Continuous (fun w => V t w + ε * Real.exp t) :=
    hVcont.add continuous_const
  have hlap := pairedCoordinateLaplacian_nonneg_at_globalMin
    (fun w => V t w + ε * Real.exp t) z hspaceCont hspaceMin
  have hcritConst : pairedGaussianCritical (fun w => V t w + ε * Real.exp t) z := by
    apply pairedGaussianCritical_of_globalMin (fun w => V t w + ε * Real.exp t) z hspaceMin
  have hcrit : pairedGaussianCritical (fun w => V t w) z := by
    constructor
    · intro i
      have hc := hcritConst.1 i
      change deriv (fun s => V t (firstBlockMove z i s) + ε * Real.exp t) 0 = 0 at hc
      have heq := deriv_add_const'
        (f := fun s => V t (firstBlockMove z i s)) (ε * Real.exp t)
      change deriv (fun s => V t (firstBlockMove z i s)) 0 = 0
      rw [← heq]
      exact hc
    · intro i
      have hc := hcritConst.2 i
      change deriv (fun s => V t (secondBlockMove z i s) + ε * Real.exp t) 0 = 0 at hc
      have heq := deriv_add_const'
        (f := fun s => V t (secondBlockMove z i s)) (ε * Real.exp t)
      change deriv (fun s => V t (secondBlockMove z i s)) 0 = 0
      rw [← heq]
      exact hc
  constructor
  · exact hcrit
  constructor
  · exact htime
  · rw [hVlap]
    have hsecondEq : ∀ i,
        pairedCoordinateSecond (fun w => V t w + ε * Real.exp t) z i =
          pairedCoordinateSecond (fun w => V t w) z i := by
      intro i
      unfold pairedCoordinateSecond pairedCoordinateLine
      have hinner := deriv_add_const'
        (f := fun s => V t (pairedCoordinateMove z i s)) (ε * Real.exp t)
      rw [hinner]
    simpa [pairedCoordinateLaplacian, hsecondEq] using hlap

/-- Uniform coercivity in the space variable makes a continuous function
attain a global minimum on a finite time slab. This is the compactness step
that turns a negative value into a spacetime minimum. -/
theorem exists_global_minOn_Icc_univ_of_uniformCoercive
    {E : Type*} [PseudoMetricSpace E] [Zero E] [ProperSpace E]
    (T : ℝ) (U : ℝ → E → ℝ)
    (hcont : Continuous (fun p : ℝ × E => U p.1 p.2))
    (hcoercive : ∀ B : ℝ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : E, R < dist x 0 → B < U t x)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : E) :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) T, ∃ x₀ : E,
      ∀ t' ∈ Set.Icc (0 : ℝ) T, ∀ x' : E, U t₀ x₀ ≤ U t' x' := by
  let B := U t x
  obtain ⟨R, hR, hRcoercive⟩ := hcoercive B
  let S : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : E) R
  have hScompact : IsCompact S := isCompact_Icc.prod (isCompact_closedBall (0 : E) R)
  have hSnonempty : S.Nonempty := by
    refine ⟨(t, 0), ?_, ?_⟩
    · exact ht
    · simp [Metric.mem_closedBall, hR]
  obtain ⟨⟨t₀, x₀⟩, hmem, hmin⟩ :=
    hScompact.exists_isMinOn hSnonempty hcont.continuousOn
  have ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T := hmem.1
  have hx₀ : x₀ ∈ Metric.closedBall (0 : E) R := hmem.2
  refine ⟨t₀, ht₀, x₀, ?_⟩
  intro t' ht' x'
  by_cases hx' : x' ∈ Metric.closedBall (0 : E) R
  · have hpair : (t', x') ∈ S := by exact ⟨ht', hx'⟩
    have hm := hmin hpair
    simpa [S] using hm
  · have hout : R < dist x' 0 := by
      simpa [Metric.mem_closedBall] using (lt_of_not_ge hx')
    have htail := hRcoercive t' ht' x' hout
    have hwit : x ∈ Metric.closedBall (0 : E) R := by
      by_contra h
      have hxout : R < dist x 0 := by
        simpa [Metric.mem_closedBall] using (lt_of_not_ge h)
      have hbad := hRcoercive t ht x hxout
      dsimp [B] at hbad
      exact (lt_irrefl _) hbad
    have hwitpair : (t, x) ∈ S := by exact ⟨ht, hwit⟩
    have hminwit : U t₀ x₀ ≤ U t x := by
      have hm := hmin hwitpair
      simpa [S] using hm
    dsimp [B] at htail hminwit
    linarith

/-- A lower-tail bound at one level, above the value of a given witness,
suffices for a global minimum on a finite time slab. Unlike coercivity, this
allows bounded heat-flow interpolants: it is enough that the spatial liminf
be nonnegative uniformly in time. -/
theorem exists_global_minOn_Icc_univ_of_tail_gt_witness
    {E : Type*} [PseudoMetricSpace E] [Zero E] [ProperSpace E]
    (T : ℝ) (U : ℝ → E → ℝ)
    (hcont : Continuous (fun p : ℝ × E => U p.1 p.2))
    {B : ℝ} (htail : ∃ R : ℝ, 0 ≤ R ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : E, R < dist x 0 → B < U t x)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : E)
    (hwitness : U t x < B) :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) T, ∃ x₀ : E,
      (∀ t' ∈ Set.Icc (0 : ℝ) T, ∀ x', U t₀ x₀ ≤ U t' x') ∧
      U t₀ x₀ < B := by
  obtain ⟨R, hR, hRtail⟩ := htail
  let S : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : E) R
  have hScompact : IsCompact S := isCompact_Icc.prod (isCompact_closedBall (0 : E) R)
  have hSnonempty : S.Nonempty := by
    refine ⟨(t, 0), ?_, ?_⟩
    · exact ht
    · simp [Metric.mem_closedBall, hR]
  obtain ⟨⟨t₀, x₀⟩, hmem, hmin⟩ :=
    hScompact.exists_isMinOn hSnonempty hcont.continuousOn
  have ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T := hmem.1
  have hx₀ : x₀ ∈ Metric.closedBall (0 : E) R := hmem.2
  have hminwit : U t₀ x₀ ≤ U t x := by
    have hwitball : x ∈ Metric.closedBall (0 : E) R := by
      by_contra h
      have hout : R < dist x 0 := by
        simpa [Metric.mem_closedBall] using (lt_of_not_ge h)
      have hcontra := hRtail t ht x hout
      linarith
    have hwitpair : (t, x) ∈ S := ⟨ht, hwitball⟩
    have hm := hmin hwitpair
    simpa [S] using hm
  have hglob : ∀ t' ∈ Set.Icc (0 : ℝ) T, ∀ x', U t₀ x₀ ≤ U t' x' := by
    intro t' ht' x'
    by_cases hx' : x' ∈ Metric.closedBall (0 : E) R
    · have hpair : (t', x') ∈ S := ⟨ht', hx'⟩
      have hm := hmin hpair
      simpa [S] using hm
    · have hout : R < dist x' 0 := by
        simpa [Metric.mem_closedBall] using (lt_of_not_ge hx')
      have htail' := hRtail t' ht' x' hout
      linarith
  exact ⟨t₀, ht₀, x₀, hglob, lt_of_le_of_lt hminwit hwitness⟩

/-- A negative minimum for a time-dependent function, with the one-sided time
derivative test and the nonnegative spatial Laplacian test supplied. This is
the exact local calculus package needed by the parabolic comparison lemma. -/
def ParabolicNegativeMinimum {E : Type*} (T : ℝ) (V : ℝ → E → ℝ)
    (Vt Vlap : ℝ → E → ℝ) (critical : ℝ → E → Prop) : Prop :=
  ∀ {ε : ℝ}, 0 < ε →
    (∃ t ∈ Set.Icc (0 : ℝ) T, ∃ x, V t x + ε * Real.exp t < 0) →
      ∃ t₀ ∈ Set.Icc (0 : ℝ) T, ∃ x₀,
        V t₀ x₀ + ε * Real.exp t₀ < 0 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          V t₀ x₀ + ε * Real.exp t₀ ≤ V t x + ε * Real.exp t) ∧
        critical t₀ x₀ ∧
        (Vt t₀ x₀ + ε * Real.exp t₀ ≤ 0) ∧
        (0 ≤ Vlap t₀ x₀)

/-- Under uniform coercivity, every negative value of the exponentially
perturbed function gives an attained negative global minimum. The remaining
input `htest` is the ordinary one-sided-time / spatial-second-derivative test
at such a minimum. -/
theorem parabolicNegativeMinimum_of_uniformLiminf
    {E : Type*} [PseudoMetricSpace E] [Zero E] [ProperSpace E]
    (T : ℝ) (V Vt Vlap : ℝ → E → ℝ) (critical : ℝ → E → Prop)
    (hinitial : ∀ x, 0 ≤ V 0 x)
    (hcont : ∀ {ε : ℝ}, 0 < ε →
      Continuous (fun p : ℝ × E => V p.1 p.2 + ε * Real.exp p.1))
    (hliminf : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 ≤ R ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : E, R < dist x 0 → -η < V t x)
    (htest : ∀ {ε : ℝ}, 0 < ε → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : E,
      V t x + ε * Real.exp t < 0 →
      (∀ t' ∈ Set.Icc (0 : ℝ) T, ∀ x',
        V t x + ε * Real.exp t ≤ V t' x' + ε * Real.exp t') →
      0 < t → critical t x ∧ Vt t x + ε * Real.exp t ≤ 0 ∧ 0 ≤ Vlap t x) :
    ParabolicNegativeMinimum T V Vt Vlap critical := by
  intro ε hε ⟨t, ht, x, hneg⟩
  let U : ℝ → E → ℝ := fun s y => V s y + ε * Real.exp s
  have hUcont : Continuous (fun p : ℝ × E => U p.1 p.2) := by
    simpa [U] using hcont hε
  let η : ℝ := -(U t x) / 2
  have hη : 0 < η := by dsimp [η, U]; linarith
  let B : ℝ := -η
  have hwitness : U t x < B := by dsimp [B, η]; linarith
  obtain ⟨R, hR, htailV⟩ := hliminf η hη
  have htailU : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : E,
      R < dist y 0 → B < U s y := by
    intro s hs y hy
    have hlow := htailV s hs y hy
    have hexp : 0 < ε * Real.exp s := mul_pos hε (Real.exp_pos s)
    dsimp [U, B]
    linarith
  have htail : ∃ R' : ℝ, 0 ≤ R' ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : E, R' < dist y 0 → B < U s y :=
    ⟨R, hR, htailU⟩
  obtain ⟨t₀, ht₀, x₀, hglob, hUneg⟩ :=
    exists_global_minOn_Icc_univ_of_tail_gt_witness T U hUcont htail ht x hwitness
  have hBneg : B < 0 := by dsimp [B]; linarith
  have hUneg0 : U t₀ x₀ < 0 := lt_trans hUneg hBneg
  have ht₀zero : t₀ ≠ 0 := by
    intro hz
    subst t₀
    have hnonneg : 0 ≤ U 0 x₀ := by
      have hbase := hinitial x₀
      have hexp : 0 < ε * Real.exp 0 := mul_pos hε (Real.exp_pos 0)
      dsimp [U]
      linarith
    exact (not_lt_of_ge hnonneg) hUneg0
  have ht₀pos : 0 < t₀ := by
    rcases lt_or_eq_of_le ht₀.1 with hpos | heq
    · exact hpos
    · exact False.elim (ht₀zero heq.symm)
  obtain ⟨hcritical, htestTime, htestSpace⟩ := htest hε t₀ ht₀ x₀ hUneg0 hglob ht₀pos
  exact ⟨t₀, ht₀, x₀, hUneg0, hglob, hcritical, htestTime, htestSpace⟩

/-- If a heat-flow interpolation satisfies
`V_t = (Vlap - V q)/2` with a nonnegative potential, then an attained
negative perturbed minimum is impossible. This is the maximum-principle core
of Borell's PDE argument. -/
theorem nonneg_of_heatEquation_of_parabolicNegativeMinimum
    {E : Type*} (T : ℝ) (V Vt Vlap q : ℝ → E → ℝ)
    (critical : ℝ → E → Prop)
    (hinitial : ∀ x, 0 ≤ V 0 x)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ q t x)
    (hpde : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, critical t x →
      Vt t x = (Vlap t x - V t x * q t x) / 2)
    (hmin : ParabolicNegativeMinimum T V Vt Vlap critical) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ V t x := by
  intro t ht x
  by_contra hnot
  have hneg : V t x < 0 := lt_of_not_ge hnot
  let ε : ℝ := -V t x / (2 * Real.exp t)
  have hexp : 0 < Real.exp t := Real.exp_pos t
  have hε : 0 < ε := by
    dsimp [ε]
    apply div_pos
    · linarith
    · positivity
  have hpert : V t x + ε * Real.exp t < 0 := by
    dsimp [ε]
    field_simp
    linarith
  obtain ⟨t₀, ht₀, x₀, hUneg, _hglobal, hcritical, htime, hlap⟩ :=
    hmin hε ⟨t, ht, x, hpert⟩
  have ht₀zero : t₀ ≠ 0 := by
    intro hz
    subst t₀
    have hbase := hinitial x₀
    have hcontr : 0 ≤ V 0 x₀ + ε * Real.exp 0 := by
      have he : 0 < ε * Real.exp 0 := mul_pos hε (Real.exp_pos 0)
      linarith
    exact (not_lt_of_ge hcontr) hUneg
  have ht₀pos : 0 < t₀ := by
    have hleft := ht₀.1
    rcases lt_or_eq_of_le hleft with hpos | heq
    · exact hpos
    · exact False.elim (ht₀zero heq.symm)
  have ht₀Ioc : t₀ ∈ Set.Ioc (0 : ℝ) T := ⟨ht₀pos, ht₀.2⟩
  have hpotential := hq t₀ ht₀ x₀
  have hode := hpde t₀ ht₀Ioc x₀ hcritical
  have hU : V t₀ x₀ + ε * Real.exp t₀ < 0 := hUneg
  have htimepos : 0 < Vt t₀ x₀ + ε * Real.exp t₀ := by
    have hterm : 0 < ε * Real.exp t₀ := mul_pos hε (Real.exp_pos t₀)
    have hVneg : V t₀ x₀ < 0 := by
      have : 0 < ε * Real.exp t₀ := hterm
      linarith
    rw [hode]
    have hnum : 0 < Vlap t₀ x₀ - V t₀ x₀ * q t₀ x₀ := by
      have hprod : 0 ≤ (-V t₀ x₀) * q t₀ x₀ :=
        mul_nonneg (le_of_lt (neg_pos.mpr hVneg)) hpotential
      linarith
    have hhalf : 0 < (Vlap t₀ x₀ - V t₀ x₀ * q t₀ x₀) / 2 := by
      positivity
    linarith
  exact (not_lt_of_ge htime) htimepos

/-- The weak parabolic maximum principle with the bounded-at-infinity
compactness route used in Borell's proof. Its side conditions are continuity,
nonnegative initial data, uniform nonnegative spatial liminf, and the usual
differential tests at a negative global minimum. -/
theorem nonneg_of_heatEquation_of_uniformLiminf
    {E : Type*} [PseudoMetricSpace E] [Zero E] [ProperSpace E]
    (T : ℝ) (V Vt Vlap q : ℝ → E → ℝ) (critical : ℝ → E → Prop)
    (hinitial : ∀ x, 0 ≤ V 0 x)
    (hcont : ∀ {ε : ℝ}, 0 < ε →
      Continuous (fun p : ℝ × E => V p.1 p.2 + ε * Real.exp p.1))
    (hliminf : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 ≤ R ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : E, R < dist x 0 → -η < V t x)
    (htest : ∀ {ε : ℝ}, 0 < ε → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : E,
      V t x + ε * Real.exp t < 0 →
      (∀ t' ∈ Set.Icc (0 : ℝ) T, ∀ x',
        V t x + ε * Real.exp t ≤ V t' x' + ε * Real.exp t') →
      0 < t → critical t x ∧ Vt t x + ε * Real.exp t ≤ 0 ∧ 0 ≤ Vlap t x)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : E, 0 ≤ q t x)
    (hpde : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, critical t x →
      Vt t x = (Vlap t x - V t x * q t x) / 2) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ V t x := by
  apply nonneg_of_heatEquation_of_parabolicNegativeMinimum T V Vt Vlap q critical
    hinitial hq hpde
  exact parabolicNegativeMinimum_of_uniformLiminf T V Vt Vlap critical hinitial
    hcont hliminf htest

/-- Instantiation of the parabolic maximum principle on two finite Gaussian
coordinate blocks. Here the spatial derivative-test premises are discharged
by the paired diagonal Laplacian lemma and the time endpoint slope lemma. -/
theorem pairedGaussian_nonneg_of_heatEquation_of_uniformLiminf
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : ℝ) (V Vt Vlap q : ℝ → (κ → ℝ) × (κ → ℝ) → ℝ)
    (hinitial : ∀ z, 0 ≤ V 0 z)
    (hjoint : Continuous (fun p : ℝ × ((κ → ℝ) × (κ → ℝ)) => V p.1 p.2))
    (hsection : ∀ t, Continuous (V t))
    (hVtime : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ z,
      HasDerivAt (fun s => V s z) (Vt t z) t)
    (hVlap : ∀ t z,
      Vlap t z = pairedCoordinateLaplacian (fun w => V t w) z)
    (hliminf : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 ≤ R ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z,
        R < dist z 0 → -η < V t z)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z, 0 ≤ q t z)
    (hpde : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ z,
      pairedGaussianCritical (fun w => V t w) z →
      Vt t z = (Vlap t z - V t z * q t z) / 2)
    [ProperSpace ((κ → ℝ) × (κ → ℝ))] :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z, 0 ≤ V t z := by
  apply nonneg_of_heatEquation_of_uniformLiminf T V Vt Vlap q
    (fun t z => pairedGaussianCritical (fun w => V t w) z) hinitial
  · intro ε hε
    exact hjoint.add (continuous_const.mul (Real.continuous_exp.comp continuous_fst))
  · exact hliminf
  · intro ε hε t ht z hneg hglobal htpos
    have htIoc : t ∈ Set.Ioc (0 : ℝ) T := ⟨htpos, ht.2⟩
    exact pairedGaussian_parabolic_minimum_tests T ε t z V Vt Vlap ht htpos
      (hVtime t htIoc z) (hsection t) (hVlap t z) hglobal
  · exact hq
  · exact hpde

end BrownianSharp
