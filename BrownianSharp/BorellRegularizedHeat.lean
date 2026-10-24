import BrownianSharp.GaussianHeatSpatial
import BrownianSharp.GaussianQuantileHeatPDE
import BrownianSharp.GaussianHeatTraceProved
import BrownianSharp.BorellInfinity
import BrownianSharp.BorellMaximum
import BrownianSharp.BorellRegularization
import BrownianSharp.BorellSetLimit
import BrownianSharp.BorellSetExtension

/-!
# Assembly of the regularized Borell inequality from the heat trace equation

The sole analytic premise here is the ordinary finite-product Gaussian heat
trace identity for a constant plus a smooth compactly supported perturbation.
All range, derivative, endpoint, spatial-infinity, and maximum-principle work
is discharged in this module.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology ContDiff

namespace BrownianSharp
open Concentration

/-- Finite-product Gaussian heat trace equation, stated only for the exact
constant-plus-compact-perturbation inputs used in Borell regularization. -/
def GaussianHeatTracePDE (κ : Type*) [Fintype κ] [DecidableEq κ] : Prop :=
  ∀ (c : ℝ) (p : (κ → ℝ) → ℝ), ContDiff ℝ 2 p → HasCompactSupport p →
    ∀ (x : κ → ℝ) (t : ℝ), 0 < t →
      HasDerivAt (fun s : ℝ => gaussianHeat (fun y => c + p y) s x)
        ((∑ i, ∫ z, fderiv ℝ
          (fun y => fderiv ℝ (fun w => c + p w) y (Pi.single i (1 : ℝ)))
          (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
          ∂productStandardGaussian κ) / 2) t

noncomputable def gaussianQuantileHeat {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (t : ℝ) (x : κ → ℝ) : ℝ :=
  standardGaussianQuantile (gaussianHeat q t x)

noncomputable def gaussianQuantileHeatLine {κ : Type*} [Fintype κ]
    [DecidableEq κ]
    (q : (κ → ℝ) → ℝ) (t : ℝ) (x : κ → ℝ) (i : κ) (s : ℝ) : ℝ :=
  gaussianQuantileHeat q t (x + s • Pi.single i (1 : ℝ))

private theorem gaussianHeat_const_add {κ : Type*} [Fintype κ]
    (p : (κ → ℝ) → ℝ) (c t : ℝ) (x : κ → ℝ)
    (hp : Continuous p) (hpc : HasCompactSupport p) :
    gaussianHeat (fun y => c + p y) t x = c + gaussianHeat p t x := by
  have hpBound0 := hp.bounded_above_of_compact_support hpc
  let Cp := max hpBound0.choose 0
  have hpBound (y : κ → ℝ) : ‖p y‖ ≤ Cp :=
    (hpBound0.choose_spec y).trans (le_max_left _ _)
  have hpi : Integrable (fun z : κ → ℝ => p (x + Real.sqrt t • z))
      (productStandardGaussian κ) :=
    gaussianHeat_integrable_of_bounded p hp t x hpBound
  rw [gaussianHeat]
  calc
    (∫ z, c + p (x + Real.sqrt t • z) ∂productStandardGaussian κ) =
        (∫ _z, c ∂productStandardGaussian κ) +
          ∫ z, p (x + Real.sqrt t • z) ∂productStandardGaussian κ :=
      integral_add (integrable_const c) hpi
    _ = c + gaussianHeat p t x := by simp [gaussianHeat]

private theorem continuous_gaussianHeat_const_add {κ : Type*} [Fintype κ]
    (p : (κ → ℝ) → ℝ) (c : ℝ) (hp : Continuous p)
    (hpc : HasCompactSupport p) :
    Continuous (fun u : ℝ × (κ → ℝ) =>
      gaussianHeat (fun y => c + p y) u.1 u.2) := by
  have hpJoint := continuous_gaussianHeat_of_continuous_compactSupport p hp hpc
  have hEq : (fun u : ℝ × (κ → ℝ) =>
      gaussianHeat (fun y => c + p y) u.1 u.2) =
      (fun u => c + gaussianHeat p u.1 u.2) := by
    funext u
    exact gaussianHeat_const_add p c u.1 u.2 hp hpc
  rw [hEq]
  exact continuous_const.add hpJoint

private theorem continuous_gaussianQuantileHeat_const_add {κ : Type*} [Fintype κ]
    (p : (κ → ℝ) → ℝ) (c lo hi : ℝ) (hp : Continuous p)
    (hpc : HasCompactSupport p) (hlo : 0 < lo) (hhi : hi < 1)
    (hrange : ∀ x, c + p x ∈ Set.Icc lo hi) :
    Continuous (fun u : ℝ × (κ → ℝ) =>
      standardGaussianQuantile (gaussianHeat (fun y => c + p y) u.1 u.2)) := by
  have hmass : Continuous (fun u : ℝ × (κ → ℝ) =>
      gaussianHeat (fun y => c + p y) u.1 u.2) :=
    continuous_gaussianHeat_const_add p c hp hpc
  rw [continuous_iff_continuousAt]
  intro u
  have hval : gaussianHeat (fun y => c + p y) u.1 u.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    have hr := gaussianHeat_mem_Icc (fun y => c + p y)
      (by fun_prop) (fun x => hrange x) u.1 u.2
    exact ⟨lt_of_lt_of_le hlo hr.1, lt_of_le_of_lt hr.2 hhi⟩
  have hQ := standardGaussianQuantile_continuousAt hval.1 hval.2
  have hm : ContinuousAt
      (fun w : ℝ × (κ → ℝ) => gaussianHeat (fun y => c + p y) w.1 w.2) u :=
    hmass.continuousAt
  change ContinuousAt
    (fun w : ℝ × (κ → ℝ) =>
      standardGaussianQuantile (gaussianHeat (fun y => c + p y) w.1 w.2)) u
  exact ContinuousAt.comp_of_eq hQ hm rfl

private theorem hasDerivAt_gaussianHeat_const_add_line
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ) (t : ℝ)
    (x v : κ → ℝ) (s : ℝ) (hq : ContDiff ℝ 1 q)
    (hqBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖q y‖ ≤ C)
    (hdBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ q y‖ ≤ C) :
    HasDerivAt (fun r : ℝ => gaussianHeat q t (x + r • v))
      (gaussianHeat (fun y => fderiv ℝ q y v) t (x + s • v)) s :=
  hasDerivAt_gaussianHeat_directional_line q t x v s hq hqBound hdBound


/-- Scalar quantile heat profile satisfies Borell's nonlinear PDE under the
finite-product Gaussian trace identity. The proof supplies the mass ranges,
first spatial derivatives, and second-variation formulas from the actual heat
integrals; only the trace identity is conditional. -/
theorem gaussianQuantileHeat_pde_of_trace
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (htrace : GaussianHeatTracePDE κ)
    (c : ℝ) (p : (κ → ℝ) → ℝ) (hp : ContDiff ℝ 2 p)
    (hpc : HasCompactSupport p) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : hi < 1)
    (hrange : ∀ x, c + p x ∈ Set.Icc lo hi)
    (t : ℝ) (ht : 0 < t) (x : κ → ℝ) :
    deriv (fun s : ℝ => gaussianQuantileHeat (fun y => c + p y) s x) t =
      ((∑ i, deriv (fun s : ℝ =>
          deriv (fun r : ℝ => gaussianQuantileHeatLine
            (fun y => c + p y) t x i r) s) 0) -
        gaussianQuantileHeat (fun y => c + p y) t x *
          (∑ i, (deriv (fun s : ℝ => gaussianQuantileHeatLine
            (fun y => c + p y) t x i s) 0) ^ 2)) / 2 := by
  let q : (κ → ℝ) → ℝ := fun y => c + p y
  have hp1 : ContDiff ℝ 1 p := hp.of_le (by norm_num)
  have hq : ContDiff ℝ 2 q := by
    fun_prop
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  obtain ⟨hqdf, hqBound, hqDtheBound⟩ :=
    compactPerturb_heatInput_bounds p c hp1 hpc
  have htime := htrace c p hp hpc x t ht
  let uTime : ℝ → ℝ := fun s => gaussianHeat q s x
  let uLine : κ → ℝ → ℝ := fun i s =>
    gaussianHeat q t (x + s • Pi.single i (1 : ℝ))
  let dU : κ → ℝ → ℝ := fun i s => deriv (uLine i) s
  let d2U : κ → ℝ := fun i =>
    ∫ z, fderiv ℝ (fun y => fderiv ℝ q y (Pi.single i (1 : ℝ)))
      (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
      ∂productStandardGaussian κ
  let u₀ := gaussianHeat q t x
  have huRange : u₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    have hr := gaussianHeat_mem_Icc q hq.continuous hrange t x
    exact ⟨lt_of_lt_of_le hlo hr.1, lt_of_le_of_lt hr.2 hhi⟩
  have huLineRange (i : κ) (s : ℝ) : uLine i s ∈ Set.Ioo (0 : ℝ) 1 := by
    have hr := gaussianHeat_mem_Icc q hq.continuous hrange t
      (x + s • Pi.single i (1 : ℝ))
    exact ⟨lt_of_lt_of_le hlo hr.1, lt_of_le_of_lt hr.2 hhi⟩
  have htimeValue : uTime t = u₀ := rfl
  have htimeQ : HasDerivAt uTime
      ((∑ i, ∫ z, fderiv ℝ
        (fun y => fderiv ℝ q y (Pi.single i (1 : ℝ)))
        (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
        ∂productStandardGaussian κ) / 2) t := by
    simpa [uTime, q] using htime
  have hfirst (i : κ) (s : ℝ) : HasDerivAt (uLine i)
      (dU i s) s := by
    have h := hasDerivAt_gaussianHeat_directional_line
      q t x (Pi.single i (1 : ℝ)) s hq1 hqBound hqDtheBound
    convert h using 1
    exact h.deriv
  have hsecond (i : κ) : HasDerivAt (dU i)
      (∫ z, fderiv ℝ
        (fun y => fderiv ℝ q y (Pi.single i (1 : ℝ)))
        (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
        ∂productStandardGaussian κ) 0 := by
    have h := hasDerivAt_deriv_gaussianHeat_directional q t x
      (Pi.single i (1 : ℝ)) hq hqdf hqBound hqDtheBound
    have hdir : heatDirectional q (Pi.single i (1 : ℝ)) =
        (fun y => fderiv ℝ p y (Pi.single i (1 : ℝ))) := by
      funext y
      simp [heatDirectional, q, fderiv_const_add]
    rw [hdir] at h
    simpa [dU, uLine, d2U, q, fderiv_const_add] using h
  have hheat : (∑ i, d2U i) / 2 =
      (∑ i, ∫ z, fderiv ℝ
        (fun y => fderiv ℝ q y (Pi.single i (1 : ℝ)))
        (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
        ∂productStandardGaussian κ) / 2 := by
    rfl
  have htraceEq : deriv uTime t = (∑ i, d2U i) / 2 := by
    rw [htimeQ.deriv]
  have htime' : HasDerivAt uTime (deriv uTime t) t := by
    convert htimeQ using 1
  have hquantile := gaussianQuantile_transformed_heat_equation
      uTime uLine dU d2U u₀ (deriv uTime t) t huRange
      huLineRange htimeValue htime'
      (by intro i; simp [uLine, u₀]) hfirst hsecond htraceEq
  simpa [uTime, u₀, q, gaussianQuantileHeat, gaussianQuantileHeatLine] using hquantile

set_option maxHeartbeats 2000000 in
/-- Derivative data for one actual regularized quantile heat profile. The
second-variation hypotheses needed by the two-point interpolation are proved,
not postulated. -/
theorem gaussianQuantileHeat_derivative_data_of_trace
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (htrace : GaussianHeatTracePDE κ)
    (c : ℝ) (p : (κ → ℝ) → ℝ) (hp : ContDiff ℝ 2 p)
    (hpc : HasCompactSupport p) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : hi < 1)
    (hrange : ∀ x, c + p x ∈ Set.Icc lo hi)
    (t : ℝ) (ht : 0 < t) (x : κ → ℝ) :
    let q : (κ → ℝ) → ℝ := fun y => c + p y
    let dQ : κ → ℝ → ℝ := fun i s => deriv (fun r : ℝ =>
      gaussianQuantileHeatLine q t x i r) s
    let d2Q : κ → ℝ := fun i => deriv (dQ i) 0
    (HasDerivAt (fun s : ℝ => gaussianQuantileHeat q s x)
      (deriv (fun s => gaussianQuantileHeat q s x) t) t) ∧
    (∀ i s, HasDerivAt (fun r : ℝ => gaussianQuantileHeatLine q t x i r)
      (dQ i s) s) ∧
    (∀ i, HasDerivAt (dQ i) (d2Q i) 0) ∧
    deriv (fun s : ℝ => gaussianQuantileHeat q s x) t =
      ((∑ i, d2Q i) - gaussianQuantileHeat q t x *
        (∑ i, (dQ i 0) ^ 2)) / 2 := by
  dsimp only
  let q : (κ → ℝ) → ℝ := fun y => c + p y
  let dQ : κ → ℝ → ℝ := fun i s => deriv (fun r : ℝ =>
    gaussianQuantileHeatLine q t x i r) s
  let d2Q : κ → ℝ := fun i => deriv (dQ i) 0
  have hp1 : ContDiff ℝ 1 p := hp.of_le (by norm_num)
  have hq : ContDiff ℝ 2 q := by fun_prop
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  obtain ⟨hqdf, hqBound, hqDtheBound⟩ :=
    compactPerturb_heatInput_bounds p c hp1 hpc
  have hmassTime := htrace c p hp hpc x t ht
  have hu : gaussianHeat q t x ∈ Set.Ioo (0 : ℝ) 1 := by
    have hr := gaussianHeat_mem_Icc q hq.continuous hrange t x
    exact ⟨lt_of_lt_of_le hlo hr.1, lt_of_le_of_lt hr.2 hhi⟩
  have htimeComp := HasDerivAt.comp t
    (hasDerivAt_standardGaussianQuantile hu.1 hu.2) hmassTime
  have htimeQ : HasDerivAt (fun s : ℝ => gaussianQuantileHeat q s x)
      (deriv (fun s : ℝ => gaussianQuantileHeat q s x) t) t := by
    change HasDerivAt (fun s => standardGaussianQuantile (gaussianHeat q s x))
      (deriv (fun s => standardGaussianQuantile (gaussianHeat q s x)) t) t
    exact htimeComp.congr_deriv htimeComp.deriv.symm
  have huLine (i : κ) (s : ℝ) :
      gaussianHeat q t (x + s • Pi.single i (1 : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 := by
    have hr := gaussianHeat_mem_Icc q hq.continuous hrange t
      (x + s • Pi.single i (1 : ℝ))
    exact ⟨lt_of_lt_of_le hlo hr.1, lt_of_le_of_lt hr.2 hhi⟩
  have hmassFirst (i : κ) (s : ℝ) : HasDerivAt
      (fun r : ℝ => gaussianHeat q t (x + r • Pi.single i (1 : ℝ)))
      (deriv (fun r : ℝ => gaussianHeat q t (x + r • Pi.single i (1 : ℝ))) s) s := by
    have h := hasDerivAt_gaussianHeat_directional_line q t x
      (Pi.single i (1 : ℝ)) s hq1 hqBound hqDtheBound
    convert h using 1
    exact h.deriv
  have hlineFirst (i : κ) (s : ℝ) : HasDerivAt
      (fun r : ℝ => gaussianQuantileHeatLine q t x i r)
      (dQ i s) s := by
    have h := HasDerivAt.comp s
      (hasDerivAt_standardGaussianQuantile (huLine i s).1 (huLine i s).2)
      (hmassFirst i s)
    change HasDerivAt
      (fun r => standardGaussianQuantile (gaussianHeat q t
        (x + r • Pi.single i (1 : ℝ))))
      (deriv (fun r => standardGaussianQuantile (gaussianHeat q t
        (x + r • Pi.single i (1 : ℝ))) ) s) s
    exact h.congr_deriv h.deriv.symm
  have hmassSecond (i : κ) : HasDerivAt
      (fun s : ℝ => deriv (fun r : ℝ =>
        gaussianHeat q t (x + r • Pi.single i (1 : ℝ))) s)
      (∫ z, fderiv ℝ
        (fun y => fderiv ℝ q y (Pi.single i (1 : ℝ)))
        (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
        ∂productStandardGaussian κ) 0 := by
    have h := hasDerivAt_deriv_gaussianHeat_directional q t x
      (Pi.single i (1 : ℝ)) hq hqdf hqBound hqDtheBound
    have hdir : heatDirectional q (Pi.single i (1 : ℝ)) =
        (fun y => fderiv ℝ p y (Pi.single i (1 : ℝ))) := by
      funext y
      simp [heatDirectional, q, fderiv_const_add]
    rw [hdir] at h
    simpa [q] using h
  have hlineSecond (i : κ) : HasDerivAt (dQ i) (d2Q i) 0 := by
    have h := hasDerivAt_deriv_gaussianQuantile_comp
      (uLine := fun s => gaussianHeat q t
        (x + s • Pi.single i (1 : ℝ)))
      (dU := fun s => deriv (fun r : ℝ => gaussianHeat q t
        (x + r • Pi.single i (1 : ℝ))) s)
      (d2U := ∫ z, fderiv ℝ
        (fun y => fderiv ℝ q y (Pi.single i (1 : ℝ)))
        (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
        ∂productStandardGaussian κ)
      (fun s => ⟨(huLine i s).1, (huLine i s).2⟩)
      (hmassFirst i) (hmassSecond i)
    have hval := deriv_deriv_gaussianQuantile_comp
      (uLine := fun s => gaussianHeat q t
        (x + s • Pi.single i (1 : ℝ)))
      (dU := fun s => deriv (fun r : ℝ => gaussianHeat q t
        (x + r • Pi.single i (1 : ℝ))) s)
      (d2U := ∫ z, fderiv ℝ
        (fun y => fderiv ℝ q y (Pi.single i (1 : ℝ)))
        (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
        ∂productStandardGaussian κ)
      (fun s => ⟨(huLine i s).1, (huLine i s).2⟩)
      (hmassFirst i) (hmassSecond i)
    have h' : HasDerivAt (dQ i) (d2Q i) 0 := by
      apply h.congr_deriv
      exact hval.symm
    exact h'
  have hPDE := gaussianQuantileHeat_pde_of_trace htrace c p hp hpc hlo hhi hrange t ht x
  have hpde' : deriv (fun s : ℝ => gaussianQuantileHeat q s x) t =
      ((∑ i, d2Q i) - gaussianQuantileHeat q t x *
        (∑ i, (dQ i 0) ^ 2)) / 2 := by
    simpa [dQ, d2Q, q, gaussianQuantileHeatLine] using hPDE
  exact ⟨htimeQ, hlineFirst, hlineSecond, hpde'⟩

set_option maxHeartbeats 3000000

/-- Borell's full regularized Gaussian functional inequality follows from the
finite-product Gaussian heat trace equation. In particular, the range controls,
initial condition, behavior at infinity, and all differential tests are
proved for the literal compactly supported smooth perturbations. -/
theorem regularizedGaussianFunctional_of_heatTrace
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (htrace : GaussianHeatTracePDE κ) :
    RegularizedGaussianFunctionalInequality κ := by
  intro a b ha hb hab F G H hFsmooth hGsmooth hHsmooth hFcompact hGcompact hHcompact
    hFRange hGRange hHRange δ α β hδ hα hδα hβ hβα hbase1 hbase2 hinit
  let pF : (κ → ℝ) → ℝ := fun x => (α - δ) * F x
  let pG : (κ → ℝ) → ℝ := fun x => (α - δ) * G x
  let pH : (κ → ℝ) → ℝ := fun x => (α - β) * H x
  let qF : (κ → ℝ) → ℝ := fun x => δ + pF x
  let qG : (κ → ℝ) → ℝ := fun x => δ + pG x
  let qH : (κ → ℝ) → ℝ := fun x => β + pH x
  have hpF : ContDiff ℝ 2 pF := by
    have hF2 : ContDiff ℝ 2 F := (contDiff_infty.mp hFsmooth) 2
    simpa [pF] using ContDiff.const_smul (α - δ) hF2
  have hpG : ContDiff ℝ 2 pG := by
    have hG2 : ContDiff ℝ 2 G := (contDiff_infty.mp hGsmooth) 2
    simpa [pG] using ContDiff.const_smul (α - δ) hG2
  have hpH : ContDiff ℝ 2 pH := by
    have hH2 : ContDiff ℝ 2 H := (contDiff_infty.mp hHsmooth) 2
    simpa [pH] using ContDiff.const_smul (α - β) hH2
  have hpFc : HasCompactSupport pF := by
    exact hFcompact.comp_left (g := fun r : ℝ => (α - δ) * r) (by simp)
  have hpGc : HasCompactSupport pG := by
    exact hGcompact.comp_left (g := fun r : ℝ => (α - δ) * r) (by simp)
  have hpHc : HasCompactSupport pH := by
    exact hHcompact.comp_left (g := fun r : ℝ => (α - β) * r) (by simp)
  have hqFRange : ∀ x, qF x ∈ Set.Icc δ α := by
    intro x
    exact borell_regularization_mem_Icc (hFRange x) hδα
  have hqGRange : ∀ x, qG x ∈ Set.Icc δ α := by
    intro x
    exact borell_regularization_mem_Icc (hGRange x) hδα
  have hqHRange : ∀ x, qH x ∈ Set.Icc β α := by
    intro x
    exact borell_regularization_mem_Icc (hHRange x) hβα
  have hδ1 : δ < 1 := hδα.trans_lt hα
  have hβ1 : β < 1 := hβα.trans_lt hα
  let QF : ℝ → (κ → ℝ) → ℝ := fun t x => gaussianQuantileHeat qF t x
  let QG : ℝ → (κ → ℝ) → ℝ := fun t x => gaussianQuantileHeat qG t x
  let QH : ℝ → (κ → ℝ) → ℝ := fun t x => gaussianQuantileHeat qH t x
  let V : ℝ → (κ → ℝ) × (κ → ℝ) → ℝ :=
    fun t z => borellCombinationFamily a b QH QF QG t z
  let Vt : ℝ → (κ → ℝ) × (κ → ℝ) → ℝ := fun t z => deriv (fun s => V s z) t
  let Vlap : ℝ → (κ → ℝ) × (κ → ℝ) → ℝ :=
    fun t z => pairedCoordinateLaplacian (fun w => V t w) z
  let dHF : ℝ → (κ → ℝ) → κ → ℝ → ℝ := fun t x i s =>
    deriv (fun r : ℝ => QH t (x + r • Pi.single i (1 : ℝ))) s
  let dFF : ℝ → (κ → ℝ) → κ → ℝ → ℝ := fun t x i s =>
    deriv (fun r : ℝ => QF t (x + r • Pi.single i (1 : ℝ))) s
  let dGF : ℝ → (κ → ℝ) → κ → ℝ → ℝ := fun t x i s =>
    deriv (fun r : ℝ => QG t (x + r • Pi.single i (1 : ℝ))) s
  let d2HF : ℝ → (κ → ℝ) → κ → ℝ := fun t x i => deriv (dHF t x i) 0
  let d2FF : ℝ → (κ → ℝ) → κ → ℝ := fun t x i => deriv (dFF t x i) 0
  let d2GF : ℝ → (κ → ℝ) → κ → ℝ := fun t x i => deriv (dGF t x i) 0
  let potential : ℝ → (κ → ℝ) × (κ → ℝ) → ℝ := fun t z =>
    ∑ i, (dFF t z.1 i 0) ^ 2
  have hQFjoint : Continuous (fun u : ℝ × (κ → ℝ) => QF u.1 u.2) := by
    apply continuous_gaussianQuantileHeat_const_add pF δ δ α
      (hFsmooth.continuous.const_mul (α - δ)) hpFc hδ hα
    intro x
    exact hqFRange x
  have hQGjoint : Continuous (fun u : ℝ × (κ → ℝ) => QG u.1 u.2) := by
    apply continuous_gaussianQuantileHeat_const_add pG δ δ α
      (hGsmooth.continuous.const_mul (α - δ)) hpGc hδ hα
    intro x
    exact hqGRange x
  have hQHjoint : Continuous (fun u : ℝ × (κ → ℝ) => QH u.1 u.2) := by
    apply continuous_gaussianQuantileHeat_const_add pH β β α
      (hHsmooth.continuous.const_mul (α - β)) hpHc hβ hα
    intro x
    exact hqHRange x
  have hVjoint : Continuous (fun u : ℝ × ((κ → ℝ) × (κ → ℝ)) => V u.1 u.2) := by
    simp only [V, borellCombinationFamily]
    have harg : Continuous (fun u : ℝ × ((κ → ℝ) × (κ → ℝ)) =>
        (u.1, a • u.2.1 + b • u.2.2)) := by fun_prop
    have hHcomp := hQHjoint.comp harg
    have hFcomp : Continuous (fun u : ℝ × ((κ → ℝ) × (κ → ℝ)) => QF u.1 u.2.1) := by
      have hargF : Continuous (fun u : ℝ × ((κ → ℝ) × (κ → ℝ)) => (u.1, u.2.1)) := by fun_prop
      exact hQFjoint.comp hargF
    have hGcomp : Continuous (fun u : ℝ × ((κ → ℝ) × (κ → ℝ)) => QG u.1 u.2.2) := by
      have hargG : Continuous (fun u : ℝ × ((κ → ℝ) × (κ → ℝ)) => (u.1, u.2.2)) := by fun_prop
      exact hQGjoint.comp hargG
    fun_prop
  have hsection (t : ℝ) : Continuous (V t) := by
    have heval : Continuous (fun z : (κ → ℝ) × (κ → ℝ) => (t, z)) := by fun_prop
    exact (hVjoint.comp heval)
  have hinitial : ∀ z, 0 ≤ V 0 z := by
    intro z
    have h := hinit z.1 z.2
    change 0 ≤ borellCombinationFamily a b QH QF QG 0 z
    simp only [borellCombinationFamily, QH, QF, QG, gaussianQuantileHeat,
      qH, qF, qG, pH, pF, pG, gaussianHeat_zero]
    linarith [h]
  have hliminf : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 ≤ R ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z,
        R < dist z 0 → -η < V t z := by
    obtain ⟨Rf, hRfpos, hRf⟩ := hFcompact.exists_pos_le_norm
    obtain ⟨Rg, hRgpos, hRg⟩ := hGcompact.exists_pos_le_norm
    have hfout : ∀ x, Rf < ‖x‖ → qF x = δ := by
      intro x hx
      simp [qF, pF, hRf x (le_of_lt hx)]
    have hgout : ∀ x, Rg < ‖x‖ → qG x = δ := by
      intro x hx
      simp [qG, pG, hRg x (le_of_lt hx)]
    intro η hη
    obtain ⟨R, hR⟩ := borellHeatDifference_uniform_liminf a b ha hb hab qF qG qH
      (by fun_prop) (by fun_prop) (by fun_prop)
      (Rf := Rf) (Rg := Rg) (T := 1) hδ hα hδα hβ hβα (by norm_num)
      hqFRange hqGRange hqHRange hfout hgout hbase1 hbase2 η hη
    refine ⟨max R 0, le_max_right _ _, ?_⟩
    intro t ht z hz
    have hz' : R < ‖z‖ := by
      have hz'' : R < dist z 0 := lt_of_le_of_lt (le_max_left _ _) hz
      simpa using hz''
    have hRz := hR t ht z hz'
    simpa [V, borellCombinationFamily, QH, QF, QG, borellHeatDifference,
      gaussianQuantileHeat] using hRz
  have hqpot : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z, 0 ≤ potential t z := by
    intro t ht z
    dsimp [potential]
    exact Finset.sum_nonneg fun i hi => sq_nonneg (dFF t z.1 i 0)
  have hVtime : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      HasDerivAt (fun s => V s z) (Vt t z) t := by
    intro t ht z
    have hH := gaussianQuantileHeat_derivative_data_of_trace htrace
      β pH hpH hpHc hβ hα hqHRange t ht.1 (a • z.1 + b • z.2)
    have hF := gaussianQuantileHeat_derivative_data_of_trace htrace
      δ pF hpF hpFc hδ hα hqFRange t ht.1 z.1
    have hG := gaussianQuantileHeat_derivative_data_of_trace htrace
      δ pG hpG hpGc hδ hα hqGRange t ht.1 z.2
    have hcomb := hasDerivAt_borellCombinationFamily a b QH QF QG t
      (deriv (fun s => QH s (a • z.1 + b • z.2)) t)
      (deriv (fun s => QF s z.1) t) (deriv (fun s => QG s z.2) t) z
      hH.1 hF.1 hG.1
    have hcombV : HasDerivAt (fun s => V s z)
        (deriv (fun s => QH s (a • z.1 + b • z.2)) t -
          a * deriv (fun s => QF s z.1) t - b * deriv (fun s => QG s z.2) t) t := by
      convert hcomb using 1
    exact hcombV.congr_deriv (by
      simpa [Vt] using hcombV.deriv.symm)
  have hVlap : ∀ t z, Vlap t z = pairedCoordinateLaplacian (fun w => V t w) z := by
    intro t z
    rfl
  have hpde : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      pairedGaussianCritical (fun w => V t w) z →
      Vt t z = (Vlap t z - V t z * potential t z) / 2 := by
    intro t ht z hcritical
    have hH := gaussianQuantileHeat_derivative_data_of_trace htrace
      β pH hpH hpHc hβ hα hqHRange t ht.1 (a • z.1 + b • z.2)
    have hF := gaussianQuantileHeat_derivative_data_of_trace htrace
      δ pF hpF hpFc hδ hα hqFRange t ht.1 z.1
    have hG := gaussianQuantileHeat_derivative_data_of_trace htrace
      δ pG hpG hpGc hδ hα hqGRange t ht.1 z.2
    let Hsp : (κ → ℝ) → ℝ := QH t
    let Fsp : (κ → ℝ) → ℝ := QF t
    let Gsp : (κ → ℝ) → ℝ := QG t
    have hHfirst : ∀ i s, HasDerivAt
        (fun r : ℝ => Hsp (a • z.1 + b • z.2 + r • Pi.single i (1 : ℝ)))
        (dHF t (a • z.1 + b • z.2) i s) s := by
      intro i s
      simpa [Hsp, QH, dHF, gaussianQuantileHeatLine] using hH.2.1 i s
    have hFfirst : ∀ i s, HasDerivAt
        (fun r : ℝ => Fsp (z.1 + r • Pi.single i (1 : ℝ)))
        (dFF t z.1 i s) s := by
      intro i s
      simpa [Fsp, QF, dFF, gaussianQuantileHeatLine] using hF.2.1 i s
    have hGfirst : ∀ i s, HasDerivAt
        (fun r : ℝ => Gsp (z.2 + r • Pi.single i (1 : ℝ)))
        (dGF t z.2 i s) s := by
      intro i s
      simpa [Gsp, QG, dGF, gaussianQuantileHeatLine] using hG.2.1 i s
    have hHsecond : ∀ i, HasDerivAt (dHF t (a • z.1 + b • z.2) i)
        (d2HF t (a • z.1 + b • z.2) i) 0 := by
      intro i
      simpa [dHF, d2HF, QH, gaussianQuantileHeatLine] using hH.2.2.1 i
    have hFsecond : ∀ i, HasDerivAt (dFF t z.1 i) (d2FF t z.1 i) 0 := by
      intro i
      simpa [dFF, d2FF, QF, gaussianQuantileHeatLine] using hF.2.2.1 i
    have hGsecond : ∀ i, HasDerivAt (dGF t z.2 i) (d2GF t z.2 i) 0 := by
      intro i
      simpa [dGF, d2GF, QG, gaussianQuantileHeatLine] using hG.2.2.1 i
    have hlap := pairedCoordinateLaplacian_borellCombination a b Hsp Fsp Gsp z
      (dHF t (a • z.1 + b • z.2)) (dFF t z.1) (dGF t z.2)
      (d2HF t (a • z.1 + b • z.2)) (d2FF t z.1) (d2GF t z.2)
      hab hHfirst hFfirst hGfirst hHsecond hFsecond hGsecond
    have hcrit1 : ∀ i, firstBlockPartial
        (borellCombination a b Hsp Fsp Gsp) z i = 0 := hcritical.1
    have hcrit2 : ∀ i, secondBlockPartial
        (borellCombination a b Hsp Fsp Gsp) z i = 0 := hcritical.2
    have hpartial1 : ∀ i, firstBlockPartial
        (borellCombination a b Hsp Fsp Gsp) z i =
          a * dHF t (a • z.1 + b • z.2) i 0 - a * dFF t z.1 i 0 := by
      intro i
      exact firstBlockPartial_borellCombination a b Hsp Fsp Gsp z i
        (dHF t (a • z.1 + b • z.2) i 0) (dFF t z.1 i 0)
        (hHfirst i 0) (hFfirst i 0)
    have hpartial2 : ∀ i, secondBlockPartial
        (borellCombination a b Hsp Fsp Gsp) z i =
          b * dHF t (a • z.1 + b • z.2) i 0 - b * dGF t z.2 i 0 := by
      intro i
      exact secondBlockPartial_borellCombination a b Hsp Fsp Gsp z i
        (dHF t (a • z.1 + b • z.2) i 0) (dGF t z.2 i 0)
        (hHfirst i 0) (hGfirst i 0)
    have hVtcalc : Vt t z =
        (deriv (fun s => QH s (a • z.1 + b • z.2)) t) -
          a * (deriv (fun s => QF s z.1) t) -
          b * (deriv (fun s => QG s z.2) t) := by
      have h := hasDerivAt_borellCombinationFamily a b QH QF QG t
        (deriv (fun s => QH s (a • z.1 + b • z.2)) t)
        (deriv (fun s => QF s z.1) t) (deriv (fun s => QG s z.2) t) z
        hH.1 hF.1 hG.1
      change deriv (fun s => borellCombinationFamily a b QH QF QG s z) t = _
      simpa [borellCombinationFamily] using h.deriv
    have hVlapcalc : Vlap t z =
        (∑ i : κ, d2HF t (a • z.1 + b • z.2) i) -
          a * (∑ i : κ, d2FF t z.1 i) - b * (∑ i : κ, d2GF t z.2 i) := by
      change pairedCoordinateLaplacian (borellCombination a b Hsp Fsp Gsp) z = _
      calc
        pairedCoordinateLaplacian (borellCombination a b Hsp Fsp Gsp) z =
            ∑ i : κ, (d2HF t (a • z.1 + b • z.2) i -
              a * d2FF t z.1 i - b * d2GF t z.2 i) := by exact hlap
        _ = (∑ i : κ, d2HF t (a • z.1 + b • z.2) i) -
              a * (∑ i : κ, d2FF t z.1 i) - b * (∑ i : κ, d2GF t z.2 i) := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum]
    have hVval : V t z = Hsp (a • z.1 + b • z.2) - a * Fsp z.1 - b * Gsp z.2 := by
      rfl
    have hPDE := borellCriticalPoint_potential_equation a b
      (Hsp (a • z.1 + b • z.2)) (Fsp z.1) (Gsp z.2)
      (∑ i, d2HF t (a • z.1 + b • z.2) i)
      (∑ i, d2FF t z.1 i) (∑ i, d2GF t z.2 i)
      (deriv (fun s => QH s (a • z.1 + b • z.2)) t)
      (deriv (fun s => QF s z.1) t) (deriv (fun s => QG s z.2) t)
      (Vt t z) (Vlap t z) (V t z)
      (dHF t (a • z.1 + b • z.2) · 0)
      (dFF t z.1 · 0) (dGF t z.2 · 0)
      (firstBlockPartial (borellCombination a b Hsp Fsp Gsp) z)
      (secondBlockPartial (borellCombination a b Hsp Fsp Gsp) z)
      (ne_of_gt ha) (ne_of_gt hb) hpartial1 hpartial2 hcrit1 hcrit2
      (by simpa [Hsp, QH, dHF, d2HF, gaussianQuantileHeatLine] using hH.2.2.2)
      (by simpa [Fsp, QF, dFF, d2FF, gaussianQuantileHeatLine] using hF.2.2.2)
      (by simpa [Gsp, QG, dGF, d2GF, gaussianQuantileHeatLine] using hG.2.2.2)
      hVtcalc hVlapcalc hVval
    simpa [Vt, Vlap, V, potential, borellCombinationFamily, Hsp, Fsp, Gsp,
      dFF, d2FF, QH, QF, QG, gaussianQuantileHeatLine] using hPDE
  have hnonneg := pairedGaussian_nonneg_of_heatEquation_of_uniformLiminf
    (κ := κ) 1 V Vt Vlap potential hinitial hVjoint hsection hVtime hVlap
    hliminf hqpot hpde
  have hbase := hnonneg 1 (by norm_num) (0, 0)
  have hquant : a * gaussianQuantileHeat qF 1 0 +
      b * gaussianQuantileHeat qG 1 0 ≤ gaussianQuantileHeat qH 1 0 := by
    have hbase' := hbase
    change 0 ≤ borellCombinationFamily a b QH QF QG 1 (0, 0) at hbase'
    simp only [borellCombinationFamily, QH, QF, QG, smul_zero, add_zero] at hbase'
    linarith
  have hIF := borell_plateau_integral_mem_Icc F hFsmooth.continuous hFRange
  have hIG := borell_plateau_integral_mem_Icc G hGsmooth.continuous hGRange
  have hIH := borell_plateau_integral_mem_Icc H hHsmooth.continuous hHRange
  have hmassF : (∫ x, qF x ∂productStandardGaussian κ) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [integral_borell_regularization _ F (borell_plateau_integrable F hFsmooth.continuous hFRange)]
    have h := borell_regularization_mem_Icc hIF hδα
    exact ⟨lt_of_lt_of_le hδ h.1, lt_of_le_of_lt h.2 hα⟩
  have hmassG : (∫ x, qG x ∂productStandardGaussian κ) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [integral_borell_regularization _ G (borell_plateau_integrable G hGsmooth.continuous hGRange)]
    have h := borell_regularization_mem_Icc hIG hδα
    exact ⟨lt_of_lt_of_le hδ h.1, lt_of_le_of_lt h.2 hα⟩
  have hmassH : (∫ x, qH x ∂productStandardGaussian κ) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [integral_borell_regularization _ H (borell_plateau_integrable H hHsmooth.continuous hHRange)]
    have h := borell_regularization_mem_Icc hIH hβα
    exact ⟨lt_of_lt_of_le hβ h.1, lt_of_le_of_lt h.2 hα⟩
  have hmeanF : gaussianHeat qF 1 0 = ∫ x, qF x ∂productStandardGaussian κ := by
    simp [gaussianHeat, Real.sqrt_one]
  have hmeanG : gaussianHeat qG 1 0 = ∫ x, qG x ∂productStandardGaussian κ := by
    simp [gaussianHeat, Real.sqrt_one]
  have hmeanH : gaussianHeat qH 1 0 = ∫ x, qH x ∂productStandardGaussian κ := by
    simp [gaussianHeat, Real.sqrt_one]
  have hCDF := standardGaussianCDF_strictMono.monotone hquant
  have hquantF : gaussianQuantileHeat qF 1 0 = standardGaussianQuantile
      (∫ x, qF x ∂productStandardGaussian κ) := by
    simp [gaussianQuantileHeat, hmeanF]
  have hquantG : gaussianQuantileHeat qG 1 0 = standardGaussianQuantile
      (∫ x, qG x ∂productStandardGaussian κ) := by
    simp [gaussianQuantileHeat, hmeanG]
  have hquantH : gaussianQuantileHeat qH 1 0 = standardGaussianQuantile
      (∫ x, qH x ∂productStandardGaussian κ) := by
    simp [gaussianQuantileHeat, hmeanH]
  rw [hquantF, hquantG, hquantH,
    standardGaussianCDF_standardGaussianQuantile hmassH.1 hmassH.2] at hCDF
  simp only [qF, pF, qG, pG, qH, pH] at hCDF
  exact hCDF

/-- The regularized Gaussian functional inequality is unconditional: the sole
heat-trace premise used above is discharged by finite-product Gaussian
integration by parts. -/
theorem regularizedGaussianFunctional_of_gaussianHeatTrace
    {κ : Type*} [Fintype κ] [DecidableEq κ] :
    RegularizedGaussianFunctionalInequality κ := by
  apply regularizedGaussianFunctional_of_heatTrace
  simpa [GaussianHeatTracePDE] using gaussianHeatTracePDE_proved κ

/-- Finite-dimensional Gaussian Ehrhard follows from the proved heat trace,
the two-point heat maximum principle, and the regularized-set limit. -/
theorem gaussianEhrhard_of_gaussianHeatTrace
    {κ : Type*} [Fintype κ] :
    GaussianEhrhard (κ → ℝ) (productStandardGaussian κ) := by
  classical
  exact gaussianEhrhard_of_regularizedFunctional
    regularizedGaussianFunctional_of_gaussianHeatTrace

end BrownianSharp
