import BrownianSharp.GaussianHeatTime
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Spatial derivatives of finite-dimensional Gaussian heat averages

For a compactly supported `C²` test function, differentiation of the Gaussian
heat average twice along a fixed direction is reduced to the existing first
variation theorem, applied to the directional derivative of the test function.
This is the spatial half of the heat equation used by the Borell interpolation.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace BrownianSharp

/-- A constant plus a continuously differentiable compactly supported
perturbation has bounded value and bounded derivative. Its derivative itself
has compact support, which is the exact hypothesis needed by the second
variation theorem below. -/
theorem compactPerturb_heatInput_bounds {κ : Type*} [Fintype κ]
    (p : (κ → ℝ) → ℝ) (c : ℝ) (hp : ContDiff ℝ 1 p)
    (hpc : HasCompactSupport p) :
    HasCompactSupport (fderiv ℝ (fun x => c + p x)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖c + p x‖ ≤ C) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (fun y => c + p y) x‖ ≤ C) := by
  have hdfp : HasCompactSupport (fderiv ℝ p) := hpc.fderiv (𝕜 := ℝ)
  have hdf : HasCompactSupport (fderiv ℝ (fun x => c + p x)) := by
    convert hdfp using 1
    ext x w
    exact congrArg (fun L : (κ → ℝ) →L[ℝ] ℝ => L w)
      (fderiv_const_add (𝕜 := ℝ) (f := p) (x := x) c)
  have hpv : Continuous p := hp.continuous
  have hpd : Continuous (fderiv ℝ p) := hp.continuous_fderiv (by norm_num)
  obtain ⟨Cp, hCp⟩ := hpv.bounded_above_of_compact_support hpc
  obtain ⟨Cd, hCd⟩ := hpd.bounded_above_of_compact_support hdfp
  refine ⟨hdf, ?_, ?_⟩
  · refine ⟨|c| + max Cp 0, by positivity, ?_⟩
    intro x
    calc
      ‖c + p x‖ ≤ |c| + ‖p x‖ := norm_add_le _ _
      _ ≤ |c| + max Cp 0 := by
        gcongr
        exact (hCp x).trans (le_max_left _ _)
  · refine ⟨max Cd 0, le_max_right _ _, ?_⟩
    intro x
    rw [fderiv_const_add]
    exact (hCd x).trans (le_max_left _ _)

noncomputable def heatDirectional (q : (κ → ℝ) → ℝ) (v : κ → ℝ) :
    (κ → ℝ) → ℝ := fun x => fderiv ℝ q x v

private theorem contDiff_heatDirectional {κ : Type*} [Fintype κ]
    {q : (κ → ℝ) → ℝ} (_hq : ContDiff ℝ 2 q) (v : κ → ℝ) :
    ContDiff ℝ 1 (heatDirectional q v) := by
  have h := _hq.contDiff_fderiv_apply (m := 1) (n := 2) (by norm_num)
  have hmap : ContDiff ℝ 1 (fun x : (κ → ℝ) => (x, v)) := by
    fun_prop
  change ContDiff ℝ 1 (fun x => (fderiv ℝ q x) v)
  exact h.comp hmap

private theorem compactSupport_heatDirectional {κ : Type*} [Fintype κ]
    {q : (κ → ℝ) → ℝ} (hdf : HasCompactSupport (fderiv ℝ q))
    (v : κ → ℝ) :
    HasCompactSupport (heatDirectional q v) := by
  exact hdf.comp_left (g := fun L : (κ → ℝ) →L[ℝ] ℝ => L v) (by simp)

private theorem heatDirectional_bounds {κ : Type*} [Fintype κ]
    {q : (κ → ℝ) → ℝ} (hq : ContDiff ℝ 2 q)
    (hdf : HasCompactSupport (fderiv ℝ q)) (v : κ → ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖heatDirectional q v y‖ ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ (heatDirectional q v) y‖ ≤ C) := by
  have hqv : HasCompactSupport (heatDirectional q v) :=
    compactSupport_heatDirectional hdf v
  have hqvc : Continuous (heatDirectional q v) :=
    (contDiff_heatDirectional hq v).continuous
  have hqvd : Continuous (fderiv ℝ (heatDirectional q v)) :=
    (contDiff_heatDirectional hq v).continuous_fderiv (by norm_num)
  obtain ⟨Cqv, hCqv⟩ := hqvc.bounded_above_of_compact_support hqv
  obtain ⟨Cqvd, hCqvd⟩ := hqvd.bounded_above_of_compact_support (hqv.fderiv (𝕜 := ℝ))
  refine ⟨?_, ?_⟩
  · refine ⟨max Cqv 0, le_max_right _ _, ?_⟩
    intro y
    exact (hCqv y).trans (le_max_left _ _)
  · refine ⟨max Cqvd 0, le_max_right _ _, ?_⟩
    intro y
    exact (hCqvd y).trans (le_max_left _ _)

/-- First spatial derivative of a finite-product Gaussian heat average at an
arbitrary parameter value, obtained by translating the base point in the
first-variation formula. -/
theorem hasDerivAt_gaussianHeat_directional_line
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ) (t : ℝ)
    (x v : κ → ℝ) (s : ℝ) (hq : ContDiff ℝ 1 q)
    (hq_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖q y‖ ≤ C)
    (hderiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ q y‖ ≤ C) :
    HasDerivAt (fun r : ℝ => gaussianHeat q t (x + r • v))
      (gaussianHeat (heatDirectional q v) t (x + s • v)) s := by
  have hfirst := hasDerivAt_gaussianHeat_directional_of_bounded_deriv
    q t (x + s • v) v hq hq_bound hderiv_bound
  have hshift : HasDerivAt (fun r : ℝ => r - s) 1 s := by
    convert (hasDerivAt_id s).add_const (-s) using 1
    · ext r
      dsimp [id]
      ring
  have hcomp := HasDerivAt.comp_of_eq s hfirst hshift (by simp)
  convert hcomp using 1
  · ext r
    simp only [Function.comp_apply, gaussianHeat]
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    simp only [sub_smul]
    abel
  · simp [gaussianHeat, heatDirectional]

/-- Twice differentiate finite-dimensional Gaussian heat along one direction.
The second derivative is the heat average of the derivative of the first
variation; the formula is deliberately phrased with `fderiv` so it composes
with the product-coordinate Laplacian without choosing a Euclidean basis. -/
theorem hasDerivAt_deriv_gaussianHeat_directional
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ) (t : ℝ)
    (x v : κ → ℝ) (hq : ContDiff ℝ 2 q) (hdf : HasCompactSupport (fderiv ℝ q))
    (hq_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖q y‖ ≤ C)
    (hderiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ q y‖ ≤ C) :
    HasDerivAt (fun s : ℝ => deriv (fun r : ℝ =>
        gaussianHeat q t (x + r • v)) s)
      (∫ z, fderiv ℝ (heatDirectional q v)
        (x + Real.sqrt t • z) v ∂productStandardGaussian κ) 0 := by
  let qv := heatDirectional q v
  have hqvC : ContDiff ℝ 1 qv := contDiff_heatDirectional hq v
  have hqv_bounds := heatDirectional_bounds hq hdf v
  have hqv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖qv y‖ ≤ C := hqv_bounds.1
  have hqv_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ qv y‖ ≤ C :=
    hqv_bounds.2
  have hline_deriv (s : ℝ) : HasDerivAt (fun r : ℝ =>
      gaussianHeat q t (x + r • v)) (gaussianHeat qv t (x + s • v)) s := by
    have hqC1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
    simpa [qv] using hasDerivAt_gaussianHeat_directional_line q t x v s
      hqC1 hq_bound hderiv_bound
  have hderiv_eq : (fun s : ℝ => deriv (fun r : ℝ =>
      gaussianHeat q t (x + r • v)) s) =
      (fun s : ℝ => gaussianHeat qv t (x + s • v)) := by
    funext s
    exact (hline_deriv s).deriv
  have hsecond := hasDerivAt_gaussianHeat_directional_of_bounded_deriv
      qv t x v hqvC hqv_bound hqv_deriv_bound
  simpa [hderiv_eq] using hsecond

end BrownianSharp
