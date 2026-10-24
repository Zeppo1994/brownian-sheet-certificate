import BrownianSharp.AlignmentGaussianChaining
import Mathlib.MeasureTheory.Measure.Continuity

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BrownianSharp.AlignmentEndpointCubeGridLimit

open BrownianSharp BrownianSharp.AlignmentGaussianChaining
open HaarQuarter

def cubeDyadicRefine {d M : ℕ} (j : CubeDyadicGrid d M) : CubeDyadicGrid d (M+1) :=
  fun i => ⟨(j i).val*2, by
    have hj : (j i).val ≤ 2^M := by omega
    rw [pow_succ]
    omega⟩

theorem cubeDyadicAnchor_refine {d M : ℕ} (j : CubeDyadicGrid d M) :
    cubeDyadicAnchor (cubeDyadicRefine j) = cubeDyadicAnchor j := by
  ext i
  simp only [cubeDyadicAnchor, cubeDyadicRefine]
  rw [pow_succ]
  push_cast
  ring

theorem cubeGridMaximum_le_succ {d : ℕ} (M : ℕ) (f : C(BrownianCubeAnchor d,ℝ)) :
    cubeGridMaximum M f ≤ cubeGridMaximum (M+1) f := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro j
  have h := norm_le_pi_norm
    (fun l : CubeDyadicGrid d (M+1) => f (cubeDyadicAnchor l)) (cubeDyadicRefine j)
  simpa only [cubeGridMaximum, Function.comp_apply, cubeDyadicAnchor_refine] using h

theorem cubeGridMaximum_mono {d : ℕ} {M N : ℕ} (hMN : M≤N)
    (f : C(BrownianCubeAnchor d,ℝ)) : cubeGridMaximum M f ≤ cubeGridMaximum N f := by
  induction hMN with
  | refl => exact le_rfl
  | @step N h ih => exact ih.trans (cubeGridMaximum_le_succ N f)

/-- Uniform norm mass follows from uniform lower bounds on the nested finite
dyadic grid events. The proof uses continuity of the sample paths and
measure continuity from above; it has no Gaussian hypotheses. -/
theorem cube_grid_mass_lower_to_uniform_mass_lower
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → C(BrownianCubeAnchor d,ℝ)) (hF : Measurable F)
    (ε : ℝ) (hε : 0≤ε) (c : ℝ≥0∞)
    (hgrid : ∀ M : ℕ,
      c ≤ P {ω | cubeGridMaximum M (F ω) ≤ ε}) :
    c ≤ P {ω | ‖F ω‖ ≤ ε} := by
  classical
  let A : ℕ → Set Ω := fun M => {ω | cubeGridMaximum M (F ω) ≤ ε}
  have hAm : ∀ M, MeasurableSet (A M) := by
    intro M
    exact measurableSet_le ((cubeGridMaximum_continuous M).measurable.comp hF)
      measurable_const
  have hanti : Antitone A := by
    intro M N hMN ω hω
    change cubeGridMaximum N (F ω) ≤ ε at hω
    change cubeGridMaximum M (F ω) ≤ ε
    exact (cubeGridMaximum_mono hMN (F ω)).trans hω
  have hinter : (⋂ M, A M) = {ω | ‖F ω‖ ≤ ε} := by
    ext ω
    constructor
    · intro hω
      apply (ContinuousMap.norm_le _ hε).2
      intro x
      let g := F ω
      let v : ℕ → ℝ := fun M => |g (cubeDyadicApprox M x)|
      have hlim : Tendsto v atTop (𝓝 |g x|) := by
        dsimp [v, g]
        exact (g.continuous.tendsto x).abs.comp (cubeDyadicApprox_tendsto x)
      have hval : ∀ M, v M ≤ ε := by
        intro M
        have hgridM : cubeGridMaximum M g ≤ ε := by
          simpa [A, g] using (Set.mem_iInter.mp hω M)
        have hcoord : |g (cubeDyadicApprox M x)| ≤ cubeGridMaximum M g := by
          simpa only [cubeGridMaximum, cubeDyadicApprox, Real.norm_eq_abs] using
            (norm_le_pi_norm (fun j : CubeDyadicGrid d M => g (cubeDyadicAnchor j))
              (cubeDyadicChoice M x))
        exact hcoord.trans hgridM
      have hclosed : IsClosed (Set.Iic ε) := isClosed_Iic
      have hev : ∀ᶠ M : ℕ in atTop, v M ∈ Set.Iic ε :=
        Filter.Eventually.of_forall (fun M => hval M)
      have hmem := hclosed.mem_of_tendsto hlim hev
      simpa only [Set.mem_Iic, g, Real.norm_eq_abs] using hmem
    · intro hω
      apply Set.mem_iInter.mpr
      intro M
      change cubeGridMaximum M (F ω) ≤ ε
      have hnorm : cubeGridMaximum M (F ω) ≤ ‖F ω‖ :=
        cubeGridMaximum_le_norm M (F ω)
      exact hnorm.trans hω
  rw [← hinter, hanti.measure_iInter (fun M => (hAm M).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  apply le_iInf
  intro M
  exact hgrid M

end BrownianSharp.AlignmentEndpointCubeGridLimit
