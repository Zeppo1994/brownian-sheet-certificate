import BrownianSharp.BrownianGaussianL2Closure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open MeasureTheory ProbabilityTheory Filter Topology

namespace HaarQuarter

universe u v

theorem centeredGaussian_on_coordinateSpan
    {Ω : Type v} {J : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : J → Ω → ℝ)
    (hB : ∀ j, MemLp (B j) 2 P)
    (hjoint : ∀ s : Finset J,
      HasGaussianLaw (fun ω (i : s) => B i.1 ω) P)
    (hmean : ∀ j, ∫ ω, B j ω ∂P = 0) :
    let S : Submodule ℝ (Lp ℝ 2 P) :=
      Submodule.span ℝ (Set.range fun j => (hB j).toLp (B j))
    ∀ y : Lp ℝ 2 P, y ∈ S →
      HasGaussianLaw (fun ω => y ω) P ∧ ∫ ω, y ω ∂P = 0 := by
  classical
  dsimp
  intro y hy
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  let I := {j // j ∈ c.support}
  let v : I → J := fun i => i.1
  let L : (I → ℝ) →L[ℝ] ℝ := ∑ i : I, c i.1 • ContinuousLinearMap.proj i
  have hJoint := hjoint c.support
  have hMap : HasGaussianLaw (fun ω => L (fun i => B (v i) ω)) P := hJoint.map L
  have hpoint : ∀ ω, L (fun i => B (v i) ω) = ∑ i : I, c i.1 * B i.1 ω := by
    intro ω
    simp [L, v, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have hyAe : (fun ω => y ω) =ᵐ[P] fun ω => L (fun i => B (v i) ω) := by
    have hsum := Lp.coeFn_finsetSum Finset.univ
      (fun i : I => c i.1 • (hB i.1).toLp (B i.1))
    have hscalar : ∀ i : I, ∀ᵐ ω ∂P,
        ((c i.1 • (hB i.1).toLp (B i.1)) : Lp ℝ 2 P) ω = c i.1 * B i.1 ω := by
      intro i
      filter_upwards [Lp.coeFn_smul (c i.1) ((hB i.1).toLp (B i.1)),
        (hB i.1).coeFn_toLp] with ω hsmul hrep
      calc
        ((c i.1 • (hB i.1).toLp (B i.1)) : Lp ℝ 2 P) ω =
            (c i.1 • ((hB i.1).toLp (B i.1) : Ω → ℝ)) ω := hsmul
        _ = c i.1 * ((hB i.1).toLp (B i.1)) ω := rfl
        _ = c i.1 * B i.1 ω := by rw [hrep]
    have hsumI : c.sum (fun j a => a • (hB j).toLp (B j)) =
        ∑ i : I, c i.1 • (hB i.1).toLp (B i.1) := by
      simp only [Finsupp.sum]
      exact Finset.sum_subtype c.support (fun _ => Iff.rfl)
        (fun j => c j • (hB j).toLp (B j))
    have hyLp : y = ∑ i : I, c i.1 • (hB i.1).toLp (B i.1) := by
      calc
        y = c.sum (fun j a => a • (hB j).toLp (B j)) := hc.symm
        _ = _ := hsumI
    filter_upwards [hsum, ae_all_iff.2 hscalar] with ω hsumω hscalarω
    rw [hyLp]
    rw [hsumω]
    rw [Finset.sum_apply]
    rw [hpoint]
    apply Finset.sum_congr rfl
    intro i hi
    exact hscalarω i
  have hLaw : HasGaussianLaw (fun ω => y ω) P := hMap.congr hyAe.symm
  have hzero : ∫ ω, y ω ∂P = 0 := by
      have hsumMean : ∫ ω, ∑ i : I, c i.1 * B i.1 ω ∂P = 0 := by
        rw [integral_finsetSum]
        · simp [integral_const_mul, hmean]
        · intro i hi
          exact ((hB i.1).integrable (by norm_num)).const_mul (c i.1)
      calc
        ∫ ω, y ω ∂P = ∫ ω, L (fun i => B (v i) ω) ∂P := integral_congr_ae hyAe
        _ = ∫ ω, ∑ i : I, c i.1 * B i.1 ω ∂P := by
          apply integral_congr_ae
          exact Eventually.of_forall hpoint
        _ = 0 := hsumMean
  exact ⟨hLaw, hzero⟩

theorem centeredGaussian_on_closedCoordinateSpan
    {Ω : Type v} {J : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : J → Ω → ℝ)
    (hB : ∀ j, MemLp (B j) 2 P)
    (hjoint : ∀ s : Finset J,
      HasGaussianLaw (fun ω (i : s) => B i.1 ω) P)
    (hmean : ∀ j, ∫ ω, B j ω ∂P = 0) :
    let S : Submodule ℝ (Lp ℝ 2 P) :=
      Submodule.span ℝ (Set.range fun j => (hB j).toLp (B j))
    ∀ y : Lp ℝ 2 P, y ∈ S.topologicalClosure →
      HasGaussianLaw (fun ω => y ω) P ∧ ∫ ω, y ω ∂P = 0 := by
  classical
  dsimp
  intro y hy
  let S : Submodule ℝ (Lp ℝ 2 P) :=
    Submodule.span ℝ (Set.range fun j => (hB j).toLp (B j))
  have hspan := centeredGaussian_on_coordinateSpan B hB hjoint hmean
  have hGaussian : ∀ x : Lp ℝ 2 P, x ∈ S → HasGaussianLaw (fun ω => x ω) P := by
    intro x hx
    exact (hspan x hx).1
  have hcenter : ∀ x : Lp ℝ 2 P, x ∈ S → ∫ ω, x ω ∂P = 0 := by
    intro x hx
    exact (hspan x hx).2
  have hclosedGaussian := hasGaussianLaw_of_mem_topologicalClosure_gaussianSubmodule
    S hGaussian hcenter y hy
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hy
  have hdiffTendsto : Filter.Tendsto (fun n : ℕ => u n - y) atTop (𝓝 (0 : Lp ℝ 2 P)) := by
    simpa using hlim.sub_const y
  have hnormTendsto : Filter.Tendsto (fun n : ℕ => ‖u n - y‖) atTop (𝓝 (0 : ℝ)) := by
    have htemp := (continuous_norm.tendsto (0 : Lp ℝ 2 P)).comp hdiffTendsto
    change Filter.Tendsto (fun n : ℕ => ‖u n - y‖) atTop
      (𝓝 ‖(0 : Lp ℝ 2 P)‖) at htemp
    simpa using htemp
  have hmeanBound : ∀ n, |∫ ω, y ω ∂P| ≤ ‖u n - y‖ := by
    intro n
    let hf : MemLp (fun ω => u n ω - y ω) 2 P :=
      (Lp.memLp (u n - y)).ae_eq (Lp.coeFn_sub (u n) y)
    have hclass : hf.toLp (fun ω => u n ω - y ω) = u n - y := by
      calc
        hf.toLp (fun ω => u n ω - y ω) =
            (Lp.memLp (u n - y)).toLp (fun ω => (u n - y) ω) :=
          MemLp.toLp_congr hf (Lp.memLp (u n - y)) (Lp.coeFn_sub (u n) y).symm
        _ = u n - y := Lp.toLp_coeFn (u n - y) (Lp.memLp (u n - y))
    have huInt : Integrable (fun ω => u n ω) P :=
      (Lp.memLp (u n)).integrable (by norm_num)
    have hyInt : Integrable (fun ω => y ω) P := (Lp.memLp y).integrable (by norm_num)
    have hdiffIntegral : ∫ ω, (u n ω - y ω) ∂P =
        (∫ ω, u n ω ∂P) - (∫ ω, y ω ∂P) := integral_sub huInt hyInt
    have habs : |∫ ω, (u n ω - y ω) ∂P| ≤ ‖u n - y‖ := by
      calc
        |∫ ω, (u n ω - y ω) ∂P| ≤ ∫ ω, |u n ω - y ω| ∂P :=
          MeasureTheory.abs_integral_le_integral_abs
        _ ≤ ‖hf.toLp (fun ω => u n ω - y ω)‖ := integral_abs_le_l2 hf
        _ = ‖u n - y‖ := by rw [hclass]
    rw [hdiffIntegral, hcenter (u n) (hu n), zero_sub, abs_neg] at habs
    exact habs
  have hmeanLeZero : |∫ ω, y ω ∂P| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hnormTendsto
      (Eventually.of_forall hmeanBound)
  have hmeanAbs : |∫ ω, y ω ∂P| = 0 := le_antisymm hmeanLeZero (abs_nonneg _)
  have hmeanZero : ∫ ω, y ω ∂P = 0 := abs_eq_zero.mp hmeanAbs
  exact ⟨hclosedGaussian, hmeanZero⟩

end HaarQuarter
