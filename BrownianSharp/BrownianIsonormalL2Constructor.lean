import BrownianSharp.BrownianGaussianL2Closure
import BrownianSharp.BrownianHaarCovariance
import Mathlib.Probability.Moments.Covariance

open MeasureTheory ProbabilityTheory InnerProductSpace Filter Topology
open scoped RealInnerProductSpace ProbabilityTheory

namespace HaarQuarter

/-- Choose a genuinely measurable representative of a real `L²` element. -/
noncomputable def l2MeasurableRepresentative {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (f : Lp ℝ 2 P) : Ω → ℝ :=
  (Lp.aestronglyMeasurable f).mk

/-- An isometric Gaussian embedding of a Hilbert space into scalar `L²` defines an
isonormal Gaussian family on that Hilbert space. The finite-family joint law is obtained by
checking every continuous linear functional, reducing it to one scalar image of the embedding. -/
noncomputable def isonormalGaussianFamily_of_l2_isometry
    {H Ω ι : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (T : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hGaussian : ∀ f : H, HasGaussianLaw (fun ω => T f ω) P)
    (hmean : ∀ f : H, ∫ ω, T f ω ∂P = 0) :
    IsonormalGaussianFamily H Ω ι P := by
  classical
  let eval : H → Ω → ℝ := fun f => l2MeasurableRepresentative (T f)
  have hrep (f : H) : eval f =ᵐ[P] fun ω => T f ω := by
    exact (Lp.aestronglyMeasurable (T f)).ae_eq_mk.symm
  have hmem (f : H) : MemLp (eval f) 2 P :=
    (Lp.memLp (T f)).ae_eq (hrep f).symm
  have hLaw (f : H) : HasGaussianLaw (eval f) P :=
    (hGaussian f).congr (hrep f).symm
  have hMean (f : H) : ∫ ω, eval f ω ∂P = 0 := by
    rw [integral_congr_ae (hrep f)]
    exact hmean f
  refine ⟨eval, ?_, ?_, hMean, ?_⟩
  · intro v
    apply hasGaussianLaw_of_dual_centered_l2_limits
    · exact (measurable_pi_iff.mpr fun i =>
        (Lp.aestronglyMeasurable (T (v i))).measurable_mk).aemeasurable
    · intro L
      let c : ι → ℝ := fun i => L (Pi.single i 1)
      let f : H := ∑ i, c i • v i
      let proj : Ω → ℝ := fun ω => L (fun i => eval (v i) ω)
      have hLexpand (x : ι → ℝ) : L x = ∑ i, x i * c i := by
        have hx : x = ∑ i, x i • Pi.single i 1 := by
          funext i
          simp [Finset.sum_apply, Pi.single_apply]
        rw [hx, map_sum]
        simp [c, smul_eq_mul, Pi.single_apply]
      have hproj : proj =ᵐ[P] eval f := by
        have hcoords : ∀ᵐ ω ∂P, ∀ i, eval (v i) ω = T (v i) ω := by
          filter_upwards [ae_all_iff.2 fun i => hrep (v i)] with ω hω i
          exact hω i
        have hsum : eval f =ᵐ[P] fun ω => ∑ i, c i * T (v i) ω := by
          have h := hrep f
          have hT : T f = ∑ i, c i • T (v i) := by
            simp [f, map_sum]
          have hlin : (fun ω => T f ω) =ᵐ[P] fun ω => ∑ i, c i * T (v i) ω := by
            rw [hT]
            have hsmul : ∀ᵐ ω ∂P, ∀ i, (c i • T (v i)) ω = c i * T (v i) ω := by
              filter_upwards [ae_all_iff.2 fun i => Lp.coeFn_smul (c i) (T (v i))]
                with ω hω i
              exact hω i
            filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => c i • T (v i)),
              hsmul] with ω hsum hω
            rw [hsum]
            simp only [Finset.sum_apply]
            apply Finset.sum_congr rfl
            intro i hi
            exact hω i
          exact h.trans hlin
        filter_upwards [hcoords, hsum] with ω hω hωsum
        change L (fun i => eval (v i) ω) = eval f ω
        rw [hLexpand]
        change (∑ i, eval (v i) ω * c i) = eval f ω
        rw [hωsum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hω i]
        ring
      have hProjMem : MemLp proj 2 P := (hmem f).ae_eq hproj.symm
      have hEq : ((hmem f).toLp (eval f)) = (hProjMem.toLp proj) :=
        MemLp.toLp_congr (hmem f) hProjMem hproj.symm
      refine ⟨fun _ => eval f, (fun _ => hmem f), hProjMem, ?_,
        (fun _ => hLaw f), (fun _ => hMean f)⟩
      have hconst : Filter.Tendsto (fun _ : ℕ => (hmem f).toLp (eval f)) atTop
          (𝓝 ((hmem f).toLp (eval f))) := tendsto_const_nhds
      simpa only [hEq] using hconst
  · intro f
    exact (Lp.aestronglyMeasurable (T f)).measurable_mk
  · intro f g
    have hcov := ProbabilityTheory.covariance_eq_sub (hmem f) (hmem g)
    rw [hMean f, hMean g, mul_zero, sub_zero] at hcov
    have hinner : inner ℝ (T f) (T g) = ∫ ω, eval f ω * eval g ω ∂P := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hrep f, hrep g] with ω hf hg
      rw [hf, hg]
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring
    rw [hcov]
    exact hinner.symm.trans (T.inner_map_map f g)

end HaarQuarter
