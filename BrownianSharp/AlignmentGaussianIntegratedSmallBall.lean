import BrownianSharp.AlignmentGaussianShift
import BrownianSharp.AlignmentGaussianGridLimit
import BrownianSharp.AlignmentGaussianEntropySmallBall
import BrownianSharp.AlignmentFractionalAnisotropicEntropy
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentIntegratedNorm
import Mathlib.MeasureTheory.Measure.Map

noncomputable section
open MeasureTheory
open scoped ENNReal
open HaarQuarter

namespace BrownianSharp.AlignmentGaussianIntegratedSmallBall

open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentGaussianShift
open BrownianSharp.AlignmentFractionalTensorOperator

/-- Law on the actual continuous-function path space of an iterated integrated
Brownian sheet. -/
def integratedSheetLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    Measure C(BrownianCubeAnchor d, ℝ) :=
  P.map (integrateBrownianSheetPath B m)

/-- Cameron--Martin translation lower bound for every ball center in the
actual anisotropic RL image. It is derived from finite-grid shifts for the
constructed integrated Gaussian path, followed by the compact-domain grid
limit; the image membership is unfolded to an actual unit-cube source. -/
theorem integratedSheetLaw_ball_shift_lower {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (x : C(BrownianCubeAnchor d, ℝ))
    (hx : x ∈ BrownianSharp.Latest.fractionalIntegrationBall
      (fun i => (m i : ℝ) + 1)) :
    ENNReal.ofReal (Real.exp (-(R ^ 2) / 2)) *
        integratedSheetLaw B m (Metric.closedBall 0 ε) ≤
      integratedSheetLaw B m (Metric.closedBall (R • x) ε) := by
  classical
  let a : Fin d → ℝ := fun i => (m i : ℝ) + 1
  have ha : ∀ i, 1 / 2 < a i := by
    intro i
    dsimp [a]
    exact_mod_cast (show 1 / 2 < (m i : ℝ) + 1 by
      have : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
      linarith)
  rw [fractionalIntegrationBall_eq_operator_image a ha] at hx
  rcases hx with ⟨g, hg, hxEq⟩
  have hg' : ‖g‖ ≤ 1 := by
    change ‖g‖ ≤ 1 at hg
    exact hg
  have hxEq' : fractionalTensorRL a ha g = x := by
    simpa using hxEq
  let F : Ω → C(BrownianCubeAnchor d, ℝ) := integrateBrownianSheetPath B m
  have hF : Measurable F := measurable_integrateBrownianSheetPath B m
  have hcoord : ∀ t, Measurable (fun ω => F ω t) := by
    intro t
    have hevC : Continuous (fun q : C(BrownianCubeAnchor d, ℝ) => q t) :=
      continuous_eval_const t
    have hev : Measurable (fun q : C(BrownianCubeAnchor d, ℝ) => q t) := hevC.measurable
    exact hev.comp (measurable_integrateBrownianSheetPath B m)
  let f : C(BrownianCubeAnchor d, ℝ) := R • fractionalTensorRL a ha g
  have hfinite : ∀ S : Finset (BrownianCubeAnchor d),
      ENNReal.ofReal (Real.exp (-(R ^ 2) / 2)) *
        P {ω | ∀ t ∈ S, |F ω t| ≤ ε} ≤
      P {ω | ∀ t ∈ S, |F ω t - f t| ≤ ε} := by
    intro S
    have h := integratedSheet_finiteGrid_shift_lower_scaled B m g hg' S ε R hR.le
    have heq : ∀ t,
        R * BrownianSharp.Latest.fractionalIntegrationValue a g t = f t := by
      intro t
      dsimp [f]
      rw [fractionalTensorRL_apply a ha]
    simpa [F, a, heq] using h
  letI : Nonempty (BrownianCubeAnchor d) :=
    ⟨⟨0, fun _ => ⟨by norm_num, by norm_num⟩⟩⟩
  let points : ℕ → BrownianCubeAnchor d :=
    TopologicalSpace.denseSeq (BrownianCubeAnchor d)
  have hdense : DenseRange points := TopologicalSpace.denseRange_denseSeq _
  have hgrid := BrownianSharp.AlignmentGaussianGridLimit.finite_grid_mass_lower_to_uniform_mass_lower
    P points hdense F hcoord f ε hε.le
      (ENNReal.ofReal (Real.exp (-(R ^ 2) / 2))) hfinite
  have hball0 : MeasurableSet (Metric.closedBall (0 : C(BrownianCubeAnchor d, ℝ)) ε) :=
    measurableSet_closedBall
  have hballx : MeasurableSet (Metric.closedBall (R • x) ε) :=
    measurableSet_closedBall
  have hμ0 : integratedSheetLaw B m (Metric.closedBall 0 ε) =
      P {ω | ‖F ω‖ ≤ ε} := by
    rw [integratedSheetLaw, Measure.map_apply hF hball0]
    apply congrArg (fun A : Set Ω => P A)
    ext ω
    simp [F, Metric.mem_closedBall, dist_eq_norm]
  have hμx : integratedSheetLaw B m (Metric.closedBall (R • x) ε) =
      P {ω | ‖F ω - R • x‖ ≤ ε} := by
    rw [integratedSheetLaw, Measure.map_apply hF hballx]
    apply congrArg (fun A : Set Ω => P A)
    ext ω
    simp [F, Metric.mem_closedBall, dist_eq_norm]
  rw [hμ0, hμx]
  have hfEq : f = R • x := by
    dsimp [f]
    rw [hxEq']
  simpa [hfEq] using hgrid

/-- Actual anisotropic RL entropy lower rate in the order/multiplicity
parameters of the manuscript's integer integrated sheet. -/
theorem integratedSheet_entropy_lower {d : ℕ} (hd : 2 ≤ d)
    (m : Fin d → ℕ) (m₀ ν : ℕ) (hν : 2 ≤ ν)
    (hm : BrownianSharp.Latest.minimumMultiplicity
      (fun i => (m i : ℝ)) (m₀ : ℝ) ν) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * BrownianSharp.logarithmicIndexRate
        ((m₀ : ℝ) + 1)
        (((m₀ : ℝ) + 1) * ((ν - 1 : ℕ) : ℝ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (BrownianSharp.Latest.fractionalIntegrationBall
            (fun i => (m i : ℝ) + 1)) := by
  let a : Fin d → ℝ := fun i => (m i : ℝ) + 1
  let r : ℝ := (m₀ : ℝ) + 1
  have ha : ∀ i, 1 / 2 < a i := by
    intro i
    dsimp [a]
    have : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
    linarith
  have hr : 1 / 2 < r := by
    dsimp [r]
    have : 0 ≤ (m₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hm0 : (∀ i, (m₀ : ℝ) ≤ (m i : ℝ)) ∧
      (Finset.univ.filter (fun i : Fin d => (m i : ℝ) = (m₀ : ℝ))).card = ν := by
    change (∀ i, (m₀ : ℝ) ≤ (m i : ℝ)) ∧
      (Finset.univ.filter (fun i : Fin d => (m i : ℝ) = (m₀ : ℝ))).card = ν at hm
    exact hm
  have hm' : BrownianSharp.Latest.minimumMultiplicity a r ν := by
    change (∀ i, r ≤ a i) ∧
      (Finset.univ.filter (fun i : Fin d => a i = r)).card = ν
    constructor
    · intro i
      dsimp [a, r]
      linarith [hm0.1 i]
    · have hfilter : Finset.univ.filter (fun i : Fin d => a i = r) =
          Finset.univ.filter (fun i : Fin d => (m i : ℝ) = (m₀ : ℝ)) := by
        apply Finset.filter_congr
        intro i hi
        dsimp [a, r]
        constructor
        · intro h
          exact add_right_cancel h
        · intro h
          exact congrArg (fun z : ℝ => z + 1) h
      rw [hfilter]
      exact hm0.2
  obtain ⟨c, hc, k₀, hk₀, hEntropy⟩ :=
    BrownianSharp.AlignmentFractionalAnisotropicEntropy.fractional_entropy_lower_general
      hd a ha r hr hν hm'
  refine ⟨c, hc, k₀, hk₀, ?_⟩
  intro k hk
  simpa [a, r, BrownianSharp.logarithmicIndexRate, mul_assoc] using hEntropy k hk

/-- Uniform one-sided integrated-sheet small-ball lower-log estimate. The
entropy constants are selected from the actual tensor RL ball before the
probability space and sheet are quantified. -/
theorem integratedSheet_oneSided_lowerLog {d : ℕ} (hd : 2 ≤ d)
    (m : Fin d → ℕ) (m₀ ν : ℕ) (hν : 2 ≤ ν)
    (hm : BrownianSharp.Latest.minimumMultiplicity
      (fun i => (m i : ℝ)) (m₀ : ℝ) ν) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        c * BrownianSharp.Latest.smallBallRate
          (2 / (2 * (m₀ : ℝ) + 1))
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * (m₀ : ℝ) + 1)) ε ≤
          -Real.log (P.real {ω | ‖integrateSheetPath m (B.path ω)‖ ≤ ε}) := by
  let r : ℝ := (m₀ : ℝ) + 1
  let b : ℝ := r * ((ν - 1 : ℕ) : ℝ) + 1 / 2
  have hr : 1 / 2 < r := by
    dsimp [r]
    have : 0 ≤ (m₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hb : 0 ≤ b := by
    dsimp [b, r]
    positivity
  have hEntropy := integratedSheet_entropy_lower hd m m₀ ν hν hm
  obtain ⟨c, ε₀, hc, hε₀, hε₀exp, hUniform⟩ :=
    BrownianSharp.AlignmentGaussianEntropySmallBall.uniform_smallBall_probability_upper_of_entropy_lower
      (BrownianSharp.Latest.fractionalIntegrationBall (fun i => (m i : ℝ) + 1))
      r b hr hb (by
        rcases hEntropy with ⟨c', hc', k₀, hk₀, hE⟩
        exact ⟨c', hc', k₀, fun k hk => by
          have hh := hE k hk
          simpa [BrownianSharp.logarithmicIndexRate, r, b, mul_assoc] using hh⟩)
  refine ⟨c, ε₀, hc, hε₀, hε₀exp, ?_⟩
  intro Ω _ P _ B ε hε hsmall
  let μ := integratedSheetLaw B m
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (P.map (integrateBrownianSheetPath B m))
    refine ⟨?_⟩
    rw [Measure.map_apply (measurable_integrateBrownianSheetPath B m) MeasurableSet.univ]
    simp
  have hshift : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ x ∈ BrownianSharp.Latest.fractionalIntegrationBall
        (fun i => (m i : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(R ^ 2) / 2)) * μ (Metric.closedBall 0 η) ≤
          μ (Metric.closedBall (R • x) η) := by
    intro R hR η hη x hx
    exact integratedSheetLaw_ball_shift_lower B m R η hR hη x hx
  have hprob := hUniform μ inferInstance hshift ε hε (by simpa [μ] using hsmall)
  have hball : MeasurableSet (Metric.closedBall
      (0 : C(BrownianCubeAnchor d, ℝ)) ε) := measurableSet_closedBall
  have hmass : μ.real (Metric.closedBall 0 ε) =
      P.real {ω | ‖integrateSheetPath m (B.path ω)‖ ≤ ε} := by
    change (P.map (integrateBrownianSheetPath B m)).real
      (Metric.closedBall 0 ε) = _
    rw [Measure.real_def,
      Measure.map_apply (measurable_integrateBrownianSheetPath B m) hball,
      Measure.real_def]
    congr 1
  have hpositive : 0 < P.real
      {ω | ‖integrateSheetPath m (B.path ω)‖ ≤ ε} :=
    BrownianSharp.AlignmentIntegratedNorm.integrated_smallBall_probability_pos P B m hε
  have hpositiveμ : 0 < μ.real (Metric.closedBall 0 ε) := by
    rw [hmass]
    exact hpositive
  have hlog := Real.log_le_log hpositiveμ hprob
  rw [Real.log_exp] at hlog
  have hden : (1 + (m₀ : ℝ) * 2) ≠ 0 := by positivity
  have hden' : (2 * (m₀ : ℝ) + 1) ≠ 0 := by positivity
  have hden'' : ((m₀ : ℝ) + 1 - 1 / 2) ≠ 0 := by positivity
  have hdenEq : 2 * (m₀ : ℝ) + 1 = 1 + (m₀ : ℝ) * 2 := by ring
  have hrpow : (r - 1 / 2)⁻¹ = 2 / (2 * (m₀ : ℝ) + 1) := by
    dsimp [r]
    rw [show (m₀ : ℝ) + 1 - 1 / 2 = (1 + (m₀ : ℝ) * 2) / 2 by ring]
    rw [inv_div, hdenEq]
  have habeta : b / (r - 1 / 2) =
      ((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * (m₀ : ℝ) + 1) := by
    dsimp [b, r]
    have hcast : ((ν - 1 : ℕ) : ℝ) = (ν : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ ν)]
      norm_num
    rw [hcast]
    rw [show (m₀ : ℝ) + 1 - 1 / 2 = (1 + (m₀ : ℝ) * 2) / 2 by ring]
    field_simp [hden, hden', hden'']
    <;> ring
  have hrate : BrownianSharp.Latest.smallBallRate (r - 1 / 2)⁻¹
      (b / (r - 1 / 2)) ε = BrownianSharp.Latest.smallBallRate
        (2 / (2 * (m₀ : ℝ) + 1))
        (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * (m₀ : ℝ) + 1)) ε := by
    rw [hrpow, habeta]
  rw [hmass, hrate] at hlog
  linarith

end BrownianSharp.AlignmentGaussianIntegratedSmallBall
