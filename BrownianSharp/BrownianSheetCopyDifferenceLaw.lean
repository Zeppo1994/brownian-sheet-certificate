import BrownianSharp.BrownianSheetOnCube
import BrownianSharp.ContinuousMapFiniteLaw
import BrownianSharp.BrownianOriginBallPositivity
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory

noncomputable section

namespace HaarQuarter

/-- A centered Gaussian random vector has the same law after subtracting an
independent copy as after multiplication by `sqrt 2`. -/
theorem centeredGaussian_prod_sub_eq_sqrtTwo_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E] (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = (0 : E)) :
    (μ.prod μ).map (fun z : E × E => z.1 - z.2) =
      μ.map (fun x : E => Real.sqrt 2 • x) := by
  let Q := μ.prod μ
  let X : E × E → E := fun z => z.1
  let Y : E × E → E := fun z => z.2
  have hfstLaw : HasLaw X μ Q := (measurePreserving_fst (μ := μ) (ν := μ)).hasLaw
  have hsndLaw : HasLaw Y μ Q := (measurePreserving_snd (μ := μ) (ν := μ)).hasLaw
  have hfst : HasGaussianLaw X Q := hfstLaw.hasGaussianLaw
  have hsnd : HasGaussianLaw Y Q := hsndLaw.hasGaussianLaw
  have hind : X ⟂ᵢ[Q] Y :=
    indepFun_prod₀ (X := id) (Y := id) aemeasurable_id aemeasurable_id
  have hpair : HasGaussianLaw (fun z => (X z, Y z)) Q := hind.hasGaussianLaw hfst hsnd
  have hdiff : HasGaussianLaw (fun z => X z - Y z) Q := hpair.fun_sub
  have hscale : HasGaussianLaw (fun z => Real.sqrt 2 • X z) Q := by
    exact hfst.map ((ContinuousLinearMap.lsmul ℝ (R := ℝ)) (Real.sqrt 2))
  have hscaledLaw : Q.map (fun z => Real.sqrt 2 • X z) =
      μ.map (fun x : E => Real.sqrt 2 • x) := by
    calc
      Q.map (fun z => Real.sqrt 2 • X z) =
          (Q.map X).map (fun x : E => Real.sqrt 2 • x) := by
            symm
            rw [Measure.map_map (by fun_prop : Measurable (fun x : E => Real.sqrt 2 • x))
              (by fun_prop : Measurable X)]
            rfl
      _ = μ.map (fun x : E => Real.sqrt 2 • x) := by rw [hfstLaw.map_eq]
  apply Measure.ext_of_charFunDual
  ext L
  rw [← hscaledLaw, hdiff.charFunDual_map_eq_fun L, hscale.charFunDual_map_eq_fun L]
  have hU : MemLp (fun z => L (X z)) 2 Q := (hfst.map L).memLp_two
  have hV : MemLp (fun z => L (Y z)) 2 Q := (hsnd.map L).memLp_two
  have hIndL : (fun z => L (X z)) ⟂ᵢ[Q] (fun z => L (Y z)) :=
    hind.comp (by fun_prop) (by fun_prop)
  have hCov : cov[fun z => L (X z), fun z => L (Y z); Q] = 0 :=
    hIndL.covariance_eq_zero hU hV
  have hMeanU : ∫ z, L (X z) ∂Q = 0 := by
    rw [show (fun z => L (X z)) = L ∘ X by rfl,
      hfstLaw.integral_comp (by fun_prop)]
    change ∫ x, L (id x) ∂μ = 0
    rw [ContinuousLinearMap.integral_comp_comm L IsGaussian.integrable_id]
    simpa using congrArg L hmean
  have hMeanV : ∫ z, L (Y z) ∂Q = 0 := by
    rw [show (fun z => L (Y z)) = L ∘ Y by rfl,
      hsndLaw.integral_comp (by fun_prop)]
    change ∫ x, L (id x) ∂μ = 0
    rw [ContinuousLinearMap.integral_comp_comm L IsGaussian.integrable_id]
    simpa using congrArg L hmean
  have hVarU : Var[fun z => L (X z); Q] = Var[fun x : E => L x; μ] := by
    rw [← covariance_self (by fun_prop : AEMeasurable (fun z : E × E => L (X z)) Q)]
    rw [← covariance_self (by fun_prop : AEMeasurable (fun x : E => L x) μ)]
    exact hfstLaw.covariance_comp (by fun_prop) (by fun_prop)
  have hVarV : Var[fun z => L (Y z); Q] = Var[fun x : E => L x; μ] := by
    rw [← covariance_self (by fun_prop : AEMeasurable (fun z : E × E => L (Y z)) Q)]
    rw [← covariance_self (by fun_prop : AEMeasurable (fun x : E => L x) μ)]
    exact hsndLaw.covariance_comp (by fun_prop) (by fun_prop)
  have hMeanD : ∫ z, L ((fun z => X z - Y z) z) ∂Q = 0 := by
    simp only [map_sub]
    rw [integral_sub (hU.integrable (by norm_num)) (hV.integrable (by norm_num)),
      hMeanU, hMeanV, sub_self]
  have hMeanS : ∫ z, L ((fun z => Real.sqrt 2 • X z) z) ∂Q = 0 := by
    simp only [map_smul]
    rw [integral_smul, hMeanU, smul_zero]
  have hVarD : Var[fun z => L (X z - Y z); Q] = 2 * Var[fun z => L (X z); Q] := by
    calc
      Var[fun z => L (X z - Y z); Q] =
          Var[fun z => L (X z) - L (Y z); Q] := by congr 1; funext z; simp
      _ = Var[fun z => L (X z); Q] -
          2 * cov[fun z => L (X z), fun z => L (Y z); Q] +
          Var[fun z => L (Y z); Q] := variance_sub hU hV
      _ = 2 * Var[fun z => L (X z); Q] := by rw [hCov, hVarU, hVarV]; ring
  have hVarS : Var[fun z => L (Real.sqrt 2 • X z); Q] =
      2 * Var[fun z => L (X z); Q] := by
    calc
      Var[fun z => L (Real.sqrt 2 • X z); Q] =
          Var[(Real.sqrt 2) • (fun z => L (X z)); Q] := by congr 1; funext z; simp
      _ = (Real.sqrt 2)^2 * Var[fun z => L (X z); Q] := variance_smul _ _ _
      _ = 2 * Var[fun z => L (X z); Q] := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hMeanD, hVarD, hMeanS, hVarS]

/-- Source-level version of the copy-difference identity, suitable for a
random element of a continuous-map space. -/
theorem centeredGaussian_copyDifference_law
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E)
    (hX : Measurable X) (hG : HasGaussianLaw X P)
    (hmean : ∫ ω, X ω ∂P = (0 : E)) :
    (P.prod P).map (fun z => X z.1 - X z.2) =
      (P.prod P).map (fun z => Real.sqrt 2 • X z.1) := by
  let μ := P.map X
  have hμGaussian : IsGaussian μ := hG.isGaussian_map
  letI : IsGaussian μ := hμGaussian
  have hLaw : HasLaw X μ P := ⟨hX.aemeasurable, rfl⟩
  have hμmean : ∫ x, x ∂μ = (0 : E) := by
    rw [← hLaw.integral_eq]
    exact hmean
  have hpair : (P.prod P).map (fun z => (X z.1, X z.2)) = μ.prod μ := by
    change (P.prod P).map (Prod.map X X) = μ.prod μ
    exact (Measure.map_prod_map P P hX hX).symm
  have hscale : (P.prod P).map (fun z => Real.sqrt 2 • X z.1) =
      μ.map (fun x : E => Real.sqrt 2 • x) := by
    calc
      (P.prod P).map (fun z => Real.sqrt 2 • X z.1) =
          ((P.prod P).map Prod.fst).map (fun ω => Real.sqrt 2 • X ω) := by
            symm
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = P.map (fun ω => Real.sqrt 2 • X ω) := by
        rw [measurePreserving_fst.map_eq]
      _ = μ.map (fun x : E => Real.sqrt 2 • x) := by
        simpa [μ, Function.comp_def] using
          (Measure.map_map (by fun_prop : Measurable (fun x : E => Real.sqrt 2 • x)) hX).symm
  calc
    (P.prod P).map (fun z => X z.1 - X z.2) =
        ((P.prod P).map (fun z => (X z.1, X z.2))).map
          (fun z : E × E => z.1 - z.2) := by
            symm
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = (μ.prod μ).map (fun z : E × E => z.1 - z.2) := by rw [hpair]
    _ = μ.map (fun x : E => Real.sqrt 2 • x) :=
      centeredGaussian_prod_sub_eq_sqrtTwo_map μ hμmean
    _ = (P.prod P).map (fun z => Real.sqrt 2 • X z.1) := hscale.symm

/-- Every finite vector of a centered continuous-path Brownian sheet obeys the
copy-difference law needed to establish origin-ball positivity. -/
theorem BrownianSheetOnCube.copyDifference_finiteEvaluationLaw
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : BrownianSheetOnCube d Ω P)
    (I : Finset (BrownianCubeAnchor d)) :
    (P.prod P).map (fun z => I.restrict (fun x => B.eval x z.1) -
      I.restrict (fun x => B.eval x z.2)) =
    (P.prod P).map (fun z => Real.sqrt 2 • I.restrict (fun x => B.eval x z.1)) := by
  let X : Ω → I → ℝ := fun ω x => B.eval x.1 ω
  have hX : HasGaussianLaw X P := by
    change HasGaussianLaw (fun ω => I.restrict (fun x => B.eval x ω)) P
    exact B.gaussian.hasGaussianLaw I
  haveI : IsProbabilityMeasure P := B.gaussian.isProbabilityMeasure
  have hXm : Measurable X := by
    apply measurable_pi_lambda
    intro x
    exact B.measurable_eval x.1
  have hXint : Integrable X P := hX.memLp_two.integrable (by norm_num)
  have hmean : ∫ ω, X ω ∂P = 0 := by
    ext x
    let πx : (I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj x
    have hcomp := ContinuousLinearMap.integral_comp_comm
      πx hXint
    calc
      (∫ ω, X ω ∂P) x = πx (∫ ω, X ω ∂P) := by simp [πx]
      _ = ∫ ω, πx (X ω) ∂P := hcomp.symm
      _ = 0 := by
        simpa [X, πx, ContinuousLinearMap.proj_apply, BrownianSheetOnCube.eval] using
          B.mean_zero x.1
  exact centeredGaussian_copyDifference_law P X hXm hX hmean

/-- The law of a Brownian sheet's copy difference on continuous paths is the
law of `sqrt 2` times one path. Finite-dimensional Gaussian laws determine the
continuous-map law, so no ambient Gaussian process premise is used. -/
theorem BrownianSheetOnCube.copyDifference_pathLaw
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : BrownianSheetOnCube d Ω P) :
    (P.prod P).map (fun z : Ω × Ω => B.path z.1 - B.path z.2) =
      P.map (fun ω => Real.sqrt 2 • B.path ω) := by
  let F : Ω × Ω → C(BrownianCubeAnchor d, ℝ) := fun z => B.path z.1 - B.path z.2
  let G : Ω × Ω → C(BrownianCubeAnchor d, ℝ) := fun z => Real.sqrt 2 • B.path z.1
  haveI : IsProbabilityMeasure P := B.gaussian.isProbabilityMeasure
  have hF : Measurable F := by
    dsimp [F]
    exact B.measurable_path.comp measurable_fst |>.sub (B.measurable_path.comp measurable_snd)
  have hG : Measurable G := by
    dsimp [G]
    exact (B.measurable_path.comp measurable_fst).const_smul (Real.sqrt 2)
  have hfinite : ∀ I : Finset (BrownianCubeAnchor d),
      (P.prod P).map (fun z => I.restrict (fun x => F z x)) =
        (P.prod P).map (fun z => I.restrict (fun x => G z x)) := by
    intro I
    have hleft : (fun z => I.restrict (fun x => F z x)) =
        (fun z => I.restrict (fun x => B.eval x z.1) -
          I.restrict (fun x => B.eval x z.2)) := by
      funext z
      ext x
      rfl
    have hright : (fun z => I.restrict (fun x => G z x)) =
        (fun z => Real.sqrt 2 • I.restrict (fun x => B.eval x z.1)) := by
      funext z
      ext x
      rfl
    rw [hleft, hright]
    exact B.copyDifference_finiteEvaluationLaw I
  have hpath := continuousMap_map_eq_of_finite_evaluations
    (P.prod P) F G hF hG hfinite
  have hscale : (P.prod P).map G = P.map (fun ω => Real.sqrt 2 • B.path ω) := by
    have hpathScale : Measurable (fun ω => Real.sqrt 2 • B.path ω) :=
      B.measurable_path.const_smul (Real.sqrt 2)
    calc
      (P.prod P).map G =
          ((P.prod P).map Prod.fst).map (fun ω => Real.sqrt 2 • B.path ω) := by
            symm
            rw [Measure.map_map hpathScale (by fun_prop)]
            rfl
      _ = P.map (fun ω => Real.sqrt 2 • B.path ω) := by
        rw [measurePreserving_fst.map_eq]
  simpa [F] using hpath.trans hscale

/-- Every positive uniform-norm ball about zero has positive probability for
the continuous centered Gaussian sheet on the anchored cube. -/
theorem BrownianSheetOnCube.smallBall_probability_pos
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : BrownianSheetOnCube d Ω P)
    {ε : ℝ} (hε : 0 < ε) :
    0 < P.real {ω | ‖B.path ω‖ ≤ ε} := by
  haveI : IsProbabilityMeasure P := B.gaussian.isProbabilityMeasure
  exact (probability_norm_le_pos_of_copyDifferenceLaw P B.path B.measurable_path
    (Real.sqrt 2) (Real.sqrt_pos.2 (by norm_num)) B.copyDifference_pathLaw) ε hε

end HaarQuarter
