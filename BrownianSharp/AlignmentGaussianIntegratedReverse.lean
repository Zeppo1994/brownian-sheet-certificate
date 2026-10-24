import BrownianSharp.AlignmentGaussianIntegratedGridLower
import BrownianSharp.AlignmentGaussianGradedReverseClosure
import BrownianSharp.AlignmentEndpointCubeGridLimit
import BrownianSharp.AlignmentGaussianIntegratedSmallBall
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.AlignmentLatestStatements
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentGaussianIntegratedReverse

open BrownianSharp.AlignmentGaussianIntegratedGridLower
open BrownianSharp.AlignmentGaussianGradedReverseClosure
open BrownianSharp.AlignmentEndpointCubeGridLimit
open BrownianSharp.AlignmentGaussianIntegratedSmallBall
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentExponentialGradedReverseInversion
open BrownianSharp.AlignmentGaussianChaining

private theorem minimumMultiplicity_succ_shift {d ν : ℕ}
    (m : Fin d → ℕ) (m₀ : ℕ)
    (hm : BrownianSharp.Latest.minimumMultiplicity
      (fun i => (m i : ℝ)) (m₀ : ℝ) ν) :
    BrownianSharp.Latest.minimumMultiplicity
      (fun i => (m i : ℝ) + 1) ((m₀ : ℝ) + 1) ν := by
  change (∀ i, (m₀ : ℝ) ≤ (m i : ℝ)) ∧
    (Finset.univ.filter (fun i : Fin d => (m i : ℝ) = (m₀ : ℝ))).card = ν at hm
  change (∀ i, (m₀ : ℝ) + 1 ≤ (m i : ℝ) + 1) ∧
    (Finset.univ.filter (fun i : Fin d => (m i : ℝ) + 1 = (m₀ : ℝ) + 1)).card = ν
  constructor
  · intro i
    linarith [hm.1 i]
  · have hfilter :
        Finset.univ.filter (fun i : Fin d => (m i : ℝ) + 1 = (m₀ : ℝ) + 1) =
        Finset.univ.filter (fun i : Fin d => (m i : ℝ) = (m₀ : ℝ)) := by
      apply Finset.filter_congr
      intro i hi
      constructor
      · intro h
        exact add_right_cancel h
      · intro h
        exact congrArg (fun z : ℝ => z + 1) h
    rw [hfilter]
    exact hm.2

/-- The finite-grid lower bound passes to the actual supremum norm by
continuity of the integrated path and the nested dyadic-grid limit. -/
theorem integratedSheet_dyadic_reverse
    {d : ℕ} (hd : 2 ≤ d) (m : Fin d → ℕ) (m₀ ν : ℕ)
    (hν : 2 ≤ ν)
    (hm : BrownianSharp.Latest.minimumMultiplicity
      (fun i => (m i : ℝ)) (m₀ : ℝ) ν) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : BrownianSheetOnCube d Ω P)
        (N : ℕ),
        Real.exp (-B * ((2 : ℝ)^N * (((N+1:ℕ):ℝ)^(ν-1)))) ≤
          P.real {ω | ‖integrateSheetPath m (X.path ω)‖ ≤
            radiusProfile (2*(m₀:ℝ)+1) ν A N} := by
  classical
  have hνd : ν ≤ d := by
    have hmult := hm.2
    change (Finset.univ.filter (fun i : Fin d => (m i : ℝ) = (m₀ : ℝ))).card = ν at hmult
    have hle : (Finset.univ.filter (fun i : Fin d => (m i : ℝ) = (m₀ : ℝ))).card ≤ d := by
      calc
        _ ≤ Fintype.card (Fin d) := Finset.card_le_card (Finset.filter_subset _ _)
        _ = d := Fintype.card_fin d
    omega
  obtain ⟨e, hde⟩ : ∃ e : ℕ, ν + e = d := ⟨d - ν, by omega⟩
  cases hde
  have hms := minimumMultiplicity_succ_shift m m₀ hm
  obtain ⟨A₀,D,hA₀,hD,hgrid⟩ := integerIntegrated_grid_lower_bound
    hν m₀ m hms
  let β : ℝ := 2*(m₀:ℝ)+1
  let A : ℝ := 2*A₀
  let B : ℝ := D + Real.log 4
  have hβ : 0 < β := by dsimp [β]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by
    dsimp [B]
    have : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
    linarith
  refine ⟨A,B,hA,hB,?_⟩
  intro Ω hΩ P hP X N
  let rad : ℝ := radiusProfile β ν A N
  let cost : ℝ := (2:ℝ)^N * (((N+1:ℕ):ℝ)^(ν-1))
  have hcost : 1 ≤ cost := by
    dsimp [cost]
    have hp : (1:ℝ) ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hn : (1:ℝ) ≤ (((N+1:ℕ):ℝ)^(ν-1)) := by
      apply one_le_pow₀
      exact_mod_cast (show 1 ≤ N+1 by omega)
    nlinarith [mul_le_mul_of_nonneg_left hn (show 0≤(2:ℝ)^N by positivity)]
  have hradpos : 0 < rad := by
    dsimp [rad, radiusProfile]
    positivity
  have hgrid' : ∀ M : ℕ,
      ENNReal.ofReal (Real.exp (-D*cost))*((1/2:ENNReal)*(1/2:ENNReal)) ≤
        P {ω | cubeGridMaximum M
          (integrateSheetPath m (X.path ω)) ≤ rad} := by
    intro M
    have hh := hgrid Ω P (CubeDyadicGrid (ν+e) M) X cubeDyadicAnchor N
    have hsqrt : Real.sqrt (((N+1:ℕ):ℝ)^ν) =
        (((N+1:ℕ):ℝ)^((ν:ℝ)/2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((N+1:ℕ):ℝ))]
      congr 1
      ring
    have hradEq : 2*A₀*Real.rpow 2 (-(2*(m₀:ℝ)+1)*(N:ℝ)/2)*
        Real.sqrt (((N+1:ℕ):ℝ)^ν) = rad := by
      rw [hsqrt]
      dsimp [rad, radiusProfile, A, β]
    have hevent :
        {ω | ∀ j : CubeDyadicGrid (ν+e) M,
          |integrateSheetPath m (X.path ω) (cubeDyadicAnchor j)| ≤
            2*A₀*Real.rpow 2 (-(2*(m₀:ℝ)+1)*(N:ℝ)/2)*
              Real.sqrt (((N+1:ℕ):ℝ)^ν)} =
        {ω | cubeGridMaximum M (integrateSheetPath m (X.path ω)) ≤ rad} := by
      rw [hradEq]
      ext ω
      constructor
      · intro h
        apply (pi_norm_le_iff_of_nonneg hradpos.le).2
        intro j
        simpa only [Real.norm_eq_abs] using h j
      · intro h j
        have hj := (pi_norm_le_iff_of_nonneg hradpos.le).1 h j
        simpa only [Real.norm_eq_abs] using hj
    rw [hevent] at hh
    simpa [cost, mul_assoc] using hh
  let F : Ω → C(BrownianCubeAnchor (ν+e),ℝ) :=
    fun ω => integrateSheetPath m (X.path ω)
  have hF : Measurable F := by
    dsimp [F]
    exact (integrateSheetPath_continuous m).measurable.comp X.measurable_path
  have huniform :
      ENNReal.ofReal (Real.exp (-D*cost))*((1/2:ENNReal)*(1/2:ENNReal)) ≤
        P {ω | ‖F ω‖ ≤ rad} :=
    cube_grid_mass_lower_to_uniform_mass_lower P F hF rad hradpos.le _ hgrid'
  have hreal := ENNReal.toReal_mono (measure_ne_top P _) huniform
  have hmass : Real.exp (-D*cost)/4 ≤
      P.real {ω | ‖integrateSheetPath m (X.path ω)‖ ≤ rad} := by
    have hmass' : (ENNReal.ofReal (Real.exp (-D*cost)) * (1/2:ENNReal) * (1/2:ENNReal)).toReal ≤
        P.real {ω | ‖integrateSheetPath m (X.path ω)‖ ≤ rad} := by
      simpa [F, Measure.real_def, mul_assoc] using hreal
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hmass'
    norm_num at hmass'
    convert hmass' using 1 <;> ring_nf
  have hexp : Real.exp (-B*cost) ≤ Real.exp (-D*cost)/4 := by
    have hlog4 : 0 ≤ Real.log (4:ℝ) := le_of_lt (Real.log_pos (by norm_num))
    have harg : -Real.log (4:ℝ)*cost ≤ -Real.log (4:ℝ) := by nlinarith
    have heq4 : Real.exp (-Real.log (4:ℝ)) = (1:ℝ)/4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
      norm_num
    have hfactor : Real.exp (-Real.log (4:ℝ)*cost) ≤ (1:ℝ)/4 := by
      calc
        _ ≤ Real.exp (-Real.log (4:ℝ)) := Real.exp_le_exp.mpr harg
        _ = _ := heq4
    have heq : -B*cost = -D*cost + (-Real.log (4:ℝ)*cost) := by
      dsimp [B]
      ring
    rw [heq, Real.exp_add]
    calc
      Real.exp (-D*cost) * Real.exp (-Real.log (4:ℝ)*cost) ≤
          Real.exp (-D*cost) * (1/4:ℝ) :=
        mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg _)
      _ = Real.exp (-D*cost)/4 := by ring
  simpa [cost, rad, radiusProfile, β] using hexp.trans hmass

/-- The dyadic probability estimate gives the actual integrated-sheet upper
small-ball logarithm, with constants fixed before the realization. -/
theorem integratedSheet_oneSided_upperLog {d : ℕ} (hd : 2 ≤ d)
    (m : Fin d → ℕ) (m₀ ν : ℕ) (hν : 2 ≤ ν)
    (hm : BrownianSharp.Latest.minimumMultiplicity
      (fun i => (m i : ℝ)) (m₀ : ℝ) ν) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P)
        (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        -Real.log (P.real {ω | ‖integrateSheetPath m (B.path ω)‖ ≤ ε}) ≤
          C * BrownianSharp.Latest.smallBallRate
            (2/(2*(m₀:ℝ)+1))
            (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*(m₀:ℝ)+1)) ε := by
  obtain ⟨A,B,hA,hB,hdyadic⟩ := integratedSheet_dyadic_reverse hd m m₀ ν hν hm
  let β : ℝ := 2*(m₀:ℝ)+1
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨C,ε₀,hC,hε₀,hε₀small,hprofiles⟩ :=
    uniform_upperLog_of_dyadic_probability_lower ν 0 hν A B β hA hB hβ
  refine ⟨C,ε₀,hC,hε₀,hε₀small,?_⟩
  intro Ω _ P _ X ε hε hsmall
  let p : ℝ → ℝ := fun η => P.real
    {ω | ‖integrateSheetPath m (X.path ω)‖ ≤ η}
  have hmono : ∀ x y, 0 < x → x ≤ y → p x ≤ p y := by
    intro x y hx hxy
    exact measureReal_mono (fun ω hω => hω.trans hxy) (measure_ne_top P _)
  have hdyad : ∀ N : ℕ, 0 ≤ N →
      Real.exp (-B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(ν-1))) ≤
        p (radiusProfile β ν A N) := by
    intro N hN
    simpa [p] using hdyadic Ω P X N
  have hmain := hprofiles p hmono hdyad ε hε hsmall
  have hcast : ((ν:ℝ)-1) = ((ν-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ ν)]
    norm_num
  have hshape : ((ν:ℝ)-1)+(ν:ℝ)/β =
      ((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*(m₀:ℝ)+1) := by
    rw [hcast]
  simp only [gradedLogRate] at hmain
  rw [hcast] at hmain
  simpa [p, BrownianSharp.Latest.smallBallRate, β, hshape,
    div_eq_mul_inv] using hmain

/-- Full latest integrated-sheet two-sided clause: the entropy/Cameron--Martin
shift lower bound and the actual finite-Gaussian/dyadic upper bound together. -/
theorem latest_integratedSheet_certified :
    BrownianSharp.Latest.IntegratedSheetStatement := by
  intro d hd m m₀ ν hν hm
  obtain ⟨c,εc,hc,hεc,hεcsmall,hlower⟩ :=
    integratedSheet_oneSided_lowerLog hd m m₀ ν hν hm
  obtain ⟨C,εC,hC,hεC,hεCsmall,hupper⟩ :=
    integratedSheet_oneSided_upperLog hd m m₀ ν hν hm
  refine ⟨c,C,min εc εC,hc,hC,lt_min hεc hεC,
    (min_le_left _ _).trans_lt hεcsmall,?_⟩
  intro Ω _ P _ B ε hε hsmall
  exact ⟨hlower Ω P B ε hε (hsmall.trans (min_le_left _ _)),
    hupper Ω P B ε hε (hsmall.trans (min_le_right _ _))⟩

end BrownianSharp.AlignmentGaussianIntegratedReverse

