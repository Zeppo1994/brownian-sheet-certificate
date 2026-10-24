import BrownianSharp.AlignmentGaussianGradedKernelReverse
import BrownianSharp.AlignmentGaussianGradedReverseClosure
import BrownianSharp.AlignmentGaussianDiagonalCoordinates
import BrownianSharp.AlignmentFractionalSheetTensorFeature
import BrownianSharp.AlignmentGaussianGridLimit
import BrownianSharp.AlignmentEndpointCubeGridLimit
import BrownianSharp.AlignmentFractionalSheetGridConfinement
import BrownianSharp.AlignmentGaussianChaining
import BrownianSharp.AlignmentLatestStatements
import Mathlib.Tactic

/-! Conditional upper-log closure for actual fractional Brownian sheets,
assuming a uniform graded source-frame profile. The frame profile is stated
explicitly; this module handles the Gaussian grid law, dense-grid limit, and
radius inversion. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianFractionalReverseClosure

open BrownianSharp.AlignmentGaussianGradedKernelReverse
open BrownianSharp.AlignmentGaussianGradedReverseClosure
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentEndpointCubeGridLimit
open BrownianSharp.AlignmentFractionalSheetGridConfinement
open BrownianSharp.AlignmentGaussianChaining
open BrownianSharp.AlignmentExponentialGradedReverseInversion
open BrownianSharp.Latest
open GaussianProjection
open HaarQuarter

/-- The literal one-sided fractional-sheet upper-log conclusion follows from
uniform frame profiles. The filtration and all profile constants are fixed
before the probability space and realization. -/
theorem fractionalSheet_upperLog_of_uniform_frame_profiles
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν)
    (Cvar Rvar Cdim η : ℝ)
    (hCvar : 0 ≤ Cvar) (hRvar : 0 ≤ Rvar) (hCdim : 0 ≤ Cdim)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (F : ℕ → Type*)
    (hfinite : ∀ M, Fintype (F M))
    (hdecEq : ∀ M, DecidableEq (F M))
    (hnonempty : ∀ M, Nonempty (F M))
    (e : ∀ M, F M → FullProductL2 d)
    (grade : ∀ M, F M → ℕ)
    (horth : ∀ M, letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ i j, ⟪e M i, e M j⟫ = if i = j then 1 else 0)
    (hvar : ∀ M N, letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ z, ∑ i : F M, (contractionScale η N (grade M i) *
          ⟪fractionalSheetFeature H hH z, e M i⟫)^2 ≤
        Cvar * (Real.rpow 2 (-(2*h) * (N : ℝ) / 2))^2 *
          (((N + 1 : ℕ) : ℝ)^((ν-1 : ℕ))))
    (hincrement : ∀ M N, letI : Fintype (F M) := hfinite M
      ∀ z w, ∑ i : F M, (contractionScale η N (grade M i) *
          (⟪fractionalSheetFeature H hH z, e M i⟫ -
            ⟪fractionalSheetFeature H hH w, e M i⟫))^2 ≤
        Rvar * (dist z w)^(2*h))
    (hfiber : ∀ M N, letI : Fintype (F M) := hfinite M
      ∀ g : Fin (N+1),
        (Fintype.card {i : F M // grade M i = g.val} : ℝ) ≤
          Cdim * (2:ℝ)^g.val * (((g.val+1:ℕ):ℝ)^(ν-1)))
    (happrox : ∀ ε, 0 < ε → ∃ M,
      letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ z, ‖fractionalSheetFeature H hH z -
        projection (e M) (fractionalSheetFeature H hH z)‖ ≤ ε) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube d Ω P), B.H = H →
        ∀ ε, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖B.path ω‖ ≤ ε} ∧
          -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) ≤
            C * Latest.smallBallRate h⁻¹
              (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε := by
  have hcard : 0 < (Finset.univ.filter (fun i : Fin d => H i = h)).card := by
    rw [show (Finset.univ.filter (fun i : Fin d => H i = h)).card = ν by
      simpa [eq_comm] using hmin.2]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  have hieq : H i = h := (Finset.mem_filter.mp hi).2
  have hh : 0 < h := by rw [← hieq]; exact (hH i).1
  have hβ : 0 < 2*h := by positivity
  obtain ⟨A,D,hA,hD,hdyadic⟩ :=
    gradedKernel_grid_lower_bound_of_uniform_frames
      (d:=d) (β:=2*h) (h:=h) Cvar Rvar Cdim η (ν-1)
      hβ hh hCvar hRvar hCdim hη hη1
  have hB : 0 < D + Real.log (4:ℝ) := by
    have hlog : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
    linarith
  obtain ⟨C,ε₀,hC,hε₀,hε₀small,hprofile⟩ :=
    uniform_upperLog_of_dyadic_probability_lower ν 0 hν (2*A)
      (D + Real.log (4:ℝ)) (2*h) (by linarith) hB hβ
  obtain ⟨εidx,_,hεidx,_,hindex⟩ :=
    exists_dyadic_radius_index ν 0 hν (A:=2*A) (β:=2*h) (by linarith) hβ
  let εfinal := min ε₀ εidx
  have hεfinal : 0 < εfinal := lt_min hε₀ hεidx
  have hεfinalsmall : εfinal < Real.exp (-1) :=
    (min_le_left _ _).trans_lt hε₀small
  refine ⟨C,εfinal,hC,hεfinal,hεfinalsmall,?_⟩
  intro Ω _ P _ B hBH ε hε hsmall
  let p : ℝ → ℝ := fun r => P.real {ω | ‖B.path ω‖ ≤ r}
  have hmono : ∀ x y, 0 < x → x ≤ y → p x ≤ p y := by
    intro x y hx hxy
    exact measureReal_mono (fun ω hω => hω.trans hxy) (measure_ne_top P _)
  have hdyad : ∀ N : ℕ, 0 ≤ N →
      Real.exp (-(D+Real.log (4:ℝ))*
        ((2:ℝ)^N*((N+1:ℕ):ℝ)^(ν-1))) ≤
        p (radiusProfile (2*h) ν (2*A) N) := by
    intro N hN
    let cost : ℝ := (2:ℝ)^N*((N+1:ℕ):ℝ)^(ν-1)
    let rad : ℝ := A*Real.rpow 2 (-2*h*(N:ℝ)/2)*
      Real.sqrt (((N+1:ℕ):ℝ)^ν)
    have hrate : 0 < Real.rpow 2 (-2*h*(N:ℝ)/2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hrad : 0 < rad := by dsimp [rad]; positivity
    have hcost1 : 1 ≤ cost := by
      dsimp [cost]
      have hpowN : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
      have hbase : 1 ≤ ((N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      have hpow : 1 ≤ ((N+1:ℕ):ℝ)^((ν-1):ℕ) := one_le_pow₀ hbase
      calc
        1 ≤ ((N+1:ℕ):ℝ)^((ν-1):ℕ) := hpow
        _ ≤ (2:ℝ)^N * ((N+1:ℕ):ℝ)^((ν-1):ℕ) := by
          have hb := mul_le_mul_of_nonneg_right hpowN
            (by positivity : 0 ≤ ((N+1:ℕ):ℝ)^((ν-1):ℕ))
          nlinarith
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-D*cost)) *
        ((1/2:ENNReal)*(1/2:ENNReal))
    have hgrid : ∀ M : ℕ, c ≤ P {ω | cubeGridMaximum M (B.path ω) ≤ 2*rad} := by
      intro M
      let J := CubeDyadicGrid d M
      let x : J → BrownianCubeAnchor d := cubeDyadicAnchor
      let X : Ω → J → ℝ := fun ω j => B.path ω (x j)
      have hbound := hdyadic F hfinite hdecEq hnonempty
        (Ω:=Ω) (J:=J) (H:=FullProductL2 d) (P:=P)
        X (fractionalSheetFeature H hH) x e grade
        horth hvar hincrement hfiber happrox
        (fractionalSheet_grid_hasGaussianLaw B x)
        (fun j => B.mean_zero (x j))
        (by
          intro i j
          rw [B.covariance,hBH,fractionalSheetFeature_gram]) N
      have hνexp : (ν-1:ℕ)+1=ν := Nat.sub_add_cancel (by omega : 1≤ν)
      have hevent : {ω | ∀ j : J, |B.path ω (x j)| ≤ 2*rad} =
          {ω | cubeGridMaximum M (B.path ω) ≤ 2*rad} := by
        ext ω
        change (∀ j : CubeDyadicGrid d M, |B.path ω (cubeDyadicAnchor j)| ≤ 2*rad) ↔
          ‖fun j : CubeDyadicGrid d M => B.path ω (cubeDyadicAnchor j)‖ ≤ 2*rad
        constructor
        · intro hj
          apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*rad)).2
          intro j
          simpa only [Real.norm_eq_abs] using hj j
        · intro hj j
          have h := (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*rad)).1 hj j
          simpa only [Real.norm_eq_abs] using h
      have hcostExp : -D*(2:ℝ)^N*((N+1:ℕ):ℝ)^((ν-1):ℕ) = -D*cost := by
        dsimp [cost]
        ring
      rw [hcostExp] at hbound
      have hbound' : c ≤ P {ω | ∀ j : J, |B.path ω (x j)| ≤ 2*rad} := by
        simpa [c,X,x,J,rad,hνexp,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
          mul_assoc,ENNReal.ofReal_mul,ENNReal.ofReal_ofNat] using hbound
      rw [hevent] at hbound'
      exact hbound'
    have hF : Measurable B.path := B.measurable_path
    have huniform := cube_grid_mass_lower_to_uniform_mass_lower
      P B.path hF (2*rad) (by positivity) c hgrid
    have hreal := ENNReal.toReal_mono (measure_ne_top P _) huniform
    have hmass : Real.exp (-D*cost)/4 ≤ p (2*rad) := by
      have hmass' : c.toReal ≤ p (2*rad) := by
        simpa [p,Measure.real_def] using hreal
      dsimp [c] at hmass'
      rw [ENNReal.toReal_mul,ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hmass'
      norm_num at hmass'
      convert hmass' using 1 <;> ring_nf
    have hexp : Real.exp (-(D+Real.log (4:ℝ))*cost) ≤
        Real.exp (-D*cost)/4 := by
      have hlog : 0 ≤ Real.log (4:ℝ) := le_of_lt (Real.log_pos (by norm_num))
      have harg : -Real.log (4:ℝ)*cost ≤ -Real.log (4:ℝ) := by nlinarith
      have hfactor : Real.exp (-Real.log (4:ℝ)*cost) ≤ 1/4 := by
        calc
          _ ≤ Real.exp (-Real.log (4:ℝ)) := Real.exp_le_exp.mpr harg
          _ = 1/4 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
      have heq : -(D+Real.log (4:ℝ))*cost =
          -D*cost + (-Real.log (4:ℝ)*cost) := by ring
      rw [heq,Real.exp_add]
      calc
        Real.exp (-D*cost)*Real.exp (-Real.log (4:ℝ)*cost) ≤
            Real.exp (-D*cost)*(1/4) :=
              mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg _)
        _ = Real.exp (-D*cost)/4 := by ring
    have hsqrt : Real.sqrt (((N+1:ℕ):ℝ)^ν) =
        ((N+1:ℕ):ℝ)^((ν:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((N+1:ℕ):ℝ))]
      congr 1
      ring_nf
    have hradius : 2*rad = radiusProfile (2*h) ν (2*A) N := by
      dsimp [rad,radiusProfile]
      have he : -2*h*(N:ℝ)/2 = -(2*h)*(N:ℝ)/2 := by ring
      rw [he,hsqrt]
      ring_nf
    rw [hradius] at hmass
    have h := hexp.trans hmass
    simpa [p,cost] using h
  obtain ⟨N,_,hrad,_⟩ := hindex ε hε (hsmall.trans (min_le_right _ _))
  have hradpos : 0 < radiusProfile (2*h) ν (2*A) N := by
    unfold radiusProfile
    positivity
  have hmasspos := (hdyad N (Nat.zero_le N)).trans
    (hmono _ _ hradpos hrad)
  have hpositive : 0 < p ε := lt_of_lt_of_le (Real.exp_pos _) hmasspos
  have hmain := hprofile p hmono hdyad ε hε
    (hsmall.trans (min_le_left _ _))
  have hcast : ((ν:ℝ)-1) = ((ν-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤ν)]
    norm_num
  have hshape : ((ν:ℝ)-1)+(ν:ℝ)/(2*h) =
      ((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h) := by rw [hcast]
  have hinv : 2/(2*h)=h⁻¹ := by field_simp
  have hshape' : ((ν:ℝ)-1)+(ν:ℝ)*(h⁻¹*2⁻¹) =
      ((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h) := by rw [hcast]; ring
  have hrate : -Real.log (p ε) ≤ C * Latest.smallBallRate h⁻¹
      (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε := by
    simpa [gradedLogRate,Latest.smallBallRate,Real.log_inv,hshape',hinv,
      div_eq_mul_inv] using hmain
  exact ⟨hpositive, by simpa [p] using hrate⟩

end BrownianSharp.AlignmentGaussianFractionalReverseClosure
