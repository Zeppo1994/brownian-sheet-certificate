import BrownianSharp.AlignmentPaperJointGlobalHighRadius
import BrownianSharp.AlignmentPaperJointGradeScaleUnscaled
import BrownianSharp.AlignmentPaperJointHighGradeCostSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Uniform actual decoded-radius bounds for individual high-grade profiles. -/

noncomputable section
open scoped NNReal
set_option maxHeartbeats 1000000

namespace BrownianSharp.AlignmentPaperJointHighGradeRadiusTerm

open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointGlobalHighRadius
open BrownianSharp.AlignmentPaperJointHighGradeCostSum
open BrownianSharp.AlignmentPaperJointGradeScaleUnscaled
open BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperLpJointDvp

/-- Each actual high-profile decoded radius is bounded by a grade-independent
exponential-polynomial profile. The prefactor is chosen before the starting
grade and the profile index. -/
theorem exists_high_decoded_radius_term_le_profile {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ N j : ℕ,
      j + 1 ≤ highProfileWindow p N →
      (decodedGradeDyadicRadius d (N + 1 + j) p
        (gradeSeriesSourceRadius d p A (N + 1 + j))
        (highProfileRank d p N (j + 1)) : ℝ) ≤
        K * ((2:ℝ)^(-(N:ℝ)) * Real.sqrt (N+1:ℝ)) *
          (2:ℝ)^(-((1 - 1/p) * (j+1:ℝ))) *
          Real.exp (highProfileEta p * (j+1:ℝ) / p) *
          (j+2:ℝ)^((d-1:ℝ)/p + 1/2) := by
  obtain ⟨Kstage, hKstage, hscale⟩ :=
    exists_stageScale_unscaled_envelope hd hp1 hA
  have hp0 : 0 < p := by linarith
  have ha : 0 < 1/p := by positivity
  let F : ℝ := (Nat.factorial (d-1) : ℝ)
  let K : ℝ := 24 * (5:ℝ)^d * Kstage * (2*F)^(1/p)
  have hF : 0 < F := by dsimp [F]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N j hj
  let n : ℕ := N + 1 + j
  let t : ℝ := (j+1:ℝ)
  let D : ℝ := (JointSampleDimension d N : ℝ)
  let Dn : ℝ := (JointSampleDimension d n : ℝ)
  let P : ℝ := (2:ℝ)^(highProfileRank d p N (j+1))
  let q : ℝ := 2 * Real.exp (highProfileEta p * t)
  let R : ℝ := F * (2:ℝ)^t * (j+2:ℝ)^(d-1)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast jointSampleDimension_pos_of_dimension_pos (n:=N) (by omega : 0<d)
  have hDn : 0 < Dn := by
    dsimp [Dn,n]
    exact_mod_cast jointSampleDimension_pos_of_dimension_pos (n:=N+1+j) (by omega : 0<d)
  have hP : 0 < P := by dsimp [P]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hR : 0 < R := by dsimp [R,F]; positivity
  have hfeasible := highProfileRank_feasible hd hp1 hp2 hj
  have hDscaled : D ≤ q * P := by
    have hmul := mul_le_mul_of_nonneg_right hfeasible.2.2 (le_of_lt hq)
    have heq : (D / 2 * Real.exp (-highProfileEta p * t)) * q = D := by
      dsimp [D,q,t]
      rw [show -highProfileEta p * (j+1:ℝ) =
        -(highProfileEta p * (j+1:ℝ)) by ring, Real.exp_neg]
      field_simp
    calc
      D = (D / 2 * Real.exp (-highProfileEta p * t)) * q := heq.symm
      _ ≤ P * q := by simpa [D,P,t] using hmul
      _ = q * P := by ring
  have hDdiv : D / P ≤ q := (div_le_iff₀ hP).2 hDscaled
  have hInv : 1/P ≤ q/D := by
    apply (le_div_iff₀ hD).2
    simpa [div_eq_mul_inv, mul_comm] using hDdiv
  have hU : Dn / P ≤ q * (Dn / D) := by
    calc
      Dn / P = Dn * (1/P) := by rw [div_eq_mul_inv, one_div]
      _ ≤ Dn * (q/D) := mul_le_mul_of_nonneg_left hInv hDn.le
      _ = q * (Dn/D) := by ring
  have hratio := highProfile_sampleDimension_ratio_bound (d:=d) (N:=N) (j:=j) hd
  have hRnat : R = F*(2:ℝ)^(j+1)*(j+2:ℝ)^(d-1) := by
    dsimp [R,t]
    have ht : (↑j:ℝ)+1 = ((j+1:ℕ):ℝ) := by norm_num
    rw [ht, Real.rpow_natCast]
  have hratioBase : Dn/D ≤ F*(2:ℝ)^(j+1)*(j+2:ℝ)^(d-1) := by
    simpa [Dn,D,n,F,Nat.cast_add,Nat.cast_one] using hratio
  have hratio' : Dn/D ≤ R := by rw [hRnat]; exact hratioBase
  have hUpow : (Dn/P)^(1/p) ≤ (q*R)^(1/p) :=
    Real.rpow_le_rpow (by positivity) (hU.trans (mul_le_mul_of_nonneg_left hratio' hq.le))
      (le_of_lt ha)
  have hprofilePow :
      (q*R)^(1/p) = (2*F)^(1/p) *
        Real.exp (highProfileEta p * t / p) *
        (2:ℝ)^(t/p) * (j+2:ℝ)^((d-1:ℝ)/p) := by
    have hQR : q*R =
        ((2*F) * Real.exp (highProfileEta p*t)) *
          ((2:ℝ)^t * (j+2:ℝ)^(d-1)) := by
      dsimp [q,R,F]
      ring
    have hexp : Real.exp (highProfileEta p * t)^(1/p) =
        Real.exp (highProfileEta p * t / p) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have htwo : ((2:ℝ)^t)^(1/p) = (2:ℝ)^(t/p) := by
      rw [(Real.rpow_mul (by norm_num : (0:ℝ)≤2) t (1/p)).symm]
      congr 1
      ring
    have hpoly : ((j+2:ℝ)^(d-1))^(1/p) =
        (j+2:ℝ)^((d-1:ℝ)/p) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity : 0 ≤ (j+2:ℝ))]
      congr 1
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      ring
    calc
      _ = (((2*F) * Real.exp (highProfileEta p*t))^(1/p)) *
          (((2:ℝ)^t * (j+2:ℝ)^(d-1))^(1/p)) := by
            rw [hQR, Real.mul_rpow (by positivity) (by positivity)]
      _ = ((2*F)^(1/p) * Real.exp (highProfileEta p*t)^(1/p)) *
          (((2:ℝ)^t)^(1/p) * ((j+2:ℝ)^(d-1))^(1/p)) := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
            congr 1
            exact Real.mul_rpow (by positivity) (by positivity)
      _ = _ := by rw [hexp, htwo, hpoly]; ring
  have hcombine : Dn^(1/p) * P^(-(1/p)) = (Dn/P)^(1/p) := by
    rw [Real.rpow_neg (le_of_lt hP), Real.div_rpow hDn.le hP.le]
    ring
  have hB : 0 < gradeSeriesSourceRadius d p A n := by
    dsimp [n]
    unfold gradeSeriesSourceRadius
    positivity
  have hdecoded := decodedRadius_coe_le (d:=d) (n:=n) (p:=p)
    (B:=gradeSeriesSourceRadius d p A n)
    (J:=highProfileRank d p N (j+1)) hB
  have hdecodedP :
      (decodedGradeDyadicRadius d n p (gradeSeriesSourceRadius d p A n)
        (highProfileRank d p N (j+1)) : ℝ) ≤
        24*(5:ℝ)^d *
          stageScale d n (gradeSeriesSourceRadius d p A n) * P^(-(1/p)) := by
    have hexp : (-1:ℝ)/p = -(1/p) := by ring
    simpa only [P, hexp] using hdecoded
  have hscale' := hscale n
  have hscaleCombined :
      stageScale d n (gradeSeriesSourceRadius d p A n) * P^(-(1/p)) ≤
        Kstage * (2:ℝ)^(-(n:ℝ)) * Real.sqrt (n+1:ℝ) * (Dn/P)^(1/p) := by
    calc
      _ ≤ (Kstage * (2:ℝ)^(-(n:ℝ)) * Real.sqrt (n+1:ℝ) * Dn^(1/p)) *
          P^(-(1/p)) := by
            exact mul_le_mul_of_nonneg_right hscale' (by positivity)
      _ = Kstage * (2:ℝ)^(-(n:ℝ)) * Real.sqrt (n+1:ℝ) *
          (Dn^(1/p) * P^(-(1/p))) := by ring
      _ = _ := by rw [hcombine]
  have hradBound :
      (decodedGradeDyadicRadius d n p (gradeSeriesSourceRadius d p A n)
        (highProfileRank d p N (j+1)) : ℝ) ≤
        24*(5:ℝ)^d*Kstage*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)*(q*R)^(1/p) := by
    calc
      _ ≤ 24*(5:ℝ)^d *
          (stageScale d n (gradeSeriesSourceRadius d p A n) * P^(-(1/p))) := by
            calc
              _ ≤ 24*(5:ℝ)^d *
                  stageScale d n (gradeSeriesSourceRadius d p A n) * P^(-(1/p)) := hdecodedP
              _ = _ := by ring
      _ ≤ 24*(5:ℝ)^d *
          (Kstage*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)*(Dn/P)^(1/p)) :=
            mul_le_mul_of_nonneg_left hscaleCombined (by positivity)
      _ ≤ 24*(5:ℝ)^d*Kstage*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)*(q*R)^(1/p) := by
            have hfactor : 0 ≤ 24*(5:ℝ)^d*Kstage*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ) := by positivity
            have hm := mul_le_mul_of_nonneg_left hUpow hfactor
            nlinarith [hm]
  have hNpoly : (n+1:ℝ) ≤ (N+1:ℝ)*(j+2:ℝ) := by
    dsimp [n]
    push_cast
    nlinarith [show (0:ℝ) ≤ (N:ℝ) by positivity,
      show (0:ℝ) ≤ (j:ℝ) by positivity]
  have hroot : Real.sqrt (n+1:ℝ) ≤
      Real.sqrt (N+1:ℝ)*Real.sqrt (j+2:ℝ) := by
    calc
      _ ≤ Real.sqrt ((N+1:ℝ)*(j+2:ℝ)) := Real.sqrt_le_sqrt hNpoly
      _ = _ := by rw [Real.sqrt_mul (by positivity)]
  have hdecay : (2:ℝ)^(-(n:ℝ))*(2:ℝ)^(t/p) =
      (2:ℝ)^(-(N:ℝ))*(2:ℝ)^(-((1-1/p)*t)) := by
    calc
      _ = (2:ℝ)^(-(n:ℝ) + t/p) := by
        rw [← Real.rpow_add (by norm_num : 0 < (2:ℝ))]
      _ = (2:ℝ)^(-(N:ℝ) - ((1-1/p)*t)) := by
        congr 1
        dsimp [n,t]
        push_cast
        ring
      _ = _ := by
        rw [show -(N:ℝ)-((1-1/p)*t) = -(N:ℝ)+ -((1-1/p)*t) by ring,
          Real.rpow_add (by norm_num : 0 < (2:ℝ))]
  have hpolyFinal : (j+2:ℝ)^((d-1:ℝ)/p)*Real.sqrt (j+2:ℝ) =
      (j+2:ℝ)^((d-1:ℝ)/p+1/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : 0 < (j+2:ℝ))]
  calc
    _ ≤ 24*(5:ℝ)^d*Kstage*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)*(q*R)^(1/p) := hradBound
    _ = 24*(5:ℝ)^d*Kstage*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)*
          ((2*F)^(1/p)*Real.exp (highProfileEta p*t/p)*(2:ℝ)^(t/p)*
            (j+2:ℝ)^((d-1:ℝ)/p)) := by rw [hprofilePow]
    _ ≤ Kstage*24*(5:ℝ)^d*(2*F)^(1/p)*
          ((2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ))*
          (2:ℝ)^(-((1-1/p)*t))*Real.exp (highProfileEta p*t/p)*
          (j+2:ℝ)^((d-1:ℝ)/p+1/2) := by
        let C0 : ℝ := 24*(5:ℝ)^d*Kstage*(2*F)^(1/p)
        let Q : ℝ := (2:ℝ)^(-(n:ℝ))*(2:ℝ)^(t/p) *
          Real.exp (highProfileEta p*t/p)*(j+2:ℝ)^((d-1:ℝ)/p)
        have hQ : 0 ≤ Q := by dsimp [Q]; positivity
        have hcoef : 0 ≤ C0*Q := by dsimp [C0]; positivity
        have hm' : C0 * Q * Real.sqrt (n+1:ℝ) ≤
            C0 * Q * (Real.sqrt (N+1:ℝ)*Real.sqrt (j+2:ℝ)) := by
          exact mul_le_mul_of_nonneg_left hroot hcoef
        calc
          _ = C0 * Q * Real.sqrt (n+1:ℝ) := by dsimp [C0,Q]; ring
          _ ≤ C0 * Q * (Real.sqrt (N+1:ℝ)*Real.sqrt (j+2:ℝ)) := hm'
          _ = C0 * ((2:ℝ)^(-(n:ℝ))*(2:ℝ)^(t/p)) *
              Real.exp (highProfileEta p*t/p) *
              ((j+2:ℝ)^((d-1:ℝ)/p)*Real.sqrt (j+2:ℝ)) *
              Real.sqrt (N+1:ℝ) := by dsimp [Q]; ring
          _ = C0 * ((2:ℝ)^(-(N:ℝ))*(2:ℝ)^(-((1-1/p)*t))) *
              Real.exp (highProfileEta p*t/p) *
              (j+2:ℝ)^((d-1:ℝ)/p+1/2) * Real.sqrt (N+1:ℝ) := by
                rw [hdecay, hpolyFinal]
          _ = _ := by dsimp [C0,K]; ring
    _ = K * ((2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ))*
          (2:ℝ)^(-((1-1/p)*(j+1:ℝ)))*
          Real.exp (highProfileEta p*(j+1:ℝ)/p)*
          (j+2:ℝ)^((d-1:ℝ)/p+1/2) := by
        dsimp [K,t]
        ring

end BrownianSharp.AlignmentPaperJointHighGradeRadiusTerm
