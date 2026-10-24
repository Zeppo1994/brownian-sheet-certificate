import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentAuditLifting
import Mathlib.MeasureTheory.Measure.Basic

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentGaussianPacking

theorem finite_separated_ball_mass_bound {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (S : Finset X) (ε : ℝ) (q : ENNReal)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → 2*ε<dist x y)
    (hmass : ∀ x∈S, q≤μ (Metric.closedBall x ε)) :
    (S.card:ENNReal)*q≤1 := by
  classical
  have hdisj : Set.PairwiseDisjoint (S:Set X) (fun x => Metric.closedBall x ε) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hz1 : dist x z≤ε := by simpa only [Metric.mem_closedBall,dist_comm] using hzx
    have hz2 : dist z y≤ε := hzy
    have htri := dist_triangle x z y
    have hdist := hsep x hx y hy hxy
    linarith
  calc
    (S.card:ENNReal)*q = ∑ _x∈S,q := by simp
    _ ≤ ∑ x∈S, μ (Metric.closedBall x ε) := Finset.sum_le_sum (fun x hx => hmass x hx)
    _ = μ (⋃ x∈S,Metric.closedBall x ε) :=
      (measure_biUnion_finset hdisj (fun _ _ => isClosed_closedBall.measurableSet)).symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

/-- The finite packing step behind the entropy/small-ball comparison.
The analytic input is an explicit lower bound for translated ball masses. -/
theorem smallBall_mass_bound_of_translated_packing
    {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (S : Finset X) (ε R : ℝ)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → 2*ε<dist x y)
    (hshift : ∀ x∈S, ENNReal.ofReal (Real.exp (-(R^2)/2)) *
      μ (Metric.closedBall 0 ε) ≤ μ (Metric.closedBall x ε)) :
    (S.card:ENNReal)*ENNReal.ofReal (Real.exp (-(R^2)/2)) *
      μ (Metric.closedBall 0 ε) ≤ 1 := by
  simpa only [mul_assoc] using finite_separated_ball_mass_bound μ S ε
    (ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 ε)) hsep hshift


theorem smallBall_mass_bound_of_external_cover
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set X)
    (ρ : ℝ≥0) (hρ : 0<(ρ:ℝ)) (M : ℕ)
    (hcover : (M:ℕ∞)<Metric.externalCoveringNumber ρ K)
    (R : ℝ) (hR : 0<R)
    (hshift : ∀ x∈K,
      ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 (R*ρ/3)) ≤
        μ (Metric.closedBall (R • x) (R*ρ/3))) :
    (M:ENNReal)*ENNReal.ofReal (Real.exp (-(R^2)/2))*
      μ (Metric.closedBall 0 (R*ρ/3)) ≤ 1 := by
  classical
  obtain ⟨S,hSK,hsep,hcard⟩ :=
    AlignmentAuditLifting.exists_finite_packing_of_externalCoveringNumber_gt K ρ M hcover
  let S' : Finset X := S.image (fun x => R • x)
  have hinj : Function.Injective (fun x : X => R • x) := by
    intro x y h
    have hh := congrArg (fun z : X => R⁻¹ • z) h
    simpa only [smul_smul,inv_mul_cancel₀ hR.ne',one_smul] using hh
  have hcard' : S'.card=S.card := Finset.card_image_of_injective S hinj
  have hsep' : ∀x∈S',∀y∈S',x≠y → 2*(R*ρ/3)<dist x y := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    have hab : a≠b := by intro h; exact hxy (congrArg (fun z : X => R • z) h)
    have hs := hsep ha hb hab
    have hs' : ENNReal.ofReal (ρ:ℝ)<ENNReal.ofReal (dist a b) := by
      simpa only [edist_dist,ENNReal.ofReal_coe_nnreal] using hs
    have hdist : (ρ:ℝ)<dist a b := (ENNReal.ofReal_lt_ofReal_iff'.mp hs').1
    have hscaled := mul_lt_mul_of_pos_left hdist hR
    rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hR,← dist_eq_norm]
    nlinarith [mul_pos hR hρ]
  have hmasses : ∀x∈S',
      ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 (R*ρ/3)) ≤
        μ (Metric.closedBall x (R*ρ/3)) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact hshift a (hSK ha)
  have hbound := finite_separated_ball_mass_bound μ S' (R*ρ/3)
    (ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 (R*ρ/3))) hsep' hmasses
  have hM : (M:ENNReal)≤(S'.card:ENNReal) := by
    rw [hcard']
    exact_mod_cast hcard.le
  simpa only [mul_assoc] using (mul_le_mul hM le_rfl bot_le bot_le).trans hbound

theorem smallBall_mass_bound_of_entropy_radius
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set X)
    (ρ : ℝ≥0) (hρ : 0<(ρ:ℝ)) (k : ℕ)
    (hentropy : (ρ:ENNReal)<HaarQuarter.TheoremD.entropyNumber k K)
    (R : ℝ) (hR : 0<R)
    (hshift : ∀x∈K,
      ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 (R*ρ/3)) ≤
        μ (Metric.closedBall (R • x) (R*ρ/3))) :
    ((2^(k-1):ℕ):ENNReal)*ENNReal.ofReal (Real.exp (-(R^2)/2))*
      μ (Metric.closedBall 0 (R*ρ/3)) ≤ 1 := by
  have hcover : ((2^(k-1):ℕ):ℕ∞)<Metric.externalCoveringNumber ρ K := by
    apply lt_of_not_ge
    intro hc
    exact (not_le_of_gt hentropy) (sInf_le ⟨ρ,rfl,hc⟩)
  exact smallBall_mass_bound_of_external_cover μ K ρ hρ (2^(k-1)) hcover R hR hshift


theorem smallBall_mass_exponential_of_entropy_radius
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set X)
    (ρ : ℝ≥0) (hρ : 0<(ρ:ℝ)) (k : ℕ) (hk : 4≤k)
    (hentropy : (ρ:ENNReal)<HaarQuarter.TheoremD.entropyNumber k K)
    (hshift : ∀x∈K,
      ENNReal.ofReal (Real.exp (-(Real.log 2*(k:ℝ))/2))*
        μ (Metric.closedBall 0 (Real.sqrt (Real.log 2*(k:ℝ))*ρ/3)) ≤
      μ (Metric.closedBall ((Real.sqrt (Real.log 2*(k:ℝ))) • x)
        (Real.sqrt (Real.log 2*(k:ℝ))*ρ/3))) :
    μ.real (Metric.closedBall 0 (Real.sqrt (Real.log 2*(k:ℝ))*ρ/3)) ≤
      Real.exp (-(Real.log 2/4)*(k:ℝ)) := by
  let R := Real.sqrt (Real.log 2*(k:ℝ))
  have hlog : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hR : 0<R := Real.sqrt_pos.mpr (mul_pos hlog hkpos)
  have hR2 : R^2=Real.log 2*(k:ℝ) := Real.sq_sqrt (mul_pos hlog hkpos).le
  have hb := smallBall_mass_bound_of_entropy_radius μ K ρ hρ k hentropy R hR
    (by simpa only [hR2] using hshift)
  have hreal := ENNReal.toReal_mono (by norm_num : (1:ENNReal)≠⊤) hb
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,ENNReal.toReal_one] at hreal
  push_cast at hreal
  have hpow : (2:ℝ)^(k-1)=Real.exp (((k-1:ℕ):ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hcoef : Real.exp ((Real.log 2/4)*(k:ℝ)) ≤
      (2:ℝ)^(k-1)*Real.exp (-(R^2)/2) := by
    rw [hpow,← Real.exp_add,hR2]
    apply Real.exp_le_exp.mpr
    rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one]
    have hk4 : (4:ℝ)≤k := by exact_mod_cast hk
    nlinarith [mul_nonneg (sub_nonneg.mpr hk4) hlog.le]
  have hp0 : 0≤(μ (Metric.closedBall 0 (R*ρ/3))).toReal := ENNReal.toReal_nonneg
  have hh : Real.exp ((Real.log 2/4)*(k:ℝ))*
      (μ (Metric.closedBall 0 (R*ρ/3))).toReal ≤1 :=
    (mul_le_mul_of_nonneg_right hcoef hp0).trans (by simpa only [mul_assoc] using hreal)
  have hm : (μ (Metric.closedBall 0 (R*ρ/3))).toReal ≤
      1/Real.exp ((Real.log 2/4)*(k:ℝ)) :=
    (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hh)
  change (μ (Metric.closedBall 0 (R*ρ/3))).toReal ≤ _
  simpa only [Real.exp_neg,one_div,neg_mul] using hm


theorem smallBall_index_rate_of_entropy_lower
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set X)
    (r a c : ℝ) (hc : 0<c) (k : ℕ) (hk : 4≤k)
    (hentropy : ENNReal.ofReal (c*logarithmicIndexRate r a k) ≤
      HaarQuarter.TheoremD.entropyNumber k K)
    (hshift : ∀R : ℝ,0<R → ∀ε : ℝ,0<ε → ∀x∈K,
      ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 ε) ≤
        μ (Metric.closedBall (R • x) ε)) :
    μ.real (Metric.closedBall 0
      ((c*Real.sqrt (Real.log 2)/6)*(k:ℝ)^(-(r-1/2))*(Real.log (k:ℝ))^a)) ≤
      Real.exp (-(Real.log 2/4)*(k:ℝ)) := by
  have hk2 : 2≤k := by omega
  have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hkp : (0:ℝ)<k := by linarith
  have hlogk : 0<Real.log (k:ℝ) := Real.log_pos hkR
  have hrate : 0<logarithmicIndexRate r a k :=
    mul_pos (Real.rpow_pos_of_pos hkp _) (Real.rpow_pos_of_pos hlogk _)
  let ρ : ℝ≥0 := ⟨(c/2)*logarithmicIndexRate r a k,by positivity⟩
  have hρ : 0<(ρ:ℝ) := mul_pos (by positivity) hrate
  have hstrict : (ρ:ENNReal)<HaarQuarter.TheoremD.entropyNumber k K := by
    have hlt : (c/2)*logarithmicIndexRate r a k<c*logarithmicIndexRate r a k := by
      nlinarith [mul_pos hc hrate]
    have he : (ρ:ENNReal)=ENNReal.ofReal ((c/2)*logarithmicIndexRate r a k) := by
      exact ENNReal.ofReal_coe_nnreal.symm
    rw [he]
    exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc hrate)).2 hlt |>.trans_le hentropy
  let R := Real.sqrt (Real.log 2*(k:ℝ))
  have hlog : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hR : 0<R := Real.sqrt_pos.mpr (mul_pos hlog hkp)
  have hR2 : R^2=Real.log 2*(k:ℝ) := Real.sq_sqrt (mul_pos hlog hkp).le
  have hprob := smallBall_mass_exponential_of_entropy_radius μ K ρ hρ k hk hstrict
    (by
      intro x hx
      have h := hshift R hR (R*ρ/3) (by positivity) x hx
      simpa only [hR2] using h)
  have hroot : R=Real.sqrt (Real.log 2)*(k:ℝ)^(1/2:ℝ) := by
    dsimp [R]
    simp only [Real.sqrt_mul hlog.le,Real.sqrt_eq_rpow]
  have hpow : (k:ℝ)^(1/2:ℝ)*(k:ℝ)^(-r)=(k:ℝ)^(-(r-1/2)) := by
    rw [←Real.rpow_add hkp]
    congr 1
    ring
  have hradius : R*(ρ:ℝ)/3 =
      (c*Real.sqrt (Real.log 2)/6)*(k:ℝ)^(-(r-1/2))*(Real.log (k:ℝ))^a := by
    change R*((c/2)*logarithmicIndexRate r a k)/3=_
    rw [hroot]
    unfold logarithmicIndexRate
    calc
      _ = (c*Real.sqrt (Real.log 2)/6)*
          ((k:ℝ)^(1/2:ℝ)*(k:ℝ)^(-r))*(Real.log (k:ℝ))^a := by ring
      _ = _ := by rw [hpow]
  simpa only [←hradius] using hprob

end BrownianSharp.AlignmentGaussianPacking
