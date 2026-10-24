import BrownianSharp.BrownianCriticalProjection
import BrownianSharp.BrownianCriticalTensor

open MeasureTheory

namespace HaarQuarter

private theorem momentIoc_id_sub {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (x - a) ∂volume = (b - a) ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => (x - a) ^ 2 / 2) (f' := fun x => x - a) hab
    (by fun_prop)
    (fun x hx => by
      have h := (hasDerivAt_pow 2 (x - a)).div_const (2 : ℝ) |>.comp x
        ((hasDerivAt_id x).sub_const a)
      simpa [Function.comp_def] using h)
    ((continuousOn_id.sub continuousOn_const).intervalIntegrable)]
  ring

private theorem realDyadicHaar_firstMoment (r c : ℕ) :
    ∫ x, (x - realDyadicLeft r c) * realDyadicHaar r c x ∂volume =
      (realDyadicRight r c - realDyadicLeft r c) ^ 2 / 4 := by
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  have hpow : 0 < (2 : ℝ)^r := by positivity
  have hab : a < b := by
    dsimp [a,b,realDyadicLeft,realDyadicRight]
    apply div_lt_div_of_pos_right
    · exact_mod_cast Nat.lt_succ_self c
    · exact hpow
  have ham : a ≤ m := by
    dsimp [a,m,realDyadicLeft,realDyadicMid]
    apply div_le_div_of_nonneg_right _ (le_of_lt hpow)
    norm_num
  have hmb : m ≤ b := by
    dsimp [m,b,realDyadicMid,realDyadicRight]
    apply div_le_div_of_nonneg_right _ (le_of_lt hpow)
    norm_num
  have hleft : Integrable ((Set.Ioc a m).indicator (fun x => x-a)) volume := by
    exact ((continuousOn_id.sub continuousOn_const).integrableOn_compact isCompact_Icc
      |>.mono_set Set.Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hright : Integrable ((Set.Ioc m b).indicator (fun x => x-a)) volume := by
    exact ((continuousOn_id.sub continuousOn_const).integrableOn_compact isCompact_Icc
      |>.mono_set Set.Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hrep : (fun x => (x-a) * realDyadicHaar r c x) =ᵐ[volume]
      fun x => (Set.Ioc m b).indicator (fun x => x-a) x -
        (Set.Ioc a m).indicator (fun x => x-a) x := by
    filter_upwards [criticalIocHaar_ae_eq_real r c] with x hx
    rw [← hx]
    change (x-a) * ((Set.Ioc m b).indicator (fun _ : ℝ => (1:ℝ)) x -
      (Set.Ioc a m).indicator (fun _ : ℝ => (1:ℝ)) x) = _
    by_cases hr : x ∈ Set.Ioc m b <;> by_cases hl : x ∈ Set.Ioc a m
    · have : False := by
        simp only [Set.mem_Ioc] at hr hl
        linarith
      simp [hr, hl] at this
    · simp [hr, hl]
    · simp [hr, hl]
    · simp [hr, hl]
  rw [integral_congr_ae hrep, integral_sub hright hleft,
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  have hr : ∫ x in Set.Ioc m b, (x-a) ∂volume =
      ((b-a)^2 - (m-a)^2) / 2 := by
    rw [← intervalIntegral.integral_of_le hmb]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun x : ℝ => (x-a)^2/2) (f' := fun x => x-a) hmb
      (by fun_prop)
      (fun x hx => by
        have h := (hasDerivAt_pow 2 (x-a)).div_const (2 : ℝ) |>.comp x
          ((hasDerivAt_id x).sub_const a)
        simpa [Function.comp_def] using h)
      ((continuousOn_id.sub continuousOn_const).intervalIntegrable)]
    ring
  rw [hr, momentIoc_id_sub ham]
  dsimp [a,m,b]
  unfold realDyadicMid realDyadicLeft realDyadicRight
  field_simp
  <;> ring

end HaarQuarter
namespace HaarQuarter


private theorem realDyadicHaar_integral_zero (r c : ℕ) :
    ∫ x, realDyadicHaar r c x ∂volume = 0 := by
  calc
    ∫ x, realDyadicHaar r c x ∂volume =
        ∫ x, discrepancyIocDyadicHaar r c x ∂volume := by
          apply integral_congr_ae
          exact (criticalIocHaar_ae_eq_real r c).symm
    _ = 0 := by
      let a := realDyadicLeft r c
      let m := realDyadicMid r c
      let b := realDyadicRight r c
      have hab : a < m := by
        dsimp [a, m, realDyadicLeft, realDyadicMid]
        apply div_lt_div_of_pos_right
        · norm_num
        · positivity
      have hmb : m < b := by
        dsimp [m, b, realDyadicMid, realDyadicRight]
        apply div_lt_div_of_pos_right
        · norm_num
        · positivity
      have hL : Integrable ((Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
        apply (integrableOn_const (ne_of_lt measure_Ioc_lt_top)).integrable_indicator
        exact measurableSet_Ioc
      have hR : Integrable ((Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
        apply (integrableOn_const (ne_of_lt measure_Ioc_lt_top)).integrable_indicator
        exact measurableSet_Ioc
      change ∫ x, (Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ)) x -
        (Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ)) x ∂volume = 0
      rw [integral_sub hR hL, integral_indicator_const, integral_indicator_const]
      · rw [Real.volume_real_Ioc_of_le hmb.le, Real.volume_real_Ioc_of_le hab.le]
        have hm : m = (a + b) / 2 := by
          dsimp [a, m, b, realDyadicLeft, realDyadicMid, realDyadicRight]
          field_simp
          ring
        rw [hm]
        ring
      · exact measurableSet_Ioc
      · exact measurableSet_Ioc


end HaarQuarter

namespace HaarQuarter

private theorem affine_realDyadicHaar_integrable (r c : ℕ) (α β : ℝ) :
    Integrable (fun x => (α*x+β) * realDyadicHaar r c x) volume := by
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  have ham : a ≤ m := by
    dsimp [a,m,realDyadicLeft,realDyadicMid]
    apply div_le_div_of_nonneg_right _ (by positivity)
    norm_num
  have hmb : m ≤ b := by
    dsimp [m,b,realDyadicMid,realDyadicRight]
    apply div_le_div_of_nonneg_right _ (by positivity)
    norm_num
  have hL : Integrable ((Set.Ioc a m).indicator (fun x : ℝ => α*x+β)) volume := by
    have hi : IntegrableOn (fun x : ℝ => α*x+β) (Set.Ioc a m) volume :=
      ((continuousOn_id.const_mul α).add continuousOn_const).integrableOn_compact
        isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
    exact hi.integrable_indicator measurableSet_Ioc
  have hR : Integrable ((Set.Ioc m b).indicator (fun x : ℝ => α*x+β)) volume := by
    have hi : IntegrableOn (fun x : ℝ => α*x+β) (Set.Ioc m b) volume :=
      ((continuousOn_id.const_mul α).add continuousOn_const).integrableOn_compact
        isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
    exact hi.integrable_indicator measurableSet_Ioc
  have hdis : Disjoint (Set.Ioc m b) (Set.Ioc a m) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge (Set.mem_Ioc.mp hy).2) (Set.mem_Ioc.mp hx).1
  have hAE : (fun x => (α*x+β) * realDyadicHaar r c x) =ᵐ[volume]
      fun x => (Set.Ioc m b).indicator (fun x : ℝ => α*x+β) x -
        (Set.Ioc a m).indicator (fun x : ℝ => α*x+β) x := by
    filter_upwards [criticalIocHaar_ae_eq_real r c] with x hx
    rw [← hx]
    unfold discrepancyIocDyadicHaar
    simp only [Set.indicator_apply]
    by_cases hr : x ∈ Set.Ioc m b
    · by_cases hl : x ∈ Set.Ioc a m
      · exact (Set.disjoint_left.mp hdis hr hl).elim
      · simp [hr, hl, a, m, b]
    · by_cases hl : x ∈ Set.Ioc a m <;> simp [hr, hl, a, m, b]
  exact (hR.sub hL).congr hAE.symm

end HaarQuarter

namespace HaarQuarter

private theorem tent_eq_rising_branch {a m b x : ℝ} (hx : x ∈ Set.Ioc a m) :
    integratedHaarTent a m b x = x-a := by
  unfold integratedHaarTent
  have hnot : x ∉ Set.Ioc m b := by
    intro h
    exact (not_lt_of_ge (Set.mem_Ioc.mp hx).2) (Set.mem_Ioc.mp h).1
  simp [Set.indicator_apply, Set.mem_Ioc, hx, hnot]

private theorem tent_eq_falling_branch {a m b x : ℝ} (hx : x ∈ Set.Ioc m b) :
    integratedHaarTent a m b x = b-x := by
  unfold integratedHaarTent
  have hnot : x ∉ Set.Ioc a m := by
    intro h
    exact (not_lt_of_ge (Set.mem_Ioc.mp h).2) (Set.mem_Ioc.mp hx).1
  simp [Set.indicator_apply, Set.mem_Ioc, hx, hnot]

end HaarQuarter

namespace HaarQuarter

private theorem tent_times_leftChild_ae (r c : ℕ) :
    (fun x => integratedHaarTent (realDyadicLeft r c) (realDyadicMid r c)
        (realDyadicRight r c) x * realDyadicHaar (r+1) (2*c) x) =ᵐ[volume]
      (fun x => (x-realDyadicLeft r c) * realDyadicHaar (r+1) (2*c) x) := by
  have hleft : realDyadicLeft (r+1) (2*c) = realDyadicLeft r c := by
    dsimp [realDyadicLeft]
    push_cast
    rw [pow_succ]
    ring
  have hright : realDyadicRight (r+1) (2*c) = realDyadicMid r c := by
    dsimp [realDyadicRight, realDyadicMid]
    push_cast
    rw [pow_succ]
    ring
  have hmid : realDyadicMid (r+1) (2*c) =
      (realDyadicLeft r c + realDyadicMid r c)/2 := by
    dsimp [realDyadicMid, realDyadicLeft]
    push_cast
    rw [pow_succ]
    ring
  have hau : realDyadicLeft r c < realDyadicMid (r+1) (2*c) := by
    rw [hmid]
    have h : realDyadicLeft r c < realDyadicMid r c := by
      dsimp [realDyadicLeft, realDyadicMid]
      apply div_lt_div_of_pos_right
      · norm_num
      · positivity
    linarith
  have hum : realDyadicMid (r+1) (2*c) < realDyadicMid r c := by
    rw [hmid]
    have h : realDyadicLeft r c < realDyadicMid r c := by
      dsimp [realDyadicLeft, realDyadicMid]
      apply div_lt_div_of_pos_right
      · norm_num
      · positivity
    linarith
  filter_upwards [criticalIocHaar_ae_eq_real (r+1) (2*c)] with x hx
  rw [← hx]
  have hrepexpr : discrepancyIocDyadicHaar (r+1) (2*c) x =
      (Set.Ioc (realDyadicMid (r+1) (2*c)) (realDyadicMid r c)).indicator
          (fun _ : ℝ => (1:ℝ)) x -
        (Set.Ioc (realDyadicLeft r c) (realDyadicMid (r+1) (2*c))).indicator
          (fun _ : ℝ => (1:ℝ)) x := by
    rw [discrepancyIocDyadicHaar, hleft, hright]
    rfl
  rw [hrepexpr]
  by_cases hr : x ∈ Set.Ioc (realDyadicMid (r+1) (2*c)) (realDyadicMid r c)
  · have hparent : x ∈ Set.Ioc (realDyadicLeft r c) (realDyadicMid r c) :=
      ⟨lt_trans hau (Set.mem_Ioc.mp hr).1, (Set.mem_Ioc.mp hr).2⟩
    have hl : x ∉ Set.Ioc (realDyadicLeft r c) (realDyadicMid (r+1) (2*c)) := by
      intro hl
      have hle := (Set.mem_Ioc.mp hl).2
      have hlt := (Set.mem_Ioc.mp hr).1
      exact (not_lt_of_ge hle) hlt
    rw [tent_eq_rising_branch hparent]
  · by_cases hl : x ∈ Set.Ioc (realDyadicLeft r c) (realDyadicMid (r+1) (2*c))
    · have hparent : x ∈ Set.Ioc (realDyadicLeft r c) (realDyadicMid r c) :=
        ⟨(Set.mem_Ioc.mp hl).1, le_trans (Set.mem_Ioc.mp hl).2 (le_of_lt hum)⟩
      rw [tent_eq_rising_branch hparent]
    · simp [Set.indicator_apply, hr, hl]

end HaarQuarter

namespace HaarQuarter

private theorem tent_times_rightChild_ae (r c : ℕ) :
    (fun x => integratedHaarTent (realDyadicLeft r c) (realDyadicMid r c)
        (realDyadicRight r c) x * realDyadicHaar (r+1) (2*c+1) x) =ᵐ[volume]
      (fun x => (realDyadicRight r c-x) * realDyadicHaar (r+1) (2*c+1) x) := by
  have hleft : realDyadicLeft (r+1) (2*c+1) = realDyadicMid r c := by
    dsimp [realDyadicLeft, realDyadicMid]
    push_cast
    rw [pow_succ]
    ring
  have hright : realDyadicRight (r+1) (2*c+1) = realDyadicRight r c := by
    dsimp [realDyadicRight]
    push_cast
    rw [pow_succ]
    ring
  have hmid : realDyadicMid (r+1) (2*c+1) =
      (realDyadicMid r c + realDyadicRight r c)/2 := by
    dsimp [realDyadicMid, realDyadicRight]
    push_cast
    rw [pow_succ]
    ring
  have hmb : realDyadicMid r c < realDyadicRight r c := by
    dsimp [realDyadicMid, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have huv : realDyadicMid r c < realDyadicMid (r+1) (2*c+1) := by
    rw [hmid]
    linarith
  have hvb : realDyadicMid (r+1) (2*c+1) < realDyadicRight r c := by
    rw [hmid]
    linarith
  filter_upwards [criticalIocHaar_ae_eq_real (r+1) (2*c+1)] with x hx
  rw [← hx]
  have hrepexpr : discrepancyIocDyadicHaar (r+1) (2*c+1) x =
      (Set.Ioc (realDyadicMid (r+1) (2*c+1)) (realDyadicRight r c)).indicator
          (fun _ : ℝ => (1:ℝ)) x -
        (Set.Ioc (realDyadicMid r c) (realDyadicMid (r+1) (2*c+1))).indicator
          (fun _ : ℝ => (1:ℝ)) x := by
    rw [discrepancyIocDyadicHaar, hleft, hright]
    rfl
  rw [hrepexpr]
  by_cases hr : x ∈ Set.Ioc (realDyadicMid (r+1) (2*c+1)) (realDyadicRight r c)
  · have hparent : x ∈ Set.Ioc (realDyadicMid r c) (realDyadicRight r c) :=
      ⟨lt_trans huv (Set.mem_Ioc.mp hr).1, (Set.mem_Ioc.mp hr).2⟩
    have hl : x ∉ Set.Ioc (realDyadicMid r c) (realDyadicMid (r+1) (2*c+1)) := by
      intro hl
      exact (not_lt_of_ge (Set.mem_Ioc.mp hl).2) (Set.mem_Ioc.mp hr).1
    rw [tent_eq_falling_branch hparent]
  · by_cases hl : x ∈ Set.Ioc (realDyadicMid r c) (realDyadicMid (r+1) (2*c+1))
    · have hparent : x ∈ Set.Ioc (realDyadicMid r c) (realDyadicRight r c) :=
        ⟨(Set.mem_Ioc.mp hl).1, le_trans (Set.mem_Ioc.mp hl).2 (le_of_lt hvb)⟩
      rw [tent_eq_falling_branch hparent]
    · simp [Set.indicator_apply, hr, hl]

end HaarQuarter

namespace HaarQuarter

private theorem rightAffineHaar_integral (r c : ℕ) :
    ∫ x, (realDyadicRight r c - x) * realDyadicHaar r c x ∂volume =
      -((realDyadicRight r c - realDyadicLeft r c)^2/4) := by
  let d := realDyadicLeft r c
  have hconst := affine_realDyadicHaar_integrable r c 0 (realDyadicRight r c-d)
  have hmoment := affine_realDyadicHaar_integrable r c 1 (-d)
  have hsum : (fun x => (realDyadicRight r c-x)*realDyadicHaar r c x) =
      (fun x => (realDyadicRight r c-d)*realDyadicHaar r c x -
        (x-d)*realDyadicHaar r c x) := by
    funext x
    dsimp [d]
    ring
  rw [hsum]
  have hconst' : Integrable (fun x => (realDyadicRight r c-d)*realDyadicHaar r c x) := by
    simpa using hconst
  have hmoment' : Integrable (fun x => (x-d)*realDyadicHaar r c x) := by
    simpa [sub_eq_add_neg, one_mul] using hmoment
  rw [integral_sub hconst' hmoment', integral_const_mul,
    realDyadicHaar_integral_zero, realDyadicHaar_firstMoment]
  ring

private theorem parent_tent_left_child_integral (r c : ℕ) :
    ∫ x, integratedHaarTent (realDyadicLeft r c) (realDyadicMid r c)
        (realDyadicRight r c) x * realDyadicHaar (r+1) (2*c) x ∂volume =
      (realDyadicMid r c-realDyadicLeft r c)^2/4 := by
  rw [integral_congr_ae (tent_times_leftChild_ae r c)]
  have hleft : realDyadicLeft (r+1) (2*c) = realDyadicLeft r c := by
    dsimp [realDyadicLeft]
    push_cast
    rw [pow_succ]
    ring
  have hright : realDyadicRight (r+1) (2*c) = realDyadicMid r c := by
    dsimp [realDyadicRight, realDyadicMid]
    push_cast
    rw [pow_succ]
    ring
  simpa [hleft, hright] using realDyadicHaar_firstMoment (r+1) (2*c)

private theorem parent_tent_right_child_integral (r c : ℕ) :
    ∫ x, integratedHaarTent (realDyadicLeft r c) (realDyadicMid r c)
        (realDyadicRight r c) x * realDyadicHaar (r+1) (2*c+1) x ∂volume =
      -((realDyadicRight r c-realDyadicMid r c)^2/4) := by
  rw [integral_congr_ae (tent_times_rightChild_ae r c)]
  have hleft : realDyadicLeft (r+1) (2*c+1) = realDyadicMid r c := by
    dsimp [realDyadicLeft, realDyadicMid]
    push_cast
    rw [pow_succ]
    ring
  have hright : realDyadicRight (r+1) (2*c+1) = realDyadicRight r c := by
    dsimp [realDyadicRight]
    push_cast
    rw [pow_succ]
    ring
  simpa [hleft, hright] using rightAffineHaar_integral (r+1) (2*c+1)

end HaarQuarter

namespace HaarQuarter

theorem brownianParentTent_criticalE_integral (r c : ℕ) :
    ∫ x, integratedHaarTent (realDyadicLeft r c) (realDyadicMid r c)
        (realDyadicRight r c) x * criticalDyadicE r c x ∂volume =
      (realDyadicRight r c-realDyadicLeft r c) *
        Real.sqrt (realDyadicRight r c-realDyadicLeft r c) / 8 := by
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  let L := b-a
  have hL : 0 < L := by
    dsimp [L,a,b,realDyadicLeft,realDyadicRight]
    apply sub_pos.mpr
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid : m=(a+b)/2 := by
    dsimp [a,m,b,realDyadicLeft,realDyadicMid,realDyadicRight]
    field_simp
    ring
  have hleftAE := tent_times_leftChild_ae r c
  have hrightAE := tent_times_rightChild_ae r c
  have hleftI : Integrable (fun x => integratedHaarTent a m b x *
      realDyadicHaar (r+1) (2*c) x) volume := by
    have h := affine_realDyadicHaar_integrable (r+1) (2*c) 1 (-a)
    have heq : (fun x => (x-a)*realDyadicHaar (r+1) (2*c) x) =
        (fun x => (1*x+(-a))*realDyadicHaar (r+1) (2*c) x) := by
      funext x
      ring
    exact (h.congr (Filter.Eventually.of_forall (fun x => (congrFun heq x).symm))).congr hleftAE.symm
  have hrightI : Integrable (fun x => integratedHaarTent a m b x *
      realDyadicHaar (r+1) (2*c+1) x) volume := by
    have h := affine_realDyadicHaar_integrable (r+1) (2*c+1) (-1) b
    have heq : (fun x => (b-x)*realDyadicHaar (r+1) (2*c+1) x) =
        (fun x => ((-1)*x+b)*realDyadicHaar (r+1) (2*c+1) x) := by
      funext x
      ring
    exact (h.congr (Filter.Eventually.of_forall (fun x => (congrFun heq x).symm))).congr hrightAE.symm
  have hpoint : (fun x => integratedHaarTent a m b x * criticalDyadicE r c x) =
      (fun x => (integratedHaarTent a m b x * realDyadicHaar (r+1) (2*c) x -
        integratedHaarTent a m b x * realDyadicHaar (r+1) (2*c+1) x) /
          Real.sqrt L) := by
    funext x
    dsimp [criticalDyadicE, L, a, b]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hpoint x)), integral_div,
    integral_sub hleftI hrightI, parent_tent_left_child_integral,
    parent_tent_right_child_integral]
  have hsqrt : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (le_of_lt hL)
  have hmid' : realDyadicMid r c =
      (realDyadicLeft r c + realDyadicRight r c)/2 := by
    simpa [a,m,b] using hmid
  rw [hmid']
  change Real.sqrt (realDyadicRight r c-realDyadicLeft r c) ≠ 0 at hsqrt
  have hsq' : Real.sqrt (realDyadicRight r c-realDyadicLeft r c)^2 =
      realDyadicRight r c-realDyadicLeft r c := by
    exact Real.sq_sqrt (le_of_lt hL)
  field_simp [hsqrt]
  nlinarith [hsq']

end HaarQuarter

namespace HaarQuarter

theorem brownianTentTensor_criticalETensor_inner_eq_prod {d : ℕ}
    (profile cells : Fin d → ℕ) :
    ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profile cells x *
        criticalDyadicETensor profile cells x ∂(Measure.pi fun _ : Fin d => volume) =
      ∏ i, ∫ x : ℝ,
        integratedHaarTent (realDyadicLeft (profile i) (cells i))
          (realDyadicMid (profile i) (cells i))
          (realDyadicRight (profile i) (cells i)) x *
            criticalDyadicE (profile i) (cells i) x ∂volume := by
  have hpoint : (fun x : Fin d → ℝ => tensorIntegratedTentDyadic profile cells x *
      criticalDyadicETensor profile cells x) = fun x => ∏ i,
        (integratedHaarTent (realDyadicLeft (profile i) (cells i))
          (realDyadicMid (profile i) (cells i))
          (realDyadicRight (profile i) (cells i)) (x i) *
            criticalDyadicE (profile i) (cells i) (x i)) := by
    funext x
    simp only [tensorIntegratedTentDyadic, criticalDyadicETensor]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [integratedTentDyadicLeft, integratedTentDyadicRight,
      realDyadicLeft, realDyadicRight, realDyadicMid]
    congr 2
    field_simp
    ring
  rw [hpoint]
  exact integral_fintype_prod_eq_prod
    (f := fun i x =>
      integratedHaarTent (realDyadicLeft (profile i) (cells i))
        (realDyadicMid (profile i) (cells i))
        (realDyadicRight (profile i) (cells i)) x *
          criticalDyadicE (profile i) (cells i) x)
    (μ := fun _ : Fin d => (volume : Measure ℝ))

theorem brownianTentTensor_criticalETensor_diagonal {d : ℕ}
    (profile cells : Fin d → ℕ) :
    ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profile cells x *
        criticalDyadicETensor profile cells x ∂(Measure.pi fun _ : Fin d => volume) =
      ∏ i, ((realDyadicRight (profile i) (cells i) -
        realDyadicLeft (profile i) (cells i)) *
          Real.sqrt (realDyadicRight (profile i) (cells i) -
            realDyadicLeft (profile i) (cells i)) / 8) := by
  rw [brownianTentTensor_criticalETensor_inner_eq_prod]
  simp_rw [brownianParentTent_criticalE_integral]

private theorem affine_realDyadicHaar_integral (r c : ℕ) (α β : ℝ) :
    ∫ x, (α*x+β) * realDyadicHaar r c x ∂volume =
      α * ((realDyadicRight r c-realDyadicLeft r c)^2/4) := by
  let a := realDyadicLeft r c
  have h1 := affine_realDyadicHaar_integrable r c 1 (-a)
  have h0 := affine_realDyadicHaar_integrable r c 0 1
  have hpoint : (fun x => (α*x+β)*realDyadicHaar r c x) =
      (fun x => α*((x-a)*realDyadicHaar r c x) +
        (α*a+β)*realDyadicHaar r c x) := by
    funext x
    dsimp [a]
    ring
  have h1' : Integrable (fun x => (x-a)*realDyadicHaar r c x) := by
    simpa [sub_eq_add_neg, one_mul] using h1
  have h0' : Integrable (fun x => realDyadicHaar r c x) := by
    simpa using h0
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hpoint x)),
    integral_add (h1'.const_mul α) (h0'.const_mul (α*a+β)),
    integral_const_mul, integral_const_mul,
    realDyadicHaar_firstMoment, realDyadicHaar_integral_zero]
  dsimp [a]
  ring

private theorem criticalDyadicE_affine_integral_zero (r c : ℕ) (α β : ℝ) :
    ∫ x, (α*x+β) * criticalDyadicE r c x ∂volume = 0 := by
  let L := realDyadicRight r c-realDyadicLeft r c
  have hL : 0 < L := by
    dsimp [L,realDyadicRight,realDyadicLeft]
    apply sub_pos.mpr
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hleft : Integrable (fun x => (α*x+β)*realDyadicHaar (r+1) (2*c) x) volume :=
    affine_realDyadicHaar_integrable (r+1) (2*c) α β
  have hright : Integrable (fun x => (α*x+β)*realDyadicHaar (r+1) (2*c+1) x) volume :=
    affine_realDyadicHaar_integrable (r+1) (2*c+1) α β
  have hpoint : (fun x => (α*x+β)*criticalDyadicE r c x) =
      (fun x => ((α*x+β)*realDyadicHaar (r+1) (2*c) x -
        (α*x+β)*realDyadicHaar (r+1) (2*c+1) x) / Real.sqrt L) := by
    funext x
    dsimp [criticalDyadicE,L]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hpoint x)),
    integral_div, integral_sub hleft hright,
    affine_realDyadicHaar_integral, affine_realDyadicHaar_integral]
  have hlen : realDyadicRight (r+1) (2*c)-realDyadicLeft (r+1) (2*c) =
      realDyadicRight (r+1) (2*c+1)-realDyadicLeft (r+1) (2*c+1) := by
    dsimp [realDyadicRight,realDyadicLeft]
    push_cast
    ring
  rw [hlen]
  simp [L, Real.sqrt_ne_zero'.mpr hL]

private theorem criticalE_zero_outside_parent {r c : ℕ} {x : ℝ}
    (hx : x ∉ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)) :
    criticalDyadicE r c x = 0 := by
  have hs := criticalDyadicE_sq r c x
  rw [if_neg hx] at hs
  exact (sq_eq_zero_iff).1 hs

private theorem tent_eq_rising_on_Icc {a m b x : ℝ} (ham : a ≤ m)
    (hx : x ∈ Set.Icc a m) :
    integratedHaarTent a m b x = x-a := by
  by_cases hxa : x=a
  · subst x
    unfold integratedHaarTent
    have h1 : a ∉ Set.Ioc a m := by simp
    have h2 : a ∉ Set.Ioc m b := by
      intro h
      exact (not_lt_of_ge ham) h.1
    simp [h1, h2]
  · apply tent_eq_rising_branch
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩

private theorem parent_tent_criticalE_inner_zero_of_coarser
    {q r c d : ℕ} (hqr : q < r) :
    ∫ x, integratedHaarTent (realDyadicLeft q c) (realDyadicMid q c)
        (realDyadicRight q c) x * criticalDyadicE r d x ∂volume = 0 := by
  let a := realDyadicLeft q c
  let m := realDyadicMid q c
  let b := realDyadicRight q c
  let u := realDyadicLeft r d
  let v := realDyadicRight r d
  have ham : a < m := by
    dsimp [a,m,realDyadicLeft,realDyadicMid]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmb : m < b := by
    dsimp [m,b,realDyadicMid,realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  obtain hbefore | hleft | hright | hafter := critical_fine_cell_position hqr
  · have hprod : ∀ x, integratedHaarTent a m b x * criticalDyadicE r d x = 0 := by
      intro x
      by_cases hf : x ∈ Set.Ico u v
      · have hout : x ∉ Set.Ioo a b := by
          intro hx
          exact (not_lt_of_ge (le_trans (le_of_lt hf.2) hbefore)) hx.1
        rw [integratedHaarTent_eq_zero_of_not_mem_open ham hmb hout]
        simp
      · rw [criticalE_zero_outside_parent hf]
        simp
    calc
      ∫ x, integratedHaarTent a m b x * criticalDyadicE r d x ∂volume =
          ∫ x, (0:ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp

  · rcases hleft with ⟨hL,hM⟩
    have hsub : Set.Ico u v ⊆ Set.Ico a m := by
      intro x hx
      exact ⟨le_trans hL hx.1, lt_of_lt_of_le hx.2 hM⟩
    have hprod : ∀ x, integratedHaarTent a m b x * criticalDyadicE r d x =
        (x-a)*criticalDyadicE r d x := by
      intro x
      by_cases hf : x ∈ Set.Ico u v
      · have hxmem := Set.mem_Ico.mp (hsub hf)
        rw [tent_eq_rising_on_Icc (le_of_lt ham) ⟨hxmem.1, le_of_lt hxmem.2⟩]
      · rw [criticalE_zero_outside_parent hf]
        simp
    calc
      ∫ x, integratedHaarTent a m b x * criticalDyadicE r d x ∂volume =
          ∫ x, (x-a)*criticalDyadicE r d x ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simpa [one_mul, sub_eq_add_neg] using
        criticalDyadicE_affine_integral_zero r d 1 (-a)
  · rcases hright with ⟨hM,hR⟩
    have hsub : Set.Ico u v ⊆ Set.Ico m b := by
      intro x hx
      exact ⟨le_trans hM hx.1, lt_of_lt_of_le hx.2 hR⟩
    have hprod : ∀ x, x ≠ m → integratedHaarTent a m b x * criticalDyadicE r d x =
        (b-x)*criticalDyadicE r d x := by
      intro x hxm
      by_cases hf : x ∈ Set.Ico u v
      · have hxmem := Set.mem_Ico.mp (hsub hf)
        have hlt : m < x := lt_of_le_of_ne hxmem.1 (Ne.symm hxm)
        have hxicc : x ∈ Set.Ioc m b := ⟨hlt, le_of_lt hxmem.2⟩
        rw [tent_eq_falling_branch hxicc]
      · rw [criticalE_zero_outside_parent hf]
        simp
    calc
      ∫ x, integratedHaarTent a m b x * criticalDyadicE r d x ∂volume =
          ∫ x, (b-x)*criticalDyadicE r d x ∂volume := by
            apply integral_congr_ae
            have hnull : volume ({m} : Set ℝ) = 0 := measure_singleton m
            apply (ae_iff).2
            apply measure_mono_null (t := ({m} : Set ℝ))
            · intro x hx
              change integratedHaarTent a m b x * criticalDyadicE r d x ≠
                (b-x)*criticalDyadicE r d x at hx
              by_contra hxm
              exact hx (hprod x hxm)
            · exact hnull
      _ = 0 := by simpa [sub_eq_add_neg, add_comm] using
        criticalDyadicE_affine_integral_zero r d (-1) b
  · have hprod : ∀ x, integratedHaarTent a m b x * criticalDyadicE r d x = 0 := by
      intro x
      by_cases hf : x ∈ Set.Ico u v
      · have hout : x ∉ Set.Ioo a b := by
          intro hx
          exact (not_lt_of_ge (le_trans hafter hf.1)) hx.2
        rw [integratedHaarTent_eq_zero_of_not_mem_open ham hmb hout]
        simp
      · rw [criticalE_zero_outside_parent hf]
        simp
    calc
      ∫ x, integratedHaarTent a m b x * criticalDyadicE r d x ∂volume =
          ∫ x, (0:ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp

private theorem dyadicCell_right_le_left_of_lt {r c d : ℕ} (hcd : c < d) :
    realDyadicRight r c ≤ realDyadicLeft r d := by
  have hn : (c : ℝ) + 1 ≤ d := by exact_mod_cast Nat.succ_le_iff.mpr hcd
  dsimp [realDyadicRight, realDyadicLeft]
  exact div_le_div_of_nonneg_right hn (by positivity)

private theorem parent_tent_criticalE_inner_zero_of_distinct_cells
    {r c d : ℕ} (hcd : c ≠ d) :
    ∫ x, integratedHaarTent (realDyadicLeft r c) (realDyadicMid r c)
        (realDyadicRight r c) x * criticalDyadicE r d x ∂volume = 0 := by
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  let u := realDyadicLeft r d
  let v := realDyadicRight r d
  have ham : a < m := by
    dsimp [a,m,realDyadicLeft,realDyadicMid]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmb : m < b := by
    dsimp [m,b,realDyadicMid,realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hdisj : b ≤ u ∨ v ≤ a := by
    rcases lt_or_gt_of_ne hcd with h | h
    · exact Or.inl (by dsimp [b,u]; exact dyadicCell_right_le_left_of_lt h)
    · exact Or.inr (by dsimp [v,a]; exact dyadicCell_right_le_left_of_lt h)
  have hprod : ∀ x,
      integratedHaarTent a m b x * criticalDyadicE r d x = 0 := by
    intro x
    by_cases hx : x ∈ Set.Ico a b
    · have hnot : x ∉ Set.Ico u v := by
        rcases hdisj with h | h
        · intro hxv
          exact (not_lt_of_ge hxv.1) (lt_of_lt_of_le hx.2 h)
        · intro hxv
          exact (not_lt_of_ge (le_trans h hx.1)) hxv.2
      rw [criticalE_zero_outside_parent hnot]
      simp
    · have hout : x ∉ Set.Ioo a b := by
        intro hxopen
        exact hx ⟨le_of_lt hxopen.1, hxopen.2⟩
      rw [integratedHaarTent_eq_zero_of_not_mem_open ham hmb hout]
      simp
  calc
    ∫ x, integratedHaarTent a m b x * criticalDyadicE r d x ∂volume =
        ∫ x, (0:ℝ) ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hprod
    _ = 0 := by simp

/-! A tensor product of a tent and a critical function factors into its
one-dimensional inner products, also when their scale profiles differ. -/
theorem brownianTentTensor_criticalETensor_inner_eq_prod_general {d : ℕ}
    (profile₁ cells₁ profile₂ cells₂ : Fin d → ℕ) :
    ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profile₁ cells₁ x *
        criticalDyadicETensor profile₂ cells₂ x ∂(Measure.pi fun _ : Fin d => volume) =
      ∏ i, ∫ x,
        integratedHaarTent (realDyadicLeft (profile₁ i) (cells₁ i))
          (realDyadicMid (profile₁ i) (cells₁ i))
          (realDyadicRight (profile₁ i) (cells₁ i)) x *
            criticalDyadicE (profile₂ i) (cells₂ i) x ∂volume := by
  have hpoint : (fun x : Fin d → ℝ => tensorIntegratedTentDyadic profile₁ cells₁ x *
      criticalDyadicETensor profile₂ cells₂ x) = fun x => ∏ i,
        (integratedHaarTent (realDyadicLeft (profile₁ i) (cells₁ i))
          (realDyadicMid (profile₁ i) (cells₁ i))
          (realDyadicRight (profile₁ i) (cells₁ i)) (x i) *
            criticalDyadicE (profile₂ i) (cells₂ i) (x i)) := by
    funext x
    simp only [tensorIntegratedTentDyadic, criticalDyadicETensor]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [integratedTentDyadicLeft, integratedTentDyadicRight,
      realDyadicLeft, realDyadicRight, realDyadicMid]
    congr 2
    field_simp
    ring
  rw [hpoint]
  exact integral_fintype_prod_eq_prod
    (f := fun i x =>
      integratedHaarTent (realDyadicLeft (profile₁ i) (cells₁ i))
        (realDyadicMid (profile₁ i) (cells₁ i))
        (realDyadicRight (profile₁ i) (cells₁ i)) x *
          criticalDyadicE (profile₂ i) (cells₂ i) x)
    (μ := fun _ : Fin d => (volume : Measure ℝ))

/-- A tensor inner product vanishes as soon as the tent is coarser in one
coordinate.  This is the off-diagonal mechanism used when two critical
profiles have equal total depth but are not equal. -/
theorem brownianTentTensor_criticalETensor_inner_zero_of_coarser_coordinate
    {d : ℕ} (profile₁ cells₁ profile₂ cells₂ : Fin d → ℕ) (i : Fin d)
    (h : profile₁ i < profile₂ i) :
    ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profile₁ cells₁ x *
        criticalDyadicETensor profile₂ cells₂ x ∂(Measure.pi fun _ : Fin d => volume) = 0 := by
  rw [brownianTentTensor_criticalETensor_inner_eq_prod_general]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact parent_tent_criticalE_inner_zero_of_coarser h

/-- At a fixed profile, different dyadic cells have disjoint support in at
least one coordinate, so the tensor cross-Gram is zero. -/
theorem brownianTentTensor_criticalETensor_inner_zero_of_same_profile_cell_mismatch
    {d : ℕ} (profile cells₁ cells₂ : Fin d → ℕ) (h : cells₁ ≠ cells₂) :
    ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profile cells₁ x *
        criticalDyadicETensor profile cells₂ x ∂(Measure.pi fun _ : Fin d => volume) = 0 := by
  have hex : ∃ i, cells₁ i ≠ cells₂ i := by
    by_contra hnone
    push_neg at hnone
    apply h
    funext i
    exact hnone i
  obtain ⟨i, hi⟩ := hex
  rw [brownianTentTensor_criticalETensor_inner_eq_prod_general]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact parent_tent_criticalE_inner_zero_of_distinct_cells hi

private theorem exists_lt_of_eq_sum_and_ne {d : ℕ}
    (profile₁ profile₂ : Fin d → ℕ)
    (hsum : (∑ i, profile₁ i) = ∑ i, profile₂ i)
    (hne : profile₁ ≠ profile₂) : ∃ i, profile₁ i < profile₂ i := by
  by_contra h
  push_neg at h
  have hle : ∀ i ∈ Finset.univ, profile₂ i ≤ profile₁ i := by
    intro i hi
    exact h i
  have hpoint : ∀ i ∈ Finset.univ, profile₂ i = profile₁ i := by
    have hsum' : (∑ i, profile₂ i) = ∑ i, profile₁ i := hsum.symm
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum'
  apply hne
  funext i
  exact (hpoint i (Finset.mem_univ i)).symm

/-- Distinct equal-total-depth profiles have a coarser coordinate, hence
their tent/critical tensor cross-Gram vanishes. -/
theorem brownianTentTensor_criticalETensor_inner_zero_of_equal_total_ne_profile
    {d : ℕ} (profile₁ cells₁ profile₂ cells₂ : Fin d → ℕ)
    (hsum : (∑ i, profile₁ i) = ∑ i, profile₂ i)
    (hne : profile₁ ≠ profile₂) :
    ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profile₁ cells₁ x *
        criticalDyadicETensor profile₂ cells₂ x ∂(Measure.pi fun _ : Fin d => volume) = 0 := by
  obtain ⟨i, hi⟩ := exists_lt_of_eq_sum_and_ne profile₁ profile₂ hsum hne
  exact brownianTentTensor_criticalETensor_inner_zero_of_coarser_coordinate
    profile₁ cells₁ profile₂ cells₂ i hi

end HaarQuarter
