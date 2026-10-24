import BrownianSharp.AlignmentFractionalPastTailTaylor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory Set Filter
open BrownianSharp.AlignmentFractionalPastTailTaylor
open BrownianSharp.AlignmentFractionalPastTail
open scoped Topology

namespace BrownianSharp.AlignmentFractionalPastTailL2Approx

open Polynomial

theorem descPochhammer_abs_div_factorial_le_one {p : ℝ}
    (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2) (m : ℕ) :
    |(descPochhammer ℝ m).eval p| / (m.factorial:ℝ) ≤ 1 := by
  rw [descPochhammer_eval_eq_prod_range, Finset.abs_prod]
  have hprod :
      (∏ j ∈ Finset.range m, |p-(j:ℝ)|) ≤
        ∏ j ∈ Finset.range m, ((j:ℝ)+1) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
      exact abs_nonneg _
    · intro j hj
      have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
      have hlow : -((j:ℝ)+1) ≤ p-(j:ℝ) := by linarith
      have hhigh : p-(j:ℝ) ≤ (j:ℝ)+1 := by linarith
      exact abs_le.mpr ⟨hlow, hhigh⟩
  have hfactorial :
      (∏ j ∈ Finset.range m, ((j:ℝ)+1)) = (m.factorial:ℝ) := by
    norm_cast
    exact Finset.prod_range_add_one_eq_factorial m
  rw [hfactorial] at hprod
  exact (div_le_one (by positivity)).2 hprod

theorem pastTailTaylor_scalar_bound {p a : ℝ} {m : ℕ}
    (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2) (hm : 0 < m)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) * (a/2)^m *
      (-a^(2*(p-m)+1)/(2*(p-m)+1))^(1/2:ℝ) ≤
      (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m := by
  have hmcast : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hcoeff := descPochhammer_abs_div_factorial_le_one hp0 hp1 m
  have hden : 0 < 1-2*p := by linarith
  let q : ℝ := p-(m:ℝ)
  have hq : q < -(1/2:ℝ) := by dsimp [q]; linarith
  have hD : 1-2*p ≤ -(2*q+1) := by dsimp [q]; linarith
  have hDpos : 0 < -(2*q+1) := by linarith
  have hnum : 0 ≤ a^(2*q+1) := Real.rpow_nonneg ha.le _
  have hrad : -a^(2*q+1)/(2*q+1) ≤ a^(2*q+1)/(1-2*p) := by
    have hdenq : 2*q+1 ≠ 0 := ne_of_lt (by linarith)
    have hrewrite : -a^(2*q+1)/(2*q+1) = a^(2*q+1)/(-(2*q+1)) := by
      field_simp [hdenq, ne_of_gt hDpos]
    rw [hrewrite]
    exact div_le_div_of_nonneg_left hnum hden hD
  have hradnonneg : 0 ≤ -a^(2*q+1)/(2*q+1) := by
    rw [show -a^(2*q+1)/(2*q+1) = a^(2*q+1)/(-(2*q+1)) by
      field_simp [ne_of_lt (by linarith : 2*q+1 < 0), ne_of_gt hDpos]]
    exact div_nonneg hnum hDpos.le
  have hradpow := Real.rpow_le_rpow hradnonneg hrad
    (by norm_num : (0:ℝ) ≤ (1/2:ℝ))
  have hradpow' :
      (-a^(2*q+1)/(2*q+1))^(1/2:ℝ) ≤
        a^(q+(1/2:ℝ)) * (1-2*p)^(-1/2:ℝ) := by
    calc
      _ ≤ (a^(2*q+1)/(1-2*p))^(1/2:ℝ) := hradpow
      _ = a^(q+(1/2:ℝ)) * (1-2*p)^(-1/2:ℝ) := by
        rw [Real.div_rpow (Real.rpow_nonneg ha.le _) hden.le]
        rw [← Real.rpow_mul ha.le]
        rw [show (2*q+1)*(1/2:ℝ) = q+(1/2:ℝ) by ring]
        rw [div_eq_mul_inv, ← Real.inv_rpow hden.le, ← Real.rpow_neg_eq_inv_rpow]
        norm_num
  have hprod : (a/2)^m * a^(q+(1/2:ℝ)) =
      (1/2:ℝ)^m * a^(p+(1/2:ℝ)) := by
    calc
      _ = a^m * (1/2:ℝ)^m * a^(q+(1/2:ℝ)) := by
        rw [show a/2 = a*(1/2:ℝ) by ring, mul_pow]
      _ = (1/2:ℝ)^m * (a^(m:ℝ) * a^(q+(1/2:ℝ))) := by
        rw [← Real.rpow_natCast a m]
        ring
      _ = (1/2:ℝ)^m * a^(p+(1/2:ℝ)) := by
        rw [← Real.rpow_add ha]
        congr 1
        dsimp [q]
        ring
  have haPow : a^(p+(1/2:ℝ)) ≤ 1 :=
    Real.rpow_le_one ha.le ha1 (by linarith)
  have hhalf : 0 ≤ (1/2:ℝ) := by norm_num
  have hcoefPow : 0 ≤ (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m :=
    mul_nonneg (Real.rpow_nonneg hden.le (-1/2:ℝ)) (pow_nonneg hhalf m)
  have hscalar : (a/2)^m * (-a^(2*q+1)/(2*q+1))^(1/2:ℝ) ≤
      (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m := by
    calc
      _ ≤ (a/2)^m * (a^(q+(1/2:ℝ)) * (1-2*p)^(-1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left hradpow' (by positivity)
      _ = (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m * a^(p+(1/2:ℝ)) := by
        rw [mul_assoc, ← hprod]
        ring
      _ ≤ (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m := by
        calc
          _ ≤ ((1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m) * 1 :=
            mul_le_mul_of_nonneg_left haPow hcoefPow
          _ = _ := by ring
  calc
    _ = (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        ((a/2)^m * (-a^(2*(p-m)+1)/(2*(p-m)+1))^(1/2:ℝ)) := by ring
    _ ≤ 1 * ((a/2)^m * (-a^(2*(p-m)+1)/(2*(p-m)+1))^(1/2:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ _ := by simpa [q, one_mul] using hscalar

/-- Exact integral of a shifted negative power on the positive half-line. -/
theorem integral_add_rpow_Ioi {q a : ℝ} (hq : q < -1) (ha : 0 < a) :
    ∫ x : ℝ in Ioi 0, (x + a) ^ q = -a ^ (q + 1) / (q + 1) := by
  have hd : ∀ x ∈ Ici (0:ℝ),
      HasDerivAt (fun y : ℝ => (y + a) ^ (q + 1) / (q + 1)) ((x+a)^q) x := by
    intro x hx
    have hpos : 0 < x+a := by linarith [mem_Ici.mp hx]
    convert! (hasDerivAt_id x |>.add_const a).rpow_const (Or.inl hpos.ne') |>.div_const (q+1) using 1
    · simp [show q+1 ≠ 0 by linarith]
  have hi : IntegrableOn (fun x : ℝ => (x+a)^q) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt hq (by linarith)
  have hpow : Filter.Tendsto (fun y : ℝ => y ^ (q+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -(q+1)))
  have hshift : Filter.Tendsto (fun x : ℝ => (x+a)^(q+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      hpow.comp (tendsto_atTop_add_const_right _ a tendsto_id)
  have ht : Filter.Tendsto (fun x : ℝ => (x+a)^(q+1)/(q+1)) atTop
      (𝓝 (0/(q+1))) := hshift.div_const _
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht]
  ring_nf

/-- Algebraic fixed-coefficient version of the local Taylor polynomial. -/
def pastTailTaylorPoly (p : ℝ) (m : ℕ) (b t x : ℝ) : ℝ :=
  (∑ k ∈ Finset.range m,
    ((k.factorial : ℝ)⁻¹ * (t-b)^k) *
      ((descPochhammer ℝ k).eval p * (x+b)^(p-k))) - x^p

/-- On a positive interval, the within-Taylor polynomial has the usual
power-function coefficients, hence depends measurably on the source variable. -/
theorem pastTailTaylorApprox_eq_poly {p : ℝ} {m : ℕ} {a b t x : ℝ}
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b)
    (htlo : a ≤ t) (hthi : t < b) (hx : 0 ≤ x) :
    pastTailTaylorApprox p m b t x = pastTailTaylorPoly p m b t x := by
  let s : Set ℝ := Set.Icc (x+t) (x+b)
  have hlt : x+t < x+b := by linarith
  have hbase : x+b ≠ 0 := by
    apply ne_of_gt
    linarith
  have hcontAt (k : ℕ) : ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun z : ℝ => z^p) (x+b) := by
    exact Real.contDiffAt_rpow_const (n:=k) (p:=p) (x:=x+b) (Or.inl hbase)
  have hderiv (k : ℕ) :
      iteratedDerivWithin k (fun z : ℝ => z^p) s (x+b) =
        (descPochhammer ℝ k).eval p * (x+b)^(p-k) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
      (hcontAt k) (by exact ⟨by linarith, le_rfl⟩)]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const p (x+b) k]
  have hs : Set.uIcc (x+b) (x+t) = s := by
    simp [s, Set.uIcc_of_ge (by linarith : x+t ≤ x+b)]
  rw [pastTailTaylorApprox, hs, taylor_within_apply]
  dsimp [pastTailTaylorPoly]
  have hsum :
      (∑ k ∈ Finset.range (m-1+1),
        ((k.factorial : ℝ)⁻¹ * ((x+t)-(x+b))^k) •
          iteratedDerivWithin k (fun z : ℝ => z^p) s (x+b)) =
      ∑ k ∈ Finset.range m,
        ((k.factorial : ℝ)⁻¹ * (t-b)^k) *
          ((descPochhammer ℝ k).eval p * (x+b)^(p-k)) := by
    rw [Nat.sub_add_cancel hm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hderiv k, smul_eq_mul]
    have hdiff : (x+t)-(x+b)=t-b := by ring
    rw [hdiff]
  simpa only [smul_eq_mul] using congrArg (fun z : ℝ => z - x^p) hsum

/-- At the right endpoint the Taylor polynomial is exact. -/
theorem pastTailTaylorApprox_eq_poly_endpoint {p : ℝ} {m : ℕ} {a b x : ℝ}
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b) (hx : 0 ≤ x) :
    pastTailTaylorApprox p m b b x = pastTailTaylorPoly p m b b x := by
  have hleft : pastTailTaylorApprox p m b b x = (x+b)^p-x^p := by
    simp [pastTailTaylorApprox, taylorWithinEval_self]
  have hsum :
      (∑ k ∈ Finset.range m,
        ((k.factorial : ℝ)⁻¹ * (b-b)^k) *
          ((descPochhammer ℝ k).eval p * (x+b)^(p-k))) =
        (((0:ℕ).factorial : ℝ)⁻¹ * (b-b)^0) *
          ((descPochhammer ℝ 0).eval p * (x+b)^(p-(0:ℕ))) := by
    apply Finset.sum_eq_single 0
    · intro k hk hk0
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hzero : (b-b)^k = 0 := by rw [sub_self]; exact zero_pow hkpos.ne'
      rw [hzero]
      ring
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hm)).elim
  have hterm0 :
      (((0:ℕ).factorial : ℝ)⁻¹ * (b-b)^0) *
          ((descPochhammer ℝ 0).eval p * (x+b)^(p-(0:ℕ))) = (x+b)^p := by
    simp
  rw [pastTailTaylorPoly, hleft, hsum]
  rw [hterm0]


/-- A shifted power with square-integrable tail belongs to `L²` on the
positive half-line. -/
theorem shifted_rpow_memLp_two {q a : ℝ} (hq : q < -(1/2 : ℝ)) (ha : 0 < a) :
    MemLp (fun x : ℝ => (x+a)^q) 2 (volume.restrict (Ioi 0)) := by
  have hcont : ContinuousOn (fun x : ℝ => (x+a)^q) (Ioi 0) := by
    apply (continuousOn_id.add continuousOn_const).rpow_const
    intro x hx
    have hx0 : 0 < x := by simpa using hx
    have hpos : 0 < x+a := add_pos hx0 ha
    exact Or.inl (ne_of_gt (by simpa using hpos))
  have hasm : AEStronglyMeasurable (fun x : ℝ => (x+a)^q)
      (volume.restrict (Ioi 0)) := hcont.aestronglyMeasurable measurableSet_Ioi
  rw [memLp_two_iff_integrable_sq hasm]
  have hi : IntegrableOn (fun x : ℝ => (x+a)^(2*q)) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (by linarith : 2*q < -1) (by linarith)
  have heq : (fun x : ℝ => ((x+a)^q)^2) =ᵐ[volume.restrict (Ioi 0)]
      (fun x => (x+a)^(2*q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := by simpa using hx
    have hpos : 0 < x+a := by linarith
    calc
      ((x+a)^q)^2 = (x+a)^q * (x+a)^q := by rw [pow_two]
      _ = (x+a)^(q+q) := (Real.rpow_add hpos _ _).symm
      _ = (x+a)^(2*q) := by congr 1 <;> ring
  exact hi.congr heq.symm

/-- The reflected tail profile belongs to `L²` on the positive half-line. -/
theorem pastTailPower_memLp_two {p t : ℝ} (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MemLp (fun x : ℝ => pastTailPower p t x) 2 (volume.restrict (Ioi 0)) := by
  let Q : ℝ → ℝ := fun x => (pastTailPower p t x)^2
  have hp0' : -1/2 < p := by norm_num at hp0 ⊢; linarith
  have hnear : IntegrableOn Q (Ioo (0:ℝ) 1) :=
    pastTailPower_sq_integrable_near hp0' ht0 ht1
  have hnear' : IntegrableOn Q (Ioc (0:ℝ) 1) :=
    hnear.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hfar : IntegrableOn Q (Ioi (1:ℝ)) :=
    pastTailPower_sq_integrable_far hp1 ht0 ht1
  have hsq : IntegrableOn Q (Ioi (0:ℝ)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1), integrableOn_union]
    exact ⟨hnear', hfar⟩
  have hcont : ContinuousOn (fun x : ℝ => pastTailPower p t x) (Ioi 0) := by
    unfold pastTailPower
    have hx : ContinuousOn (fun x : ℝ => x+t) (Ioi 0) :=
      continuousOn_id.add continuousOn_const
    have hpplus : ContinuousOn (fun x : ℝ => (x+t)^p) (Ioi 0) :=
      hx.rpow_const (by
        intro x hx
        have hx0 : 0 < x := by simpa using hx
        exact Or.inl (ne_of_gt (by linarith [ht0, hx0])))
    have hpx : ContinuousOn (fun x : ℝ => x^p) (Ioi 0) :=
      continuousOn_id.rpow_const (by
        intro x hx
        have hx0 : 0 < x := by simpa using hx
        exact Or.inl hx0.ne')
    exact hpplus.sub hpx
  have hmeas : AEStronglyMeasurable (fun x : ℝ => pastTailPower p t x)
      (volume.restrict (Ioi 0)) := hcont.aestronglyMeasurable measurableSet_Ioi
  rw [memLp_two_iff_integrable_sq hmeas]
  simpa [Q, IntegrableOn] using hsq

/-- The fixed Taylor coefficient functions used for one local past-tail
approximation. Coefficient zero is the profile at the expansion point; higher
coefficients are the ordinary derivatives divided by their factorials. -/
def pastTailTaylorCoeff (p : ℝ) (k : ℕ) (b x : ℝ) : ℝ :=
  if k = 0 then pastTailPower p b x else
    ((k.factorial : ℝ)⁻¹ * (descPochhammer ℝ k).eval p) *
      (x+b)^(p-(k:ℝ))

/-- The algebraic Taylor polynomial is the finite sum of its fixed coefficient
functions multiplied by the corresponding powers of the parameter offset. -/
theorem pastTailTaylorPoly_eq_coeff_sum {p b t x : ℝ} {m : ℕ} (hm : 0 < m) :
    pastTailTaylorPoly p m b t x =
      ∑ k ∈ Finset.range m, (t-b)^k * pastTailTaylorCoeff p k b x := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp [pastTailTaylorPoly, pastTailTaylorCoeff, pastTailPower]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        let L : ℕ → ℝ := fun k =>
          ((k.factorial:ℝ)⁻¹*(t-b)^k) *
            ((descPochhammer ℝ k).eval p * (x+b)^(p-(k:ℕ)))
        let R : ℕ → ℝ := fun k => (t-b)^k * pastTailTaylorCoeff p k b x
        have hi : (∑ k ∈ Finset.range m, L k) - x^p =
            ∑ k ∈ Finset.range m, R k := by
          simpa [L, R, pastTailTaylorPoly] using ih hmpos
        have hlast : L m = R m := by
          have hmne : m ≠ 0 := hm0
          dsimp [L, R, pastTailTaylorCoeff]
          simp only [if_neg hmne]
          rw [show (p-(m:ℕ)) = p-(m:ℝ) by norm_cast]
          ring
        change (∑ k ∈ Finset.range (m+1), L k) - x^p =
          ∑ k ∈ Finset.range (m+1), R k
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        calc
          (∑ k ∈ Finset.range m, L k) + L m - x^p =
              ((∑ k ∈ Finset.range m, L k) - x^p) + R m := by rw [hlast]; ring
          _ = (∑ k ∈ Finset.range m, R k) + R m := by rw [hi]

/-- Every fixed Taylor coefficient is an actual vector in the source `L²`. -/
theorem pastTailTaylorCoeff_memLp {p b : ℝ} {k : ℕ}
    (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2) (hb : 0 < b) (hb1 : b ≤ 1) :
    MemLp (fun x : ℝ => pastTailTaylorCoeff p k b x) 2
      (volume.restrict (Ioi 0)) := by
  by_cases hk : k = 0
  · subst k
    simpa [pastTailTaylorCoeff, pastTailPower] using
      (pastTailPower_memLp_two hp0 hp1 hb.le hb1)
  · have hq : p-(k:ℝ) < -(1/2:ℝ) := by
      have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hkcast : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
      linarith
    have hbase := shifted_rpow_memLp_two hq hb
    simpa [pastTailTaylorCoeff, hk] using
      hbase.const_mul (((k.factorial:ℝ)⁻¹ * (descPochhammer ℝ k).eval p))

/-- The Taylor polynomial candidate is the fixed-coefficient algebraic sum,
so its source-variable dependence is measurable. -/
theorem pastTailTaylorPoly_continuousOn {p : ℝ} {m : ℕ} {b t : ℝ}
    (hbpos : 0 < b) :
    ContinuousOn (fun x : ℝ => pastTailTaylorPoly p m b t x) (Ioi 0) := by
  unfold pastTailTaylorPoly
  have hb : ContinuousOn (fun x : ℝ => (x+b)^(p-(0:ℕ))) (Ioi 0) := by
    apply (continuousOn_id.add continuousOn_const).rpow_const
    intro x hx
    have hx0 : 0 < x := by simpa using hx
    have hpos : 0 < x+b := add_pos hx0 hbpos
    exact Or.inl (ne_of_gt (by simpa using hpos))
  have hterm (k : ℕ) : ContinuousOn
      (fun x : ℝ => ((k.factorial:ℝ)⁻¹*(t-b)^k) *
        ((descPochhammer ℝ k).eval p * (x+b)^(p-k))) (Ioi 0) := by
    have hpow : ContinuousOn (fun x : ℝ => (x+b)^(p-(k:ℕ))) (Ioi 0) := by
      apply (continuousOn_id.add continuousOn_const).rpow_const
      intro x hx
      have hx0 : 0 < x := by simpa using hx
      have hpos : 0 < x+b := add_pos hx0 hbpos
      exact Or.inl (ne_of_gt (by simpa using hpos))
    exact continuousOn_const.mul (continuousOn_const.mul hpow)
  have hsum := continuousOn_finsetSum (Finset.range m) (fun k hk => hterm k)
  have hxp : ContinuousOn (fun x : ℝ => x^p) (Ioi 0) := by
    apply continuousOn_id.rpow_const
    intro x hx
    have hx0 : 0 < x := by simpa using hx
    exact Or.inl hx0.ne'
  exact hsum.sub hxp

/-- Quantitative source-L² Taylor remainder on one refined geometric interval. -/
theorem pastTailTaylor_error_eLpNorm_le {p a b t : ℝ} {m : ℕ}
    (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2) (hm : 0 < m)
    (ha : 0 < a) (hab : a ≤ b) (hwidth : b-a ≤ a/2)
    (htlo : a ≤ t) (hthi : t ≤ b) :
    eLpNorm (fun x : ℝ => pastTailPower p t x - pastTailTaylorPoly p m b t x)
      2 (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal ((|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (a/2)^m * (-a^(2*(p-m)+1)/(2*(p-m)+1))^(1/2:ℝ)) := by
  let q : ℝ := p-m
  let c : ℝ := (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) * (a/2)^m
  have hmreal : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hq : q < -(1/2:ℝ) := by dsimp [q]; linarith
  have hq2 : 2*q < -1 := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let μ := volume.restrict (Ioi (0:ℝ))
  let f : ℝ → ℝ := fun x => pastTailPower p t x-pastTailTaylorPoly p m b t x
  let g : ℝ → ℝ := fun x => (x+a)^q
  have hg : MemLp g 2 μ := by
    dsimp [g, μ]
    exact shifted_rpow_memLp_two hq ha
  have hcontTail : ContinuousOn (fun x : ℝ => pastTailPower p t x) (Ioi 0) := by
    unfold pastTailPower
    have hplus : ContinuousOn (fun x : ℝ => x+t) (Ioi 0) :=
      continuousOn_id.add continuousOn_const
    have hpow : ContinuousOn (fun x : ℝ => (x+t)^p) (Ioi 0) := by
      apply hplus.rpow_const
      intro x hx
      have hx0 : 0 < x := by simpa using hx
      have htpos : 0 < t := lt_of_lt_of_le ha htlo
      exact Or.inl (ne_of_gt (by simpa using add_pos hx0 htpos))
    have hpowx : ContinuousOn (fun x : ℝ => x^p) (Ioi 0) := by
      apply continuousOn_id.rpow_const
      intro x hx
      have hx0 : 0 < x := by simpa using hx
      exact Or.inl hx0.ne'
    exact hpow.sub hpowx
  have hcontf : ContinuousOn f (Ioi 0) := by
    dsimp [f]
    exact hcontTail.sub (pastTailTaylorPoly_continuousOn (by linarith [hab, ha]))
  have hfas : AEStronglyMeasurable f μ := by
    dsimp [μ]
    exact hcontf.aestronglyMeasurable measurableSet_Ioi
  have hpoint : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hpoly : pastTailTaylorApprox p m b t x = pastTailTaylorPoly p m b t x := by
      by_cases htb : t = b
      · subst t
        exact pastTailTaylorApprox_eq_poly_endpoint hm ha hab hx0
      · exact pastTailTaylorApprox_eq_poly hm ha hab htlo (lt_of_le_of_ne hthi htb) hx0
    have hTaylor := pastTailTaylor_pointwise_error_uniform (p:=p) hm (by
      have : p < (m:ℝ) := by exact_mod_cast (by linarith : p < (m:ℝ))
      exact this) ha hab hwidth htlo hthi hx0
    have herror : |f x| ≤ c*(x+a)^q := by
      dsimp [f, c, q, g]
      rw [← hpoly]
      simpa [pastTailTaylorApprox, pastTailTaylorPoly] using hTaylor
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) q)]
    exact herror
  have hf : MemLp f 2 μ := hg.of_le_mul hfas hpoint
  have hcmp := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfas hpoint 2
  have hgnorm : eLpNorm g 2 μ =
      ENNReal.ofReal ((-a^(2*q+1)/(2*q+1))^(1/2:ℝ)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (p := (2:ENNReal))
      (by norm_num) ENNReal.ofNat_ne_top hg]
    have hint : ∫ x : ℝ, ‖g x‖ ^ (2:ℝ) ∂μ =
        -a^(2*q+1)/(2*q+1) := by
      rw [show (∫ x : ℝ, ‖g x‖ ^ (2:ℝ) ∂μ) =
          ∫ x : ℝ in Ioi 0, (x+a)^(2*q) by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        dsimp [g]
        have hx0 : 0 < x := by simpa using hx
        have hxpos : 0 < x+a := by linarith [ha]
        rw [abs_of_nonneg (Real.rpow_nonneg hxpos.le q)]
        calc
          ((x+a)^q)^(2:ℝ) = (x+a)^q*(x+a)^q := by rw [Real.rpow_two, pow_two]
          _ = (x+a)^(q+q) := (Real.rpow_add hxpos _ _).symm
          _ = (x+a)^(2*q) := by congr 1 <;> ring]
      exact integral_add_rpow_Ioi hq2 ha
    simp only [ENNReal.toReal_ofNat]
    rw [hint]
    norm_num
  rw [hgnorm] at hcmp
  have hcENN : ENNReal.ofReal c * ENNReal.ofReal
      ((-a^(2*q+1)/(2*q+1))^(1/2:ℝ)) =
      ENNReal.ofReal (c * (-a^(2*q+1)/(2*q+1))^(1/2:ℝ)) := by
    rw [← ENNReal.ofReal_mul]
    positivity
  rw [hcENN] at hcmp
  simpa [f, g, μ, c, q, ENNReal.ofReal_mul, mul_assoc] using hcmp

/-- Uniform local Taylor error for every refined partition interval in `[0,1]`;
the bound decays geometrically in the Taylor order and is independent of the
interval location and its tag. -/
theorem pastTailTaylor_error_eLpNorm_uniform {p a b t : ℝ} {m : ℕ}
    (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2) (hm : 0 < m)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hwidth : b-a ≤ a/2) (htlo : a ≤ t) (hthi : t ≤ b) :
    eLpNorm (fun x : ℝ => pastTailPower p t x - pastTailTaylorPoly p m b t x)
      2 (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal ((1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m) := by
  calc
    _ ≤ ENNReal.ofReal ((|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (a/2)^m * (-a^(2*(p-m)+1)/(2*(p-m)+1))^(1/2:ℝ)) :=
      pastTailTaylor_error_eLpNorm_le hp0 hp1 hm ha hab hwidth htlo hthi
    _ ≤ ENNReal.ofReal ((1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^m) :=
      ENNReal.ofReal_le_ofReal (pastTailTaylor_scalar_bound hp0 hp1 hm ha
        (le_trans hab hb1))

end BrownianSharp.AlignmentFractionalPastTailL2Approx
