import BrownianSharp.AlignmentFractionalKernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! The negative-time Mandelbrot--van Ness tail for fractional Brownian motion.

For `p = H - 1/2`, the tail kernel is `(x+t)^p - x^p`, `x ≥ 0`. The
module isolates its local singularity and its square-integrable far tail. -/

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentFractionalPastTail

/-- The MvN negative-time tail after reflecting `u ≤ 0` to `x = -u ≥ 0`. -/
def pastTailPower (p t x : ℝ) : ℝ := (x + t) ^ p - x ^ p

/-- On the negative half-line, the actual tail kernel is the reflected
power-difference kernel; it vanishes on positive source coordinates. -/
def pastTailKernel (H t u : ℝ) : ℝ :=
  if u < 0 then pastTailPower (H - 1/2) t (-u) else 0

/-- The far-past tail is controlled by its derivative, uniformly for
`0 ≤ t ≤ 1` and `x ≥ 1`. -/
theorem pastTailPower_abs_le_far_bound {p t x : ℝ} (hp : p < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : 1 ≤ x) :
    |pastTailPower p t x| ≤ |p| * x ^ (p - 1) := by
  by_cases hpt : t = 0
  · subst t
    simp [pastTailPower]
    positivity
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hpt)
  let f : ℝ → ℝ := fun y => y ^ p
  have hcont : ContinuousOn f (Set.Icc x (x+t)) := by
    apply continuousOn_id.rpow_const
    intro y hy
    have hypos : 0 < y := by linarith [hy.1, hx]
    exact Or.inl hypos.ne'
  have hderiv : ∀ y ∈ Set.Ioo x (x+t), HasDerivAt f (p * y^(p-1)) y := by
    intro y hy
    have hypos : 0 < y := by linarith [hx, hy.1]
    simpa [f] using Real.hasDerivAt_rpow_const (x := y) (p := p) (Or.inl hypos.ne')
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope f (fun y => p*y^(p-1))
    (by linarith : x < x+t) hcont hderiv
  have hcx : x ≤ c := le_of_lt hc.1
  have hcle : c ≤ x+t := le_of_lt hc.2
  have hcp : 0 < c := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx) hcx
  have hexp : p - 1 ≤ 0 := by linarith
  have hpow : c^(p-1) ≤ x^(p-1) := Real.rpow_le_rpow_of_nonpos
    (by linarith : 0 < x) hcx hexp
  have hdiff : pastTailPower p t x = t * (p * c^(p-1)) := by
    dsimp [pastTailPower, f] at hcslope ⊢
    have hden : x+t-x = t := by ring
    rw [hden] at hcslope
    have htne : t ≠ 0 := ne_of_gt ht
    have := (eq_div_iff htne).mp hcslope
    nlinarith
  rw [hdiff, abs_mul, abs_of_nonneg ht0, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hcp) _)]
  calc
    t * (|p| * c^(p-1)) ≤ 1 * (|p| * x^(p-1)) := by
      apply mul_le_mul ht1
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg p))
        (by positivity) (by positivity)
    _ = |p| * x^(p-1) := by ring

/-- The squared far-past kernel is integrable uniformly beyond unit distance.
This is the quantitative tail component of the full-line MvN `L²` vector. -/
theorem pastTailPower_sq_integrable_far {p t : ℝ} (hp : p < 1/2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntegrableOn (fun x : ℝ => (pastTailPower p t x)^2) (Set.Ioi 1) := by
  have hpow : IntegrableOn (fun x : ℝ => x^(2*(p-1))) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hdom : IntegrableOn (fun x : ℝ => p^2 * x^(2*(p-1))) (Set.Ioi 1) :=
    hpow.const_mul (p^2)
  have hcont : ContinuousOn (fun x : ℝ => (pastTailPower p t x)^2) (Set.Ioi 1) := by
    have hplus : ContinuousOn (fun x : ℝ => x+t) (Set.Ioi 1) :=
      continuousOn_id.add continuousOn_const
    have hplusPow : ContinuousOn (fun x : ℝ => (x+t)^p) (Set.Ioi 1) :=
      hplus.rpow_const (by
        intro x hx
        have hx' : 1 < x := by simpa using hx
        have hxpos : 0 < x := by linarith
        exact Or.inl (ne_of_gt (by linarith [hxpos, ht0])))
    have hpowX : ContinuousOn (fun x : ℝ => x^p) (Set.Ioi 1) :=
      continuousOn_id.rpow_const (by
        intro x hx
        have hx' : 1 < x := by simpa using hx
        have hxpos : 0 < x := by linarith
        exact Or.inl hxpos.ne')
    change ContinuousOn (fun x => ((x+t)^p-x^p)^2) (Set.Ioi 1)
    exact (hplusPow.sub hpowX).pow 2
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (pastTailPower p t x)^2)
      (volume.restrict (Set.Ioi 1)) := hcont.aestronglyMeasurable measurableSet_Ioi
  have hdom' : ∀ᵐ x ∂(volume.restrict (Set.Ioi 1)),
      ‖(pastTailPower p t x)^2‖ ≤ p^2 * x^(2*(p-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx
    have htail := pastTailPower_abs_le_far_bound (by linarith : p < 1) ht0 ht1 hx1
    have hxpos : 0 < x := by linarith
    have hpw : 0 ≤ x^(p-1) := Real.rpow_nonneg hxpos.le _
    have hpow2 : (x^(p-1))^2 = x^(2*(p-1)) := by
      calc
        (x^(p-1))^2 = x^(p-1) * x^(p-1) := by rw [pow_two]
        _ = x^((p-1)+(p-1)) := (Real.rpow_add hxpos _ _).symm
        _ = x^(2*(p-1)) := by congr 1; ring
    have hnonneg : 0 ≤ pastTailPower p t x ^ 2 := sq_nonneg _
    have habs2 : |pastTailPower p t x|^2 ≤
        (|p| * x^(p-1))^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 htail
    have heq : (|p| * x^(p-1))^2 = p^2 * x^(2*(p-1)) := by
      rw [mul_pow, sq_abs, hpow2]
    have hbound : |pastTailPower p t x|^2 ≤ p^2 * x^(2*(p-1)) := by
      rw [heq] at habs2
      exact habs2
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound
  rw [IntegrableOn]
  exact hdom.mono' hmeas hdom'

/-- The local singularity of the past tail is square-integrable precisely in
the fBm range `p > -1/2`; the bound is uniform for `t ∈ [0,1]`. -/
theorem pastTailPower_sq_integrable_near {p t : ℝ} (hp : -1/2 < p)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntegrableOn (fun x : ℝ => (pastTailPower p t x)^2) (Set.Ioo 0 1) := by
  have hplus : ContinuousOn (fun x : ℝ => x+t) (Set.Ioo 0 1) :=
    continuousOn_id.add continuousOn_const
  have hplusPow : ContinuousOn (fun x : ℝ => (x+t)^p) (Set.Ioo 0 1) :=
    hplus.rpow_const (by
      intro x hx
      exact Or.inl (ne_of_gt (by linarith [hx.1, ht0])))
  have hpowX : ContinuousOn (fun x : ℝ => x^p) (Set.Ioo 0 1) :=
    continuousOn_id.rpow_const (by
      intro x hx
      exact Or.inl hx.1.ne')
  have hcont : ContinuousOn (fun x : ℝ => (pastTailPower p t x)^2) (Set.Ioo 0 1) := by
    change ContinuousOn (fun x => ((x+t)^p-x^p)^2) (Set.Ioo 0 1)
    exact (hplusPow.sub hpowX).pow 2
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (pastTailPower p t x)^2)
      (volume.restrict (Set.Ioo 0 1)) := hcont.aestronglyMeasurable measurableSet_Ioo
  rw [IntegrableOn]
  by_cases hpn : p < 0
  · have hbase : IntegrableOn (fun x : ℝ => x^(2*p)) (Set.Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).2 (by linarith)
    have hdom : IntegrableOn (fun x : ℝ => x^(2*p)) (Set.Ioo 0 1) := hbase
    apply hdom.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hsum : x ≤ x+t := by linarith [ht0]
    have hmono : (x+t)^p ≤ x^p := Real.rpow_le_rpow_of_nonpos hx0 hsum (by linarith)
    have hpluspos : 0 ≤ (x+t)^p := Real.rpow_nonneg (by positivity) _
    have hsign : (x+t)^p - x^p ≤ 0 := sub_nonpos.mpr hmono
    have habs : |(x+t)^p - x^p| ≤ x^p := by
      rw [abs_of_nonpos hsign]
      linarith [hpluspos]
    have hpowpos : 0 ≤ x^p := Real.rpow_nonneg hx0.le _
    have hsq : |(x+t)^p - x^p|^2 ≤ (x^p)^2 :=
      (sq_le_sq₀ (abs_nonneg _) hpowpos).2 habs
    have hpoweq : (x^p)^2 = x^(2*p) := by
      rw [pow_two, ← Real.rpow_add hx0]
      congr 1
      ring
    have hq : ‖(pastTailPower p t x)^2‖ ≤ x^(2*p) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        ((x+t)^p-x^p)^2 = |(x+t)^p-x^p|^2 := by rw [sq_abs]
        _ ≤ (x^p)^2 := hsq
        _ = x^(2*p) := hpoweq
    simpa using hq
  · have hp0 : 0 ≤ p := le_of_not_gt hpn
    have hbase : IntegrableOn (fun _ : ℝ => ((2:ℝ)^p+1)^2) (Set.Ioo 0 1) :=
      integrableOn_const (by exact (measure_Ioo_lt_top (μ := volume) (a := (0:ℝ)) (b := 1)).ne)
    apply hbase.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hxt : x+t ≤ 2 := by linarith [ht1]
    have hpow1 : 0 ≤ (x+t)^p := Real.rpow_nonneg (by positivity) _
    have hpow2 : 0 ≤ x^p := Real.rpow_nonneg hx0.le _
    have hlarge : (x+t)^p ≤ (2:ℝ)^p := Real.rpow_le_rpow (by positivity) hxt hp0
    have hsmall : x^p ≤ (1:ℝ)^p := Real.rpow_le_rpow hx0.le hx1.le hp0
    have habs : |(x+t)^p-x^p| ≤ (2:ℝ)^p+1 := by
      calc
        _ ≤ |(x+t)^p|+|x^p| := abs_sub _ _
        _ = (x+t)^p+x^p := by rw [abs_of_nonneg hpow1, abs_of_nonneg hpow2]
        _ ≤ (2:ℝ)^p+1 := by simpa using add_le_add hlarge hsmall
    have hq : ‖(pastTailPower p t x)^2‖ ≤ ((2:ℝ)^p+1)^2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change ((x+t)^p-x^p)^2 ≤ ((2:ℝ)^p+1)^2
      have hC : 0 ≤ (2:ℝ)^p+1 := by positivity
      have hsq : |(x+t)^p-x^p|^2 ≤ ((2:ℝ)^p+1)^2 :=
        (sq_le_sq₀ (abs_nonneg _) hC).2 habs
      simpa only [sq_abs] using hsq
    simpa using hq

/-- The reflected MvN tail belongs to `L²(ℝ)` for the full fBm Hurst range. -/
theorem pastTailKernel_memLp {H t : ℝ} (hH : 0 < H) (hH1 : H < 1)
    (ht : t ∈ Set.Icc 0 1) : MemLp (pastTailKernel H t) 2 (volume : Measure ℝ) := by
  let p : ℝ := H - 1/2
  have hp0 : -1/2 < p := by dsimp [p]; linarith
  have hp1 : p < 1/2 := by dsimp [p]; linarith
  have ht0 := ht.1
  have ht1 := ht.2
  let Q : ℝ → ℝ := fun x => (pastTailPower p t x)^2
  have hnear : IntegrableOn Q (Set.Ioo 0 1) :=
    pastTailPower_sq_integrable_near hp0 ht0 ht1
  have hnear' : IntegrableOn Q (Set.Ioc 0 1) :=
    hnear.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hfar : IntegrableOn Q (Set.Ioi 1) :=
    pastTailPower_sq_integrable_far hp1 ht0 ht1
  have hpos : IntegrableOn Q (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1), integrableOn_union]
    exact ⟨hnear', hfar⟩
  have hneg : IntegrableOn (fun u : ℝ => (pastTailKernel H t u)^2) (Set.Iio 0) := by
    have hreflect := (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding).2 hpos
    have hEq : (fun u : ℝ => Q (-u)) =ᵐ[volume.restrict (Set.Iio 0)]
        (fun u => (pastTailKernel H t u)^2) := by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
      have hu0 : u < 0 := by simpa using hu
      simp [Q, pastTailKernel, pastTailPower, p, hu0]
    have hreflect' : IntegrableOn (fun u : ℝ => Q (-u)) (Set.Iio 0) := by
      have hset : Neg.neg ⁻¹' Set.Ioi (0:ℝ) = Set.Iio 0 := by
        ext u
        simp
      rw [hset] at hreflect
      simpa [Function.comp_def] using hreflect
    exact hreflect'.congr hEq
  have hleft : IntegrableOn (fun u : ℝ => (pastTailKernel H t u)^2) (Set.Iic 0) :=
    hneg.congr_set_ae Iio_ae_eq_Iic.symm
  have hsq : Integrable (fun u : ℝ => (pastTailKernel H t u)^2) (volume : Measure ℝ) := by
    rw [← integrableOn_univ,
      ← Set.Iic_union_Ioi_of_le (show (0:ℝ) ≤ 0 by rfl), integrableOn_union]
    exact ⟨hleft, by
      have hzero : (fun u : ℝ => (pastTailKernel H t u)^2) =ᵐ[volume.restrict (Set.Ioi 0)]
          (fun _ : ℝ => (0:ℝ)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : ¬ u < 0 := by linarith [show 0 < u by simpa using hu]
        simp [pastTailKernel, hu0]
      exact (integrable_zero ℝ ℝ (volume.restrict (Set.Ioi 0))).congr hzero.symm⟩
  have hmeas : AEStronglyMeasurable (pastTailKernel H t) (volume : Measure ℝ) := by
    have hnegmeas : AEStronglyMeasurable (pastTailKernel H t)
        (volume.restrict (Set.Iio 0)) := by
      have h1 : ContinuousOn (fun u : ℝ => t-u) (Set.Iio 0) :=
        continuousOn_const.sub continuousOn_id
      have h2 : ContinuousOn (fun u : ℝ => -u) (Set.Iio 0) :=
        continuousOn_id.neg
      have h1p : ContinuousOn (fun u : ℝ => (t-u)^p) (Set.Iio 0) :=
        h1.rpow_const (by
          intro u hu
          have hu0 : u < 0 := by simpa using hu
          exact Or.inl (ne_of_gt (by linarith [ht0, hu0])))
      have h2p : ContinuousOn (fun u : ℝ => (-u)^p) (Set.Iio 0) :=
        h2.rpow_const (by
          intro u hu
          have hu0 : u < 0 := by simpa using hu
          exact Or.inl (ne_of_gt (by linarith [hu0])))
      have hfun : ContinuousOn (fun u : ℝ => (t-u)^p-(-u)^p) (Set.Iio 0) := h1p.sub h2p
      have hfm : AEStronglyMeasurable (fun u : ℝ => (t-u)^p-(-u)^p)
          (volume.restrict (Set.Iio 0)) := hfun.aestronglyMeasurable measurableSet_Iio
      have heq : (pastTailKernel H t) =ᵐ[volume.restrict (Set.Iio 0)]
          (fun u : ℝ => (t-u)^p-(-u)^p) := by
        filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
        have hu0 : u < 0 := by simpa using hu
        simp [pastTailKernel, pastTailPower, p, hu0]
        congr 1 <;> ring
      exact hfm.congr heq.symm
    have hposmeas : AEStronglyMeasurable (pastTailKernel H t)
        (volume.restrict (Set.Ici 0)) := by
      have heq : (pastTailKernel H t) =ᵐ[volume.restrict (Set.Ici 0)]
          (fun _ : ℝ => (0:ℝ)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
        have hu0 : 0 ≤ u := by simpa using hu
        simp [pastTailKernel, not_lt.mpr hu0]
      exact (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ℝ => (0:ℝ)) (volume.restrict (Set.Ici 0))).congr heq.symm
    have hcover : Set.Iio (0:ℝ) ∪ Set.Ici 0 = Set.univ := by ext u; simp
    have hrestrict : AEStronglyMeasurable (pastTailKernel H t)
        (volume.restrict (Set.Iio 0 ∪ Set.Ici 0)) :=
      (aestronglyMeasurable_union_iff).2 ⟨hnegmeas, hposmeas⟩
    simpa [hcover] using hrestrict
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

end BrownianSharp.AlignmentFractionalPastTail
