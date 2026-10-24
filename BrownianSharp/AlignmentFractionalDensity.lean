import BrownianSharp.AlignmentFractionalTranslation
import BrownianSharp.AlignmentFractionalSemigroup
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction ContDiff

namespace BrownianSharp.AlignmentFractionalDensity

open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation

/-- Continuous profiles on the unit interval are embedded into the source
Hilbert space by bounded extension followed by the canonical continuous-to-Lp
map. -/
noncomputable def profileToL2 : C(UnitInterval, ℝ) →L[ℝ] UnitL2 := by
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  exact (BoundedContinuousFunction.toLp (E := ℝ) (𝕜 := ℝ) (p := 2)
    ((volume : Measure ℝ).restrict UnitInterval)).comp extendUnitProfile

theorem profileToL2_coe (f : C(UnitInterval, ℝ)) :
    profileToL2 f =ᵐ[(volume : Measure ℝ).restrict UnitInterval]
      (fun x : ℝ => f (clipUnit x)) := by
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  change BoundedContinuousFunction.toLp (E := ℝ) (p := 2)
    ((volume : Measure ℝ).restrict UnitInterval) ℝ (extendUnitProfile f) =ᵐ[
      (volume : Measure ℝ).restrict UnitInterval] (fun x : ℝ => f (clipUnit x))
  simpa [extendUnitProfile] using
    (BoundedContinuousFunction.coeFn_toLp (E := ℝ) (p := 2)
      ((volume : Measure ℝ).restrict UnitInterval) ℝ (extendUnitProfile f))

/-- The causal kernel integral on the fixed unit source interval is exactly
its interval Riemann--Liouville integral. -/
theorem causal_integral_eq_interval {α t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (F : ℝ → ℝ) :
    (∫ u, causalKernel α t u * F u ∂(volume.restrict UnitInterval)) =
      rlIntegral α F t := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  let G : ℝ → ℝ := fun u => kernel α (t-u) * F u
  have hne : ∀ᵐ u ∂μ, u ≠ 0 :=
    ae_mono Measure.restrict_le_self (volume.ae_ne 0)
  have heq : (fun u => causalKernel α t u * F u) =ᵐ[μ]
      (Set.Ioo 0 t).indicator G := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with u hu hzero
    rcases hu with ⟨hu0, hu1⟩
    by_cases hut : u < t
    · have huPos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      have hmem : u ∈ Set.Ioo (0:ℝ) t := ⟨huPos, hut⟩
      simp [causalKernel, G, hmem, hut]
    · have hut' : t ≤ u := le_of_not_gt hut
      have hnot : u ∉ Set.Ioo (0:ℝ) t := by
        simp [Set.mem_Ioo, hut']
      simp [causalKernel, G, hnot, hut']
  rw [integral_congr_ae heq, integral_indicator measurableSet_Ioo]
  have hsub : Set.Ioo 0 t ⊆ UnitInterval := by
    intro u hu
    exact ⟨le_of_lt hu.1, le_trans (le_of_lt hu.2) ht1⟩
  rw [Measure.restrict_restrict_of_subset hsub]
  unfold rlIntegral
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht0]

/-- Applying the genuine continuous RL operator to a continuous input agrees
with the classical interval-integral formula. -/
theorem fractionalRL_profile (α : ℝ) (hα : 1/2 < α)
    (f : C(UnitInterval, ℝ)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    fractionalRL α hα (profileToL2 f) ⟨t, ⟨ht0, ht1⟩⟩ =
      rlIntegral α (fun u => f (clipUnit u)) t := by
  rw [fractionalRL_apply α hα (profileToL2 f) t ht0 ht1]
  calc
    (∫ u, causalKernel α t u * profileToL2 f u
        ∂(volume.restrict UnitInterval)) =
      ∫ u, causalKernel α t u * f (clipUnit u)
        ∂(volume.restrict UnitInterval) := by
      apply integral_congr_ae
      filter_upwards [profileToL2_coe f] with u hu
      rw [hu]
    _ = rlIntegral α (fun u => f (clipUnit u)) t :=
      causal_integral_eq_interval ht0 ht1 (fun u => f (clipUnit u))



/-- The bounded RL operator on continuous profiles. -/
noncomputable def fractionalOnC (α : ℝ) (hα : 1/2 < α) :
    C(UnitInterval, ℝ) →L[ℝ] C(UnitInterval, ℝ) :=
  (fractionalRL α hα).comp profileToL2

/-- The monomial profile on the compact unit interval. -/
noncomputable def monomialProfile (m : ℕ) : C(UnitInterval, ℝ) :=
  Polynomial.toContinuousMapOn (Polynomial.X ^ m) UnitInterval

theorem clip_monomial_integral (α t : ℝ) (m : ℕ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rlIntegral α (fun u => monomialProfile m (clipUnit u)) t =
      rlIntegral α (fun u => u ^ (m:ℝ)) t := by
  unfold rlIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  have hu0 : 0 ≤ u := by
    simpa [Set.uIcc, min_eq_left ht0, max_eq_right ht0] using hu.1
  have hut : u ≤ t := by
    simpa [Set.uIcc, min_eq_left ht0, max_eq_right ht0] using hu.2
  have hu1 : u ≤ 1 := le_trans hut ht1
  have hc : clipUnit u = ⟨u, ⟨hu0, hu1⟩⟩ := by
    apply Subtype.ext
    simp [clipUnit, hu0, hu1]
  simp [monomialProfile, hc]

theorem fractionalOnC_monomial (α : ℝ) (hα : 1/2 < α) (m : ℕ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    fractionalOnC α hα (monomialProfile m) ⟨t, ⟨ht0, ht1⟩⟩ =
      rlIntegral α (fun u => u ^ (m:ℝ)) t := by
  rw [fractionalOnC, ContinuousLinearMap.comp_apply]
  rw [fractionalRL_profile α hα (monomialProfile m) t ht0 ht1]
  exact clip_monomial_integral α t m ht0 ht1

theorem fractionalOnC_semigroup_monomial {a b : ℝ} (ha : 1/2 < a)
    (hb : 1/2 < b) (m : ℕ) :
    fractionalOnC a ha (fractionalOnC b hb (monomialProfile m)) =
      fractionalOnC (a+b) (by linarith) (monomialProfile m) := by
  ext x
  rcases x.2 with ⟨hx0, hx1⟩
  by_cases hx : 0 < x.1
  · rw [fractionalOnC, ContinuousLinearMap.comp_apply]
    rw [fractionalRL_profile a ha (fractionalOnC b hb (monomialProfile m))
      x.1 hx0 hx1]
    have hfunc : ∀ y : UnitInterval,
        fractionalOnC b hb (monomialProfile m) y =
          rlIntegral b (fun v => v ^ (m:ℝ)) y.1 := by
      intro y
      exact fractionalOnC_monomial b hb m y.1 y.2.1 y.2.2
    have hint : rlIntegral a
        (fun u => fractionalOnC b hb (monomialProfile m) (clipUnit u)) x.1 =
        rlIntegral a (fun u => rlIntegral b (fun v => v^(m:ℝ)) u) x.1 := by
      unfold rlIntegral
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := by
        simpa [Set.uIcc, min_eq_left hx0, max_eq_right hx0] using hu.1
      have huLe : u ≤ x.1 := by
        simpa [Set.uIcc, min_eq_left hx0, max_eq_right hx0] using hu.2
      have hu1 : u ≤ 1 := le_trans huLe hx1
      have hclip : (clipUnit u).1 = u := by
        simp [clipUnit, hu0, hu1]
      change kernel a (x.1-u) *
          fractionalOnC b hb (monomialProfile m) (clipUnit u) =
        kernel a (x.1-u) * rlIntegral b (fun v => v^(m:ℝ)) u
      rw [hfunc (clipUnit u), hclip]
    rw [hint]
    rw [fractionalOnC_monomial (a+b) (by linarith) m x.1 hx0 hx1]
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    exact BrownianSharp.AlignmentFractionalSemigroup.rlIntegral_semigroup_natPow
      ha0 hb0 hx m
  · have hxEq : x.1 = 0 := le_antisymm (le_of_not_gt hx) hx0
    have hxid : x = ⟨0, ⟨le_rfl, by norm_num⟩⟩ := Subtype.ext hxEq
    rw [hxid]
    rw [fractionalOnC, ContinuousLinearMap.comp_apply]
    rw [fractionalRL_profile a ha (fractionalOnC b hb (monomialProfile m))
      0 le_rfl (by norm_num)]
    rw [fractionalOnC_monomial (a+b) (by linarith) m 0 le_rfl (by norm_num)]
    simp [rlIntegral]


/-- The linear span of the monomial profiles is dense, by the Weierstrass
approximation theorem and the polynomial coefficient expansion. -/
def monomialSpan : Submodule ℝ C(UnitInterval, ℝ) :=
  Submodule.span ℝ (Set.range monomialProfile)

theorem polynomialProfile_mem_monomialSpan (p : Polynomial ℝ) :
    p.toContinuousMapOn UnitInterval ∈ monomialSpan := by
  have hpoly : p = ∑ i ∈ p.support, Polynomial.C (p.coeff i) * Polynomial.X ^ i :=
    Polynomial.as_sum_support_C_mul_X_pow p
  have hexp : p.toContinuousMapOn UnitInterval =
      ∑ i ∈ p.support, (p.coeff i) • monomialProfile i := by
    ext x
    have hval := congrArg (fun q : Polynomial ℝ => q.eval x.1) hpoly
    simpa [monomialProfile, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X_pow] using hval
  rw [hexp]
  apply Submodule.sum_mem _
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

theorem monomialSpan_dense : Dense (monomialSpan : Set C(UnitInterval, ℝ)) := by
  have hsubset : (polynomialFunctions UnitInterval : Set C(UnitInterval, ℝ)) ⊆
      (monomialSpan : Set C(UnitInterval, ℝ)) := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    rcases hf with ⟨p, rfl⟩
    exact polynomialProfile_mem_monomialSpan p
  have hdense : Dense (polynomialFunctions UnitInterval : Set C(UnitInterval, ℝ)) := by
    change Dense (polynomialFunctions (Set.Icc (0:ℝ) 1) : Set C(UnitInterval, ℝ))
    have htop := congrArg (fun s : Subalgebra ℝ C(UnitInterval, ℝ) =>
      (s : Set C(UnitInterval, ℝ)))
      (polynomialFunctions_closure_eq_top (0:ℝ) 1)
    apply dense_iff_closure_eq.2
    simpa [Subalgebra.topologicalClosure_coe] using htop
  exact hdense.mono hsubset

theorem fractionalOnC_semigroup {a b : ℝ} (ha : 1/2 < a)
    (hb : 1/2 < b) :
    (fractionalOnC a ha).comp (fractionalOnC b hb) =
      fractionalOnC (a+b) (by linarith) := by
  apply ContinuousLinearMap.ext_on monomialSpan_dense
  intro f hf
  rcases hf with ⟨m, rfl⟩
  exact fractionalOnC_semigroup_monomial ha hb m

/-- Removing the unit-interval clipping on the integration interval. -/
theorem clip_RL_integral_eq {α t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (F : ℝ → ℝ) :
    rlIntegral α (fun u => F (clipUnit u)) t = rlIntegral α F t := by
  unfold rlIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  have hu0 : 0 ≤ u := by
    simpa [Set.uIcc, min_eq_left ht0, max_eq_right ht0] using hu.1
  have hut : u ≤ t := by
    simpa [Set.uIcc, min_eq_left ht0, max_eq_right ht0] using hu.2
  have hu1 : u ≤ 1 := le_trans hut ht1
  have hclip : (clipUnit u).1 = u := by simp [clipUnit, hu0, hu1]
  change kernel α (t-u) * F ((clipUnit u).1) = kernel α (t-u) * F u
  rw [hclip]

theorem kernel_one (x : ℝ) : kernel 1 x = 1 := by
  simp [kernel, Real.Gamma_one]

theorem rlIntegral_one_eq_interval (F : ℝ → ℝ) (t : ℝ) :
    rlIntegral 1 F t = ∫ u in (0:ℝ)..t, F u := by
  unfold rlIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  change kernel 1 (t-u) * F u = F u
  rw [kernel_one]
  ring

/-- Restriction of a smooth real profile to the unit interval. -/
noncomputable def restrictProfile (F : ℝ → ℝ) (hF : Continuous F) :
    C(UnitInterval, ℝ) := ⟨fun x => F x.1, hF.comp continuous_subtype_val⟩

noncomputable def derivativeProfile (n : ℕ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F) : C(UnitInterval, ℝ) :=
  restrictProfile (iteratedDeriv n F)
    (by simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv n hF).continuous)

theorem fractionalOnC_one_derivative (F : ℝ → ℝ) (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hF0 : F 0 = 0) :
    fractionalOnC 1 (by norm_num) (derivativeProfile 1 F hF) =
      restrictProfile F hF.continuous := by
  ext x
  have hx0 : 0 ≤ x.1 := x.2.1
  have hx1 : x.1 ≤ 1 := x.2.2
  rw [fractionalOnC, ContinuousLinearMap.comp_apply]
  rw [fractionalRL_profile 1 (by norm_num) (derivativeProfile 1 F hF)
      x.1 hx0 hx1]
  change rlIntegral 1 (fun u => iteratedDeriv 1 F (clipUnit u).1) x.1 = _
  rw [clip_RL_integral_eq hx0 hx1 (iteratedDeriv 1 F)]
  rw [rlIntegral_one_eq_interval]
  rw [iteratedDeriv_one]
  rw [intervalIntegral.integral_deriv_eq_sub]
  · simp [restrictProfile, hF0]
  · intro y hy
    exact (hF.differentiable (by simp)).differentiableAt
  · exact hF.continuous_deriv (by norm_num) |>.intervalIntegrable _ _

/-- Iterated ordinary integration, expressed as a continuous linear operator. -/
noncomputable def oneIntegralIterate : ℕ →
    C(UnitInterval, ℝ) →L[ℝ] C(UnitInterval, ℝ)
  | 0 => ContinuousLinearMap.id ℝ _
  | n+1 => (fractionalOnC 1 (by norm_num)).comp (oneIntegralIterate n)

theorem integerOrder_eq_iterate (n : ℕ) (hn : 0 < n) :
    fractionalOnC (n:ℝ) (by
      have hn1 : 1 ≤ n := by omega
      have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith) =
      oneIntegralIterate n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [oneIntegralIterate, fractionalOnC]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hIH := ih hnpos
      simp only [oneIntegralIterate]
      rw [← hIH]
      have hsem := fractionalOnC_semigroup (a := 1) (b := (n:ℝ)) (by norm_num)
        (by
          have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
          linarith)
      convert hsem.symm using 1 <;> push_cast <;> ring

/-- Repeated integration recovers a smooth function from its qth derivative
when its lower derivatives vanish at the origin. -/
theorem oneIntegralIterate_derivative_recovery (n : ℕ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j ≤ n, iteratedDeriv j F 0 = 0) :
    oneIntegralIterate n (derivativeProfile n F hF) = restrictProfile F hF.continuous := by
  induction n generalizing F with
  | zero =>
    simp [oneIntegralIterate, derivativeProfile, restrictProfile, iteratedDeriv_zero]
  | succ n ih =>
    have hF' : ContDiff ℝ (∞ : ℕ∞ω) (deriv F) := by
      exact (contDiff_infty_iff_deriv.mp hF).2
    have hzero' : ∀ j ≤ n, iteratedDeriv j (deriv F) 0 = 0 := by
      intro j hj
      rw [← iteratedDeriv_succ']
      exact hzero (j+1) (by omega)
    have hrec := ih (F := deriv F) hF' hzero'
    have hprofiles : derivativeProfile (n+1) F hF = derivativeProfile n (deriv F) hF' := by
      apply ContinuousMap.ext
      intro x
      simp [derivativeProfile, iteratedDeriv_succ']
    simp only [oneIntegralIterate, ContinuousLinearMap.comp_apply]
    rw [hprofiles, hrec]
    convert fractionalOnC_one_derivative (F := F) hF (hzero 0 (by omega)) using 1 <;> simp [derivativeProfile, iteratedDeriv_one]

/-- Smooth compactly supported atoms have exact fractional preimages on the
unit interval: choose any integer order q strictly above α and one-half. -/
theorem smooth_atom_fractional_preimage (α : ℝ) (hα : 1/2 < α) (q : ℕ)
    (hqα : α < q) (hqβ : 1/2 < (q:ℝ)-α) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j ≤ q, iteratedDeriv j F 0 = 0) :
    fractionalOnC α hα
      (fractionalOnC ((q:ℝ)-α) hqβ (derivativeProfile q F hF)) =
        restrictProfile F hF.continuous := by
  have hqpos : 0 < q := by
    have hα0 : (0:ℝ) < α := by linarith
    have hqR : (0:ℝ) < (q:ℝ) := lt_trans hα0 hqα
    exact_mod_cast hqR
  have hsem' :
      (fractionalOnC α hα).comp (fractionalOnC ((q:ℝ)-α) hqβ) =
        fractionalOnC (q:ℝ) (by
          have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
          linarith) := by
    convert fractionalOnC_semigroup (a := α) (b := (q:ℝ)-α) hα hqβ using 1 <;> ring
  have hcomp := congrArg (fun T : C(UnitInterval, ℝ) →L[ℝ] C(UnitInterval, ℝ) =>
    T (derivativeProfile q F hF)) hsem'
  rw [integerOrder_eq_iterate q hqpos] at hcomp
  exact hcomp.trans (oneIntegralIterate_derivative_recovery q F hF hzero)

/-- The smooth atom preimage above is an actual source `L²` element for the
bounded Riemann--Liouville operator, via the canonical continuous-profile
embedding. -/
theorem smooth_atom_fractional_preimage_L2 (α : ℝ) (hα : 1/2 < α) (q : ℕ)
    (hqα : α < q) (hqβ : 1/2 < (q:ℝ)-α) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j ≤ q, iteratedDeriv j F 0 = 0) :
    fractionalRL α hα
      (profileToL2 (fractionalOnC ((q:ℝ)-α) hqβ (derivativeProfile q F hF))) =
        restrictProfile F hF.continuous := by
  change fractionalOnC α hα
      (fractionalOnC ((q:ℝ)-α) hqβ (derivativeProfile q F hF)) = _
  exact smooth_atom_fractional_preimage α hα q hqα hqβ F hF hzero



end BrownianSharp.AlignmentFractionalDensity
