import BrownianSharp.AlignmentFractionalDensity
import BrownianSharp.SmoothAtom
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory
open scoped ContDiff Topology
open BrownianSharp.AlignmentFractionalL2
namespace BrownianSharp.AlignmentFractionalTail

/-- Repeated integration by parts transfers all ordinary derivatives from a
smooth compact atom to a supplied sequence of smooth kernel derivatives on the
integration interval. The local hypotheses permit kernels singular away from
the interval. -/
theorem transfer_derivative_sequence (n : ℕ) (K : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j < n, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0)
    (hKderiv : ∀ j < n, ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (K j) (K (j+1) x) x)
    (hKint : ∀ j < n, IntervalIntegrable (K (j+1)) volume 0 1) :
    (∫ x in (0:ℝ)..1, K 0 x * iteratedDeriv n F x) =
      (-1:ℝ)^n * (∫ x in (0:ℝ)..1, K n x * F x) := by
  induction n generalizing K with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    have hzeroN : iteratedDeriv n F 0 = 0 ∧ iteratedDeriv n F 1 = 0 := hzero n (by omega)
    have hstep := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0:ℝ)) (b := 1)
      (u := K 0) (u' := K 1)
      (v := iteratedDeriv n F) (v' := deriv (iteratedDeriv n F))
      (by intro x hx; exact hKderiv 0 (by omega) x hx)
      (by intro x hx
          have hcf : ContDiff ℝ (∞ : ℕ∞ω) (iteratedDeriv n F) := by
            simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv n hF)
          exact (hcf.differentiable (by simp)).differentiableAt.hasDerivAt)
      (hKint 0 (by omega))
      (by
        have hc : Continuous (deriv (iteratedDeriv n F)) := by
          have hcf : ContDiff ℝ (∞ : ℕ∞ω) (iteratedDeriv n F) := by
            simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv n hF)
          exact (contDiff_infty_iff_deriv.mp hcf).2.continuous
        exact hc.intervalIntegrable 0 1)
    have hboundary : K 0 1 * iteratedDeriv n F 1 - K 0 0 * iteratedDeriv n F 0 = 0 := by
      rw [hzeroN.2, hzeroN.1]
      ring
    let Kshift : ℕ → ℝ → ℝ := fun j x => K (j+1) x
    have hzero' : ∀ j < n, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0 := by
      intro j hj
      exact hzero j (by omega)
    have hKderiv' : ∀ j < n, ∀ x ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (Kshift j) (Kshift (j+1) x) x := by
      intro j hj x hx
      simpa [Kshift, Nat.add_assoc] using hKderiv (j+1) (by omega) x hx
    have hKint' : ∀ j < n, IntervalIntegrable (Kshift (j+1)) volume 0 1 := by
      intro j hj
      simpa [Kshift, Nat.add_assoc] using hKint (j+1) (by omega)
    have hrec := ih (K := Kshift) hzero' hKderiv' hKint'
    have hderivF : iteratedDeriv (n+1) F = deriv (iteratedDeriv n F) := iteratedDeriv_succ
    have hrec' : (∫ x in (0:ℝ)..1, K 1 x * iteratedDeriv n F x) =
        (-1:ℝ)^n * (∫ x in (0:ℝ)..1, K (n+1) x * F x) := by
      simpa [Kshift] using hrec
    rw [hboundary] at hstep
    rw [← hderivF] at hstep
    rw [hrec'] at hstep
    rw [pow_succ]
    nlinarith

open BrownianSharp.AlignmentFractionalKernel

/-- Closed form for the `j`th derivative of the shifted fractional kernel. -/
def fractionalKernelDerivative (β t : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  (Real.Gamma β)⁻¹ * (-1:ℝ)^j *
    (descPochhammer ℝ j).eval (β-1) * (t-u)^(β-1-(j:ℝ))

theorem fractionalKernelDerivative_zero (β t u : ℝ) :
    fractionalKernelDerivative β t 0 u = kernel β (t-u) := by
  simp [fractionalKernelDerivative, kernel]

theorem fractionalKernelDerivative_succ_deriv (β t : ℝ) (j : ℕ) (u : ℝ)
    (hu : t-u ≠ 0) :
    HasDerivAt (fractionalKernelDerivative β t j)
      (fractionalKernelDerivative β t (j+1) u) u := by
  let e : ℝ := β-1-(j:ℝ)
  let c : ℝ := (Real.Gamma β)⁻¹ * (-1:ℝ)^j *
    (descPochhammer ℝ j).eval (β-1)
  have hpow := Real.hasDerivAt_rpow_const (x := t-u) (p := e) (Or.inl hu)
  have hsub : HasDerivAt (fun x : ℝ => t-x) (-1) u := by
    have hneg : HasDerivAt (fun x : ℝ => -x) (-1) u := (hasDerivAt_id u).neg
    have hadd := (hasDerivAt_const u t).add hneg
    convert hadd using 1 <;> norm_num
  have hcomp := hpow.comp u hsub
  have hscaled : HasDerivAt (fun x : ℝ => c * (t-x)^e)
      (c * (e * (t-u)^(e-1) * -1)) u := hcomp.const_mul c
  have hcoeff : c * (e * (t-u)^(e-1) * -1) = fractionalKernelDerivative β t (j+1) u := by
    dsimp [c, e, fractionalKernelDerivative]
    rw [descPochhammer_succ_right, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast]
    push_cast
    rw [pow_succ]
    ring
  rw [← hcoeff]
  convert hscaled using 1
  funext x
  simp [fractionalKernelDerivative, c, e]

theorem iteratedDeriv_eq_fractionalKernelDerivative (β t : ℝ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun x => kernel β (t-x)) u = fractionalKernelDerivative β t j u := by
  have hcomp := iteratedDeriv_comp_const_sub (n := j)
    (f := fun z : ℝ => z^(β-1)) (s := t)
  have hrpow : iteratedDeriv j (fun z : ℝ => z^(β-1)) (t-u) =
      (descPochhammer ℝ j).eval (β-1) * (t-u)^(β-1-(j:ℝ)) := by
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const (β-1) (t-u) j
  simp only [kernel, iteratedDeriv_const_mul_field]
  rw [congrFun hcomp u]
  rw [hrpow]
  simp [fractionalKernelDerivative, smul_eq_mul, mul_assoc]

theorem fractionalKernelDerivative_continuousOn {β t : ℝ} (ht : 2 ≤ t) (j : ℕ) :
    ContinuousOn (fractionalKernelDerivative β t j) (Set.uIcc (0:ℝ) 1) := by
  let e : ℝ := β-1-(j:ℝ)
  have hbase : ContinuousOn (fun u : ℝ => t-u) (Set.uIcc (0:ℝ) 1) :=
    continuousOn_const.sub continuousOn_id
  have hpow : ContinuousOn (fun u : ℝ => (t-u)^e) (Set.uIcc (0:ℝ) 1) :=
    hbase.rpow_const (by
      intro u hu
      left
      have huIcc : u ∈ Set.Icc (0:ℝ) 1 := by
        simpa [Set.uIcc, min_eq_left (show (0:ℝ) ≤ 1 by norm_num),
          max_eq_right (show (0:ℝ) ≤ 1 by norm_num)] using hu
      have hu1 : u ≤ 1 := huIcc.2
      linarith)
  let c : ℝ := (Real.Gamma β)⁻¹ * (-1:ℝ)^j * (descPochhammer ℝ j).eval (β-1)
  change ContinuousOn (fun u => c * (t-u)^e) _
  exact continuousOn_const.mul hpow

theorem fractionalKernelDerivative_intervalIntegrable {β t : ℝ} (ht : 2 ≤ t) (j : ℕ) :
    IntervalIntegrable (fractionalKernelDerivative β t j) volume 0 1 :=
  (fractionalKernelDerivative_continuousOn ht j).intervalIntegrable

/-- The finite-interval transfer identity for the genuine RL kernel. -/
theorem fractionalKernel_transfer {β t : ℝ} (ht : 2 ≤ t) (q : ℕ)
    (F : ℝ → ℝ) (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j < q, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0) :
    (∫ u in (0:ℝ)..1, kernel β (t-u) * iteratedDeriv q F u) =
      (-1:ℝ)^q * (∫ u in (0:ℝ)..1,
        fractionalKernelDerivative β t q u * F u) := by
  let K : ℕ → ℝ → ℝ := fun j u => fractionalKernelDerivative β t j u
  have hKd : ∀ j < q, ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (K j) (K (j+1) u) u := by
    intro j hj u hu
    have huIcc : u ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc, min_eq_left (show (0:ℝ) ≤ 1 by norm_num),
        max_eq_right (show (0:ℝ) ≤ 1 by norm_num)] using hu
    have hut : u ≤ 1 := huIcc.2
    have hu0 : 0 ≤ u := huIcc.1
    have hpos : 0 < t-u := by linarith
    have hne : t-u ≠ 0 := ne_of_gt hpos
    exact fractionalKernelDerivative_succ_deriv β t j u hne
  have hKi : ∀ j < q, IntervalIntegrable (K (j+1)) volume 0 1 := by
    intro j hj
    simpa [K] using fractionalKernelDerivative_intervalIntegrable ht (j+1)
  have htrans := transfer_derivative_sequence q K F hF hzero hKd hKi
  simpa [K, fractionalKernelDerivative_zero] using htrans

/-- Compact support past one lets the global causal RL integral reduce to the
unit-interval kernel pairing, where q integrations by parts expose the decaying
qth kernel derivative. -/
theorem rlIntegral_tail_transfer {β t : ℝ} (hβ : 1/2 < β) (ht : 2 ≤ t)
    (q : ℕ) (F : ℝ → ℝ) (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j < q, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0)
    (hsupport : ∀ u, 1 ≤ u → iteratedDeriv q F u = 0) :
    rlIntegral β (iteratedDeriv q F) t =
      (-1:ℝ)^q * (∫ u in (0:ℝ)..1,
        fractionalKernelDerivative β t q u * F u) := by
  have hFq : Continuous (iteratedDeriv q F) := by
    simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv q hF).continuous
  let φ : ℝ → ℝ := fun u => kernel β (t-u) * iteratedDeriv q F u
  have ht1 : 1 ≤ t := by linarith
  have hwhole : IntervalIntegrable φ volume 0 t := by
    simpa [φ] using rlIntegrand_intervalIntegrable hβ hFq
  have h01 : Set.uIcc (0:ℝ) 1 ⊆ Set.uIcc (0:ℝ) t := by
    intro u hu
    have huI : u ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc, min_eq_left (show (0:ℝ) ≤ 1 by norm_num),
        max_eq_right (show (0:ℝ) ≤ 1 by norm_num)] using hu
    have htI : u ∈ Set.Icc (0:ℝ) t := ⟨huI.1, le_trans huI.2 ht1⟩
    simpa [Set.uIcc, min_eq_left (show (0:ℝ) ≤ t by linarith),
      max_eq_right (show (0:ℝ) ≤ t by linarith)] using htI
  have h1t : Set.uIcc 1 t ⊆ Set.uIcc (0:ℝ) t := by
    intro u hu
    have huI : u ∈ Set.Icc 1 t := by
      change u ∈ Set.uIcc 1 t at hu
      rw [Set.uIcc_of_le ht1] at hu
      exact hu
    have htI : u ∈ Set.Icc (0:ℝ) t := ⟨by linarith [huI.1], huI.2⟩
    simpa [Set.uIcc, min_eq_left (show (0:ℝ) ≤ t by linarith),
      max_eq_right (show (0:ℝ) ≤ t by linarith)] using htI
  have h01int : IntervalIntegrable φ volume 0 1 := hwhole.mono_set h01
  have h1tint : IntervalIntegrable φ volume 1 t := hwhole.mono_set h1t
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h01int h1tint
  have htail : (∫ u in (1:ℝ)..t, φ u) = 0 := by
    calc
      (∫ u in (1:ℝ)..t, φ u) = ∫ u in (1:ℝ)..t, (fun _ : ℝ => 0) u := by
        apply intervalIntegral.integral_congr
        intro u hu
        have huI : u ∈ Set.Icc 1 t := by
          change u ∈ Set.uIcc 1 t at hu
          rw [Set.uIcc_of_le ht1] at hu
          exact hu
        have hz := hsupport u huI.1
        simp [φ, hz]
      _ = 0 := by simp
  rw [show rlIntegral β (iteratedDeriv q F) t = ∫ u in (0:ℝ)..t, φ u by rfl]
  rw [← hsplit, htail]
  simp only [add_zero, φ]
  exact fractionalKernel_transfer ht q F hF hzero

theorem kernel_scale {β c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    kernel β x = c^(1-β) * kernel β (c*x) := by
  unfold kernel
  rw [Real.mul_rpow hc.le hx]
  have he : (1-β)+(β-1) = 0 := by ring
  calc
    (Real.Gamma β)⁻¹ * x^(β-1) =
        (c^(1-β) * c^(β-1)) * ((Real.Gamma β)⁻¹ * x^(β-1)) := by
          rw [← Real.rpow_add hc, he, Real.rpow_zero]
          ring
    _ = c^(1-β) * ((Real.Gamma β)⁻¹ * (c^(β-1) * x^(β-1))) := by ring

/-- Scaling a causal RL input by `c` scales its order-β integral by
`c^(q−β)` when the input itself carries q derivative factors. -/
theorem rlIntegral_dilate {β c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (q : ℕ) (F : ℝ → ℝ) :
    rlIntegral β (fun u => c^q * F (c*u)) t =
      c^((q:ℝ)-β) * rlIntegral β F (c*t) := by
  let H : ℝ → ℝ := fun x => kernel β (c*t-x) * F x
  have hscale : ∀ u ∈ Set.uIcc (0:ℝ) t,
      kernel β (t-u) * (c^q * F (c*u)) =
        c^((q:ℝ)+1-β) * H (c*u) := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0:ℝ) t := by
      simpa [Set.uIcc, min_eq_left ht, max_eq_right ht] using hu
    have hx : 0 ≤ t-u := by linarith [huIcc.2]
    have hker := kernel_scale (β := β) hc hx
    have hnat : (c^q : ℝ) = c^(q:ℝ) := by norm_cast
    have hpow : c^(1-β) * c^(q:ℝ) = c^((q:ℝ)+1-β) := by
      rw [← Real.rpow_add hc]
      congr 1
      ring
    dsimp [H]
    rw [hker, hnat]
    rw [show c * (t-u) = c*t-c*u by ring]
    calc
      c^(1-β) * kernel β (c*t-c*u) * (c^(q:ℝ) * F (c*u)) =
          (c^(1-β) * c^(q:ℝ)) * (kernel β (c*t-c*u) * F (c*u)) := by ring
      _ = c^((q:ℝ)+1-β) * (kernel β (c*t-c*u) * F (c*u)) := by rw [hpow]
  calc
    rlIntegral β (fun u => c^q * F (c*u)) t =
        ∫ u in (0:ℝ)..t, c^((q:ℝ)+1-β) * H (c*u) := by
      unfold rlIntegral
      apply intervalIntegral.integral_congr
      intro u hu
      exact hscale u hu
    _ = c^((q:ℝ)+1-β) * (∫ u in (0:ℝ)..t, H (c*u)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = c^((q:ℝ)+1-β) * (c⁻¹ * (∫ x in (0:ℝ)..c*t, H x)) := by
      rw [intervalIntegral.integral_comp_mul_left H hc.ne']
      simp [smul_eq_mul]
    _ = c^((q:ℝ)-β) * rlIntegral β F (c*t) := by
      rw [show (∫ x in (0:ℝ)..c*t, H x) = rlIntegral β F (c*t) by rfl]
      calc
        c^((q:ℝ)+1-β) * (c⁻¹ * rlIntegral β F (c*t)) =
            (c^((q:ℝ)+1-β) * c⁻¹) * rlIntegral β F (c*t) := by ring
        _ = c^((q:ℝ)-β) * rlIntegral β F (c*t) := by
          rw [← Real.rpow_neg_one c, ← Real.rpow_add hc]
          congr 1
          ring

/-- Exact finite-horizon energy scaling for a dilated causal preimage. -/
theorem rlIntegral_dilate_energy {α β c : ℝ} (q : ℕ)
    (hα : β = (q:ℝ)-α) (hc : 0 < c) (F : ℝ → ℝ) :
    (∫ t in (0:ℝ)..1,
      (rlIntegral β (fun u => c^q * F (c*u)) t)^2) =
      c^(2*α-1) * (∫ x in (0:ℝ)..c, (rlIntegral β F x)^2) := by
  have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1,
      rlIntegral β (fun u => c^q * F (c*u)) t = c^α * rlIntegral β F (c*t) := by
    intro t ht
    rw [rlIntegral_dilate hc ht.1 q F]
    have hexp : (q:ℝ)-β = α := by rw [hα]; ring
    rw [hexp]
  calc
    (∫ t in (0:ℝ)..1,
      (rlIntegral β (fun u => c^q * F (c*u)) t)^2) =
      ∫ t in (0:ℝ)..1, (c^α * rlIntegral β F (c*t))^2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := by
          simpa [Set.uIcc, min_eq_left (show (0:ℝ) ≤ 1 by norm_num),
            max_eq_right (show (0:ℝ) ≤ 1 by norm_num)] using ht
        change (rlIntegral β (fun u => c^q * F (c*u)) t)^2 = _
        rw [hpoint t htI]
    _ = c^(2*α) * (∫ t in (0:ℝ)..1, (rlIntegral β F (c*t))^2) := by
      have hmul : ∀ t, (c^α * rlIntegral β F (c*t))^2 =
          c^(2*α) * (rlIntegral β F (c*t))^2 := by
        intro t
        rw [mul_pow]
        have hp : (c^α)^2 = c^(2*α) := by
          rw [show (c^α)^2 = c^α * c^α by ring, ← Real.rpow_add hc]
          congr 1
          ring
        rw [hp]
      calc
        (∫ t in (0:ℝ)..1, (c^α * rlIntegral β F (c*t))^2) =
            ∫ t in (0:ℝ)..1, c^(2*α) * (rlIntegral β F (c*t))^2 := by
              apply intervalIntegral.integral_congr
              intro t ht
              exact hmul t
        _ = c^(2*α) * (∫ t in (0:ℝ)..1, (rlIntegral β F (c*t))^2) :=
              by rw [intervalIntegral.integral_const_mul]
    _ = c^(2*α-1) * (∫ x in (0:ℝ)..c, (rlIntegral β F x)^2) := by
      rw [intervalIntegral.integral_comp_mul_left (f := fun x => (rlIntegral β F x)^2) hc.ne']
      simp only [smul_eq_mul]
      rw [show c*0 = 0 by ring, show c*1 = c by ring]
      calc
        c^(2*α) * (c⁻¹ * (∫ x in (0:ℝ)..c, (rlIntegral β F x)^2)) =
            (c^(2*α) * c⁻¹) * (∫ x in (0:ℝ)..c, (rlIntegral β F x)^2) := by ring
        _ = c^(2*α-1) * (∫ x in (0:ℝ)..c, (rlIntegral β F x)^2) := by
          rw [← Real.rpow_neg_one c, ← Real.rpow_add hc]
          congr 1

/-- Causal translation of a left-supported input: shifting the input right by
`a` delays its RL profile by exactly `a`. -/
theorem rlIntegral_shift_right {β a t : ℝ} (hβ : 1/2 < β) (ha : 0 ≤ a)
    (ht : 0 ≤ t) (F : ℝ → ℝ) (hF : Continuous F)
    (hleft : ∀ x ≤ 0, F x = 0) :
    rlIntegral β (fun u => F (u-a)) t =
      if t ≤ a then 0 else rlIntegral β F (t-a) := by
  by_cases hta : t ≤ a
  · rw [if_pos hta]
    unfold rlIntegral
    calc
      (∫ u in (0:ℝ)..t, kernel β (t-u) * F (u-a)) =
          ∫ u in (0:ℝ)..t, (fun _ : ℝ => 0) u := by
        apply intervalIntegral.integral_congr
        intro u hu
        have huI : u ∈ Set.Icc (0:ℝ) t := by
          rw [Set.uIcc_of_le ht] at hu
          exact hu
        have harg : u-a ≤ 0 := by linarith [huI.2, hta]
        simp [hleft (u-a) harg]
      _ = 0 := by simp
  · have hat : a < t := lt_of_not_ge hta
    rw [if_neg (not_le.mpr hat)]
    let φ : ℝ → ℝ := fun u => kernel β (t-u) * F (u-a)
    have hwhole : IntervalIntegrable φ volume 0 t := by
      simpa [φ] using rlIntegrand_intervalIntegrable hβ
        (hF.comp (continuous_id.sub continuous_const))
    have h01 : IntervalIntegrable φ volume 0 a := by
      apply hwhole.mono_set
      intro u hu
      have haI : u ∈ Set.Icc (0:ℝ) a := by
        rw [Set.uIcc_of_le ha] at hu
        exact hu
      rw [Set.uIcc_of_le ht]
      exact ⟨haI.1, le_trans haI.2 hat.le⟩
    have hAt : IntervalIntegrable φ volume a t := by
      apply hwhole.mono_set
      intro u hu
      have huI : u ∈ Set.Icc a t := by
        rw [Set.uIcc_of_le hat.le] at hu
        exact hu
      rw [Set.uIcc_of_le ht]
      exact ⟨le_trans ha huI.1, huI.2⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals h01 hAt
    have hzero : (∫ u in (0:ℝ)..a, φ u) = 0 := by
      calc
        (∫ u in (0:ℝ)..a, φ u) = ∫ u in (0:ℝ)..a, (fun _ : ℝ => 0) u := by
          apply intervalIntegral.integral_congr
          intro u hu
          have huI : u ∈ Set.Icc (0:ℝ) a := by
            rw [Set.uIcc_of_le ha] at hu
            exact hu
          have harg : u-a ≤ 0 := by linarith [huI.2]
          simp [φ, hleft (u-a) harg]
        _ = 0 := by simp
    have hshift : (∫ u in a..t, φ u) = rlIntegral β F (t-a) := by
      unfold rlIntegral
      have hcomp := intervalIntegral.integral_comp_add_right
        (a := (0:ℝ)) (b := t-a) (f := φ) a
      have hcomp' : (∫ x in (0:ℝ)..t-a, φ (x+a)) = ∫ x in a..t, φ x := by
        simpa using hcomp
      rw [← hcomp']
      apply intervalIntegral.integral_congr
      intro v hv
      change kernel β (t-(v+a)) * F ((v+a)-a) =
        kernel β (t-a-v) * F v
      rw [show t-(v+a)=t-a-v by ring, show (v+a)-a=v by ring]
    rw [show rlIntegral β (fun u => F (u-a)) t = ∫ u in (0:ℝ)..t, φ u by rfl]
    rw [← hsplit, hzero, hshift]
    simp

/-- Combining causal translation with dilation gives the precise shifted
preimage formula used for dyadic smooth atoms. -/
theorem rlIntegral_dilate_shift {β c m t : ℝ} (hβ : 1/2 < β) (hc : 0 < c)
    (hm : 0 ≤ m) (ht : 0 ≤ t) (q : ℕ) (F : ℝ → ℝ)
    (hF : Continuous F) (hleft : ∀ x ≤ 0, F x = 0) :
    rlIntegral β (fun u => c^q * F (c*u-m)) t =
      if t ≤ m/c then 0 else c^((q:ℝ)-β) * rlIntegral β F (c*t-m) := by
  let H : ℝ → ℝ := fun x => F (c*x)
  have hH : Continuous H := hF.comp (continuous_const.mul continuous_id)
  have hHleft : ∀ x ≤ 0, H x = 0 := by
    intro x hx
    apply hleft
    exact mul_nonpos_of_nonneg_of_nonpos hc.le hx
  have ha : 0 ≤ m/c := div_nonneg hm hc.le
  have hmul : rlIntegral β (fun u => c^q * H (u-m/c)) t =
      c^q * rlIntegral β (fun u => H (u-m/c)) t := by
    unfold rlIntegral
    calc
      (∫ u in (0:ℝ)..t, kernel β (t-u) * (c^q * H (u-m/c))) =
          ∫ u in (0:ℝ)..t, c^q * (kernel β (t-u) * H (u-m/c)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            ring
      _ = c^q * (∫ u in (0:ℝ)..t, kernel β (t-u) * H (u-m/c)) := by
            rw [intervalIntegral.integral_const_mul]
  have hshift := rlIntegral_shift_right hβ ha ht H hH hHleft
  have harg : (fun u => F (c*u-m)) = fun u => H (u-m/c) := by
    funext u
    dsimp [H]
    congr 1
    field_simp
  have harg' : (fun u => c^q * F (c*u-m)) =
      fun u => c^q * H (u-m/c) := by
    funext u
    change c^q * F (c*u-m) = c^q * F (c*(u-m/c))
    congr 1
    field_simp
  rw [harg', hmul, hshift]
  by_cases hta : t ≤ m/c
  · simp [hta]
  · have hat : m/c < t := lt_of_not_ge hta
    have hscale := rlIntegral_dilate (β := β) (c := c) (t := t-m/c)
      hc (le_of_lt (by linarith)) 0 F
    have harg' : c*(t-m/c) = c*t-m := by field_simp
    have hscale' : rlIntegral β H (t-m/c) = c^(-β) * rlIntegral β F (c*t-m) := by
      simpa [H, harg'] using hscale
    have hpow : c^q * c^(-β) = c^((q:ℝ)-β) := by
      have hq : (c^q : ℝ) = c^(q:ℝ) := by norm_cast
      rw [hq, ← Real.rpow_add hc]
      congr 1
    simp only [if_neg hta]
    rw [hscale']
    calc
      c^q * (c^(-β) * rlIntegral β F (c*t-m)) =
          (c^q * c^(-β)) * rlIntegral β F (c*t-m) := by ring
      _ = c^((q:ℝ)-β) * rlIntegral β F (c*t-m) := by rw [hpow]

/-- On the unit support, q derivatives of the order-(q−α) kernel decay with
the sharp power t^(−α−1). -/
theorem fractionalKernelDerivative_tail_bound {α β t : ℝ} (hα : 1/2 < α)
    (ht : 2 ≤ t) (q : ℕ) (hβq : β = (q:ℝ)-α) (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    |fractionalKernelDerivative β t q u| ≤
      |(Real.Gamma β)⁻¹ * (-1:ℝ)^q * (descPochhammer ℝ q).eval (β-1)| *
        (t/2)^(-α-1) := by
  let C : ℝ := (Real.Gamma β)⁻¹ * (-1:ℝ)^q *
    (descPochhammer ℝ q).eval (β-1)
  have hpos : 0 < t-u := by linarith [hu.2]
  have htpos : 0 < t/2 := by linarith
  have hle : t/2 ≤ t-u := by linarith [hu.2]
  have hz : -α-1 ≤ 0 := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos htpos hle hz
  have hexp : β-1-(q:ℝ) = -α-1 := by rw [hβq]; push_cast; ring
  have hformula : fractionalKernelDerivative β t q u = C * (t-u)^(-α-1) := by
    simp [fractionalKernelDerivative, C, hexp]
  rw [hformula, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  have hC : 0 ≤ |C| := abs_nonneg _
  calc
    |C| * (t-u)^(-α-1) ≤ |C| * (t/2)^(-α-1) := mul_le_mul_of_nonneg_left hpow hC
    _ = |(Real.Gamma β)⁻¹ * (-1:ℝ)^q * (descPochhammer ℝ q).eval (β-1)| *
        (t/2)^(-α-1) := by rfl

/-- The transferred tail integral is bounded by a constant times t^(−α−1).
This yields a square-integrable tail for every α>1/2. -/
theorem rlIntegral_tail_decay {α β t : ℝ} (hα : 1/2 < α) (hβ : 1/2 < β)
    (ht : 2 ≤ t) (q : ℕ) (hβq : β = (q:ℝ)-α) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j < q, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0)
    (hsupport : ∀ u, 1 ≤ u → iteratedDeriv q F u = 0) :
    |rlIntegral β (iteratedDeriv q F) t| ≤
      |(Real.Gamma β)⁻¹ * (-1:ℝ)^q * (descPochhammer ℝ q).eval (β-1)| *
        (t/2)^(-α-1) * (∫ u in (0:ℝ)..1, |F u|) := by
  rw [rlIntegral_tail_transfer hβ ht q F hF hzero hsupport, abs_mul]
  have hsign : |(-1:ℝ)^q| = 1 := by simp
  rw [hsign]
  simp only [one_mul]
  let K : ℝ → ℝ := fractionalKernelDerivative β t q
  let B : ℝ := |(Real.Gamma β)⁻¹ * (-1:ℝ)^q *
    (descPochhammer ℝ q).eval (β-1)| * (t/2)^(-α-1)
  have hFcont : ContinuousOn F (Set.uIcc (0:ℝ) 1) := hF.continuous.continuousOn
  have hKcont : ContinuousOn K (Set.uIcc (0:ℝ) 1) := by
    exact fractionalKernelDerivative_continuousOn ht q
  have hleft : IntervalIntegrable (fun u => |K u * F u|) volume 0 1 :=
    (hKcont.mul hFcont).abs.intervalIntegrable
  have hright : IntervalIntegrable (fun u => B * |F u|) volume 0 1 := by
    exact (continuousOn_const.mul hFcont.abs).intervalIntegrable
  have hmono : ∀ u ∈ Set.Icc (0:ℝ) 1, |K u * F u| ≤ B * |F u| := by
    intro u hu
    have hK := fractionalKernelDerivative_tail_bound hα ht q hβq u hu
    dsimp [K, B]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hK (abs_nonneg _)
  have hint := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    hleft hright hmono
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := fun u => K u * F u) (a := (0:ℝ)) (b := 1)
    (by norm_num)
  calc
    |∫ u in (0:ℝ)..1, K u * F u| ≤ ∫ u in (0:ℝ)..1, |K u * F u| := habs
    _ ≤ ∫ u in (0:ℝ)..1, B * |F u| := hint
    _ = B * (∫ u in (0:ℝ)..1, |F u|) := by rw [← intervalIntegral.integral_const_mul]
    _ = |(Real.Gamma β)⁻¹ * (-1:ℝ)^q * (descPochhammer ℝ q).eval (β-1)| *
        (t/2)^(-α-1) * (∫ u in (0:ℝ)..1, |F u|) := rfl

/-- A continuous input has a continuous causal RL profile on every finite
time interval, by rescaling that interval to the unit interval operator. -/
theorem rlIntegral_continuousOn_compact {β : ℝ} (hβ : 1/2 < β)
    (F : ℝ → ℝ) (hF : Continuous F) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (fun t => rlIntegral β F t) (Set.Icc (0:ℝ) T) := by
  let p : C(UnitInterval, ℝ) :=
    ⟨fun x => T^β * F (T*x.1),
      continuous_const.mul (hF.comp (continuous_const.mul continuous_subtype_val))⟩
  let R : C(UnitInterval, ℝ) :=
    BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ p
  let H : ℝ → ℝ := fun t => R (clipUnit (t/T))
  have hH : Continuous H := by
    exact R.continuous.comp
      (BrownianSharp.AlignmentFractionalL2.clipUnit_continuous.comp
        (continuous_id.div_const T))
  have hEq : ∀ t ∈ Set.Icc (0:ℝ) T, rlIntegral β F t = H t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ T := ht.2
    have hc : 0 < T := hT
    have htr : t/T ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact div_nonneg ht0 hc.le
      · rw [div_le_iff₀ hc]
        simpa using ht1
    have hclip : clipUnit (t/T) = ⟨t/T, htr⟩ := by
      apply Subtype.ext
      simp [clipUnit, max_eq_right htr.1, min_eq_right htr.2]
    change rlIntegral β F t = R (clipUnit (t/T))
    rw [hclip]
    change rlIntegral β F t =
      BrownianSharp.AlignmentFractionalTranslation.fractionalRL β hβ
        (BrownianSharp.AlignmentFractionalDensity.profileToL2 p) ⟨t/T, htr⟩
    rw [BrownianSharp.AlignmentFractionalDensity.fractionalRL_profile
      β hβ p (t/T) htr.1 htr.2]
    have hinput : rlIntegral β (fun u => p (clipUnit u)) (t/T) =
        rlIntegral β (fun u => T^β * F (T*u)) (t/T) := by
      unfold rlIntegral
      apply intervalIntegral.integral_congr
      intro u hu
      have huI : u ∈ Set.Icc (0:ℝ) (t/T) := by
        rw [Set.uIcc_of_le htr.1] at hu
        exact hu
      have hu0 : 0 ≤ u := huI.1
      have hut : u ≤ t/T := huI.2
      have hu1 : u ≤ 1 := le_trans hut htr.2
      have hcl : (clipUnit u).1 = u := by simp [clipUnit, max_eq_right hu0, min_eq_right hu1]
      simp [p, hcl]
    rw [hinput]
    have hscale := rlIntegral_dilate (β := β) (c := T) (t := t/T)
      hc htr.1 0 F
    have hscale' : rlIntegral β (fun u => F (T*u)) (t/T) =
        T^(-β) * rlIntegral β F t := by
      have harg : T * (t/T) = t := by field_simp
      simpa [harg] using hscale
    have hscalar : rlIntegral β (fun u => T^β * F (T*u)) (t/T) =
        T^β * rlIntegral β (fun u => F (T*u)) (t/T) := by
      unfold rlIntegral
      calc
        (∫ u in (0:ℝ)..t/T, kernel β (t/T-u) * (T^β * F (T*u))) =
            ∫ u in (0:ℝ)..t/T, T^β * (kernel β (t/T-u) * F (T*u)) := by
              apply intervalIntegral.integral_congr
              intro u hu
              ring
        _ = T^β * (∫ u in (0:ℝ)..t/T, kernel β (t/T-u) * F (T*u)) :=
              by rw [intervalIntegral.integral_const_mul]
    rw [hscalar]
    rw [hscale']
    have hp : T^β * T^(-β) = 1 := by
      rw [← Real.rpow_add hT]
      simp
    rw [← mul_assoc, hp, one_mul]
  refine hH.continuousOn.congr ?_
  intro t ht
  exact hEq t ht

/-- The finite-horizon energy of a shifted, dilated causal atom is exactly its
base energy on the portion of the support visible before time `c`. -/
theorem rlIntegral_dilate_shift_energy {α β c m : ℝ} (q : ℕ)
    (hαβ : β = (q:ℝ)-α) (hc : 0 < c) (hm : 0 ≤ m) (hmc : m ≤ c)
    (hβ : 1/2 < β) (F : ℝ → ℝ) (hF : Continuous F)
    (hleft : ∀ x ≤ 0, F x = 0) :
    (∫ t in (0:ℝ)..1,
      (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2) =
      c^(2*α-1) *
        (∫ x in (0:ℝ)..(c-m), (rlIntegral β F x)^2) := by
  let a : ℝ := m/c
  have ha0 : 0 ≤ a := by dsimp [a]; exact div_nonneg hm hc.le
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_iff₀ hc]
    simpa using hmc
  have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1,
      rlIntegral β (fun u => c^q * F (c*u-m)) t =
        if t ≤ a then 0 else c^α * rlIntegral β F (c*t-m) := by
    intro t ht
    rw [rlIntegral_dilate_shift hβ hc hm ht.1 q F hF hleft]
    have hexp : (q:ℝ)-β = α := by rw [hαβ]; ring
    rw [hexp]
  have hsplit :
      (∫ t in (0:ℝ)..1,
        (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2) =
      (∫ t in (0:ℝ)..a,
        (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2) +
      (∫ t in a..1,
        (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2) := by
    let g : ℝ → ℝ := fun t => (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2
    have hcont : ContinuousOn g (Set.Icc (0:ℝ) 1) := by
      have h := rlIntegral_continuousOn_compact hβ
        (fun u => c^q * F (c*u-m))
        (continuous_const.mul (hF.comp
          ((continuous_const.mul continuous_id).sub continuous_const))) 1 (by norm_num)
      change ContinuousOn (fun t =>
        (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2) _
      exact h.pow 2
    have hcont' : ContinuousOn g (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hcont
    have hwhole : IntervalIntegrable g volume 0 1 := hcont'.intervalIntegrable
    have h01 : IntervalIntegrable g volume 0 a := by
      apply hwhole.mono_set
      intro t ht
      have htI : t ∈ Set.Icc (0:ℝ) a := by
        rw [Set.uIcc_of_le ha0] at ht
        exact ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨htI.1, le_trans htI.2 ha1⟩
    have h12 : IntervalIntegrable g volume a 1 := by
      apply hwhole.mono_set
      intro t ht
      have htI : t ∈ Set.Icc a 1 := by
        rw [Set.uIcc_of_le ha1] at ht
        exact ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨le_trans ha0 htI.1, htI.2⟩
    simpa [g] using (intervalIntegral.integral_add_adjacent_intervals h01 h12).symm
  have hzero : (∫ t in (0:ℝ)..a,
      (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2) = 0 := by
    calc
      _ = ∫ t in (0:ℝ)..a, (fun _ : ℝ => (0:ℝ)) t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc (0:ℝ) a := by
          rw [Set.uIcc_of_le ha0] at ht
          exact ht
        have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨htI.1, le_trans htI.2 ha1⟩
        change (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2 = (0:ℝ)
        rw [hpoint t ht01]
        simp [show t ≤ a from htI.2]
      _ = 0 := by simp
  have hright :
      (∫ t in a..1,
        (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2) =
      c^(2*α) * (∫ t in a..1, (rlIntegral β F (c*t-m))^2) := by
    have hmul : ∀ t, (c^α * rlIntegral β F (c*t-m))^2 =
        c^(2*α) * (rlIntegral β F (c*t-m))^2 := by
      intro t
      rw [mul_pow]
      have hp : (c^α)^2 = c^(2*α) := by
        rw [show (c^α)^2 = c^α * c^α by ring, ← Real.rpow_add hc]
        congr 1 <;> ring
      rw [hp]
    calc
      _ = ∫ t in a..1, (c^α * rlIntegral β F (c*t-m))^2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := by
          have ht' : t ∈ Set.uIcc a 1 := ht
          rw [Set.uIcc_of_le ha1] at ht'
          exact ⟨le_trans ha0 ht'.1, ht'.2⟩
        change (rlIntegral β (fun u => c^q * F (c*u-m)) t)^2 =
          (c^α * rlIntegral β F (c*t-m))^2
        rw [hpoint t htI]
        by_cases hta : t ≤ a
        · have hteq : t = a := le_antisymm hta (by
            have ht' : t ∈ Set.Icc a 1 := by
              rw [Set.uIcc_of_le ha1] at ht
              exact ht
            exact ht'.1)
          subst t
          have harg : c*a-m = 0 := by dsimp [a]; field_simp <;> ring
          simp [harg, rlIntegral]
        · simp [hta]
      _ = c^(2*α) * (∫ t in a..1, (rlIntegral β F (c*t-m))^2) := by
        calc
          _ = ∫ t in a..1, c^(2*α) * (rlIntegral β F (c*t-m))^2 := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact hmul t
          _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hsplit, hzero, zero_add, hright]
  have hcomp := intervalIntegral.integral_comp_mul_add
    (a := a) (b := (1:ℝ)) (f := fun x => (rlIntegral β F x)^2)
    (c := c) hc.ne' (-m)
  have hcomp' : (∫ t in a..1, (rlIntegral β F (c*t-m))^2) =
      c⁻¹ * (∫ x in (0:ℝ)..(c-m), (rlIntegral β F x)^2) := by
    have hc0 : c*a-m = 0 := by dsimp [a]; field_simp <;> ring
    have hc0' : c*a + -m = 0 := by linarith
    have hc1 : c*1-m = c-m := by ring
    simpa [smul_eq_mul, sub_eq_add_neg, hc0', hc1] using hcomp
  rw [hcomp']
  calc
    c^(2*α) * (c⁻¹ * (∫ x in (0:ℝ)..(c-m), (rlIntegral β F x)^2)) =
        (c^(2*α) * c⁻¹) * (∫ x in (0:ℝ)..(c-m), (rlIntegral β F x)^2) := by ring
    _ = _ := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hc]
      congr 1 <;> ring

/-- A nonzero smooth atom has a nonzero fractional-integral preimage in the
unit-interval source space. This obtains strict positivity from the exact
operator identity, without estimating a particular integral from below. -/
theorem smooth_atom_preimage_norm_pos (α : ℝ) (hα : 1/2 < α) (q : ℕ)
    (hqα : α < q) (hqβ : 1/2 < (q:ℝ)-α) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j ≤ q, iteratedDeriv j F 0 = 0)
    (hout : BrownianSharp.AlignmentFractionalDensity.restrictProfile F hF.continuous ≠ 0) :
    0 < ‖BrownianSharp.AlignmentFractionalDensity.profileToL2
      (BrownianSharp.AlignmentFractionalDensity.fractionalOnC ((q:ℝ)-α) hqβ
        (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q F hF))‖ := by
  apply norm_pos_iff.mpr
  intro hsource
  apply hout
  have hpre :=
    BrownianSharp.AlignmentFractionalDensity.smooth_atom_fractional_preimage_L2
      α hα q hqα hqβ F hF hzero
  have hmap : BrownianSharp.AlignmentFractionalTranslation.fractionalRL α hα
      (BrownianSharp.AlignmentFractionalDensity.profileToL2
        (BrownianSharp.AlignmentFractionalDensity.fractionalOnC ((q:ℝ)-α) hqβ
          (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q F hF))) = 0 := by
    rw [hsource, map_zero]
  calc
    BrownianSharp.AlignmentFractionalDensity.restrictProfile F hF.continuous =
        BrownianSharp.AlignmentFractionalTranslation.fractionalRL α hα
          (BrownianSharp.AlignmentFractionalDensity.profileToL2
            (BrownianSharp.AlignmentFractionalDensity.fractionalOnC ((q:ℝ)-α) hqβ
              (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q F hF))) := hpre.symm
    _ = 0 := hmap

/-- The canonical profile embedding preserves the squared `L²` energy on the
unit interval, written as a classical interval integral. -/
theorem profileToL2_norm_sq_interval
    (p : ContinuousMap UnitInterval ℝ) :
    ‖BrownianSharp.AlignmentFractionalDensity.profileToL2 p‖^2 =
      (∫ t in (0:ℝ)..1, (p (clipUnit t))^2) := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  let g : UnitL2 := BrownianSharp.AlignmentFractionalDensity.profileToL2 p
  have hnorm : ‖g‖^2 = ∫ u, (g u)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    congr 1
    funext u
    simp [pow_two]
  have hcoe := BrownianSharp.AlignmentFractionalDensity.profileToL2_coe p
  have hmeas : MeasurableSet UnitInterval := measurableSet_Icc
  have hset :
      (∫ u in UnitInterval, (g u)^2 ∂volume) =
        ∫ u in UnitInterval, (p (clipUnit u))^2 ∂volume := by
    apply integral_congr_ae
    filter_upwards [hcoe, ae_restrict_mem hmeas] with u huCoe hu
    rw [huCoe]
  have hinterval :
      (∫ u in UnitInterval, (p (clipUnit u))^2 ∂volume) =
        (∫ t in (0:ℝ)..1, (p (clipUnit t))^2) := by
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (μ := volume) (f :=
      fun t => (p (clipUnit t))^2) (by norm_num : (0:ℝ) ≤ 1)]
  calc
    ‖BrownianSharp.AlignmentFractionalDensity.profileToL2 p‖^2 = ‖g‖^2 := rfl
    _ = ∫ u, (g u)^2 ∂μ := hnorm
    _ = ∫ u in UnitInterval, (g u)^2 ∂volume := rfl
    _ = ∫ u in UnitInterval, (p (clipUnit u))^2 ∂volume := hset
    _ = ∫ t in (0:ℝ)..1, (p (clipUnit t))^2 := hinterval

/-- The smooth fractional preimage's source norm is exactly the energy of its
Riemann--Liouville profile, so the shifted scaling identity applies directly
to the Hilbert-space norm used in the entropy argument. -/
theorem smooth_atom_preimage_norm_sq_eq_energy {α β : ℝ} (hα : 1/2 < α)
    (q : ℕ) (hqα : α < q) (hβ : 1/2 < β)
    (hβq : β = (q:ℝ)-α) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F) :
    ‖BrownianSharp.AlignmentFractionalDensity.profileToL2
      (BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ
        (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q F hF))‖^2 =
      (∫ t in (0:ℝ)..1, (rlIntegral β (iteratedDeriv q F) t)^2) := by
  let d := BrownianSharp.AlignmentFractionalDensity.derivativeProfile q F hF
  let p := BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ d
  rw [profileToL2_norm_sq_interval p]
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Set.Icc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact ht
  have htclip : clipUnit t = ⟨t, htI⟩ := by
    apply Subtype.ext
    simp [clipUnit, max_eq_right htI.1, min_eq_right htI.2]
  have hprofile : p (clipUnit t) = rlIntegral β (iteratedDeriv q F) t := by
    rw [htclip]
    change BrownianSharp.AlignmentFractionalTranslation.fractionalRL β hβ
      (BrownianSharp.AlignmentFractionalDensity.profileToL2 d) ⟨t, htI⟩ = _
    rw [BrownianSharp.AlignmentFractionalDensity.fractionalRL_profile
      β hβ d t htI.1 htI.2]
    unfold rlIntegral
    apply intervalIntegral.integral_congr
    intro u hu
    have huI : u ∈ Set.Icc (0:ℝ) t := by
      rw [Set.uIcc_of_le htI.1] at hu
      exact hu
    have hu1 : u ≤ 1 := le_trans huI.2 htI.2
    have huclip : clipUnit u = ⟨u, ⟨huI.1, hu1⟩⟩ := by
      apply Subtype.ext
      simp [clipUnit, max_eq_right huI.1, min_eq_right hu1]
    dsimp [d, BrownianSharp.AlignmentFractionalDensity.derivativeProfile,
      BrownianSharp.AlignmentFractionalDensity.restrictProfile]
    rw [huclip]
  change (p (clipUnit t))^2 = (rlIntegral β (iteratedDeriv q F) t)^2
  rw [hprofile]

/-- The ordinary qth derivative of a shifted dilation carries the exact factor
`c^q`; no asymptotic comparison is used. -/
theorem iteratedDeriv_dilate_shift (q : ℕ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F) (c m : ℝ) :
    iteratedDeriv q (fun x => F (c*x-m)) =
      fun x => c^q * iteratedDeriv q F (c*x-m) := by
  let G : ℝ → ℝ := fun y => F (y-m)
  have hG : ContDiff ℝ (∞ : ℕ∞ω) G := hF.comp (contDiff_id.sub contDiff_const)
  have hscale := iteratedDeriv_comp_const_mul (n := q) (hG.of_le (by simp)) c
  have hshift : iteratedDeriv q G = fun y => iteratedDeriv q F (y-m) := by
    exact iteratedDeriv_comp_sub_const q F m
  calc
    iteratedDeriv q (fun x => F (c*x-m)) = iteratedDeriv q (fun x => G (c*x)) := by
      congr 1
    _ = fun x => c^q * iteratedDeriv q G (c*x) := hscale
    _ = fun x => c^q * iteratedDeriv q F (c*x-m) := by
      funext x
      rw [hshift]

/-- Every derivative of the concrete plateau atom vanishes to the left of its
support, using the explicit open zero neighborhood from its definition. -/
theorem smoothAtom_iteratedDeriv_zero_left (q : ℕ) {x : ℝ} (hx : x ≤ 0) :
    iteratedDeriv q BrownianSharp.smoothAtom x = 0 := by
  have heq : Set.EqOn BrownianSharp.smoothAtom (fun _ : ℝ => (0:ℝ))
      (Set.Iio (1/8:ℝ)) := by
    intro y hy
    exact BrownianSharp.smoothAtom_support_inner y (Or.inl (le_of_lt hy))
  have hx' : x ∈ Set.Iio (1/8:ℝ) := by change x < 1/8; linarith
  have hderiv := heq.iteratedDeriv_of_isOpen isOpen_Iio q hx'
  simpa using hderiv

/-- Every derivative of the concrete plateau atom vanishes to the right of
its support. -/
theorem smoothAtom_iteratedDeriv_zero_right (q : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    iteratedDeriv q BrownianSharp.smoothAtom x = 0 := by
  have heq : Set.EqOn BrownianSharp.smoothAtom (fun _ : ℝ => (0:ℝ))
      (Set.Ioi (7/8:ℝ)) := by
    intro y hy
    exact BrownianSharp.smoothAtom_support_inner y (Or.inr (le_of_lt hy))
  have hx' : x ∈ Set.Ioi (7/8:ℝ) := by change 7/8 < x; linarith
  have hderiv := heq.iteratedDeriv_of_isOpen isOpen_Ioi q hx'
  simpa using hderiv

/-- The actual atom has all derivatives zero at both endpoints and its qth
derivative vanishes beyond the unit interval. -/
theorem smoothAtom_fractional_atom_conditions (q : ℕ) :
    (∀ j < q, iteratedDeriv j BrownianSharp.smoothAtom 0 = 0 ∧
      iteratedDeriv j BrownianSharp.smoothAtom 1 = 0) ∧
    (∀ u, 1 ≤ u → iteratedDeriv q BrownianSharp.smoothAtom u = 0) ∧
    (∀ u ≤ 0, iteratedDeriv q BrownianSharp.smoothAtom u = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact ⟨smoothAtom_iteratedDeriv_zero_left j le_rfl,
      smoothAtom_iteratedDeriv_zero_right j le_rfl⟩
  · intro u hu
    exact smoothAtom_iteratedDeriv_zero_right q hu
  · intro u hu
    exact smoothAtom_iteratedDeriv_zero_left q hu

/-- Every derivative of a shifted dilation of the actual plateau atom vanishes
at the left endpoint, including the order needed by the fractional preimage. -/
theorem shiftedSmoothAtom_jets_zero (q : ℕ) {c m : ℝ}
    (hc : 0 < c) (hm : 0 ≤ m) :
    ∀ j ≤ q, iteratedDeriv j (fun x => BrownianSharp.smoothAtom (c*x-m)) 0 = 0 := by
  have hδ : 0 < 1/(8*c) := div_pos (by norm_num) (mul_pos (by norm_num) hc)
  have hloc : (fun x : ℝ => BrownianSharp.smoothAtom (c*x-m)) =ᶠ[𝓝 (0:ℝ)]
      (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds hδ] with x hx
    have hx' : x < 1/(8*c) := by simpa using hx
    have hcx : c*x < 1/8 := by
      have hmul := mul_lt_mul_of_pos_left hx' hc
      have heq : c*(1/(8*c)) = (1/8:ℝ) := by field_simp
      rw [heq] at hmul
      exact hmul
    have harg : c*x-m ≤ 1/8 := by linarith
    exact BrownianSharp.smoothAtom_support_inner (c*x-m) (Or.inl harg)
  intro j hj
  have hderiv := Filter.EventuallyEq.iteratedDeriv_eq j hloc
  simpa using hderiv

/-- Combining the genuine smooth-atom source with the exact shifted energy
identity gives the sharp dilation exponent in the Hilbert source norm. -/
theorem smooth_atom_shift_preimage_norm_sq {α β c m : ℝ} (hα : 1/2 < α)
    (q : ℕ) (hqα : α < q) (hβ : 1/2 < β)
    (hβq : β = (q:ℝ)-α) (hc : 0 < c) (hm : 0 ≤ m) (hmc : m ≤ c)
    (F : ℝ → ℝ) (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hleft : ∀ x ≤ 0, iteratedDeriv q F x = 0) :
    ‖BrownianSharp.AlignmentFractionalDensity.profileToL2
      (BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ
        (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q
          (fun x => F (c*x-m))
          (hF.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))))‖^2 =
      c^(2*α-1) *
        (∫ x in (0:ℝ)..(c-m), (rlIntegral β (iteratedDeriv q F) x)^2) := by
  let H : ℝ → ℝ := fun x => F (c*x-m)
  have hH : ContDiff ℝ (∞ : ℕ∞ω) H :=
    hF.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hHnorm := smooth_atom_preimage_norm_sq_eq_energy hα q hqα hβ hβq H hH
  have hFq : Continuous (iteratedDeriv q F) := by
    simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv q hF).continuous
  have hderiv := iteratedDeriv_dilate_shift q F hF c m
  calc
    _ = ∫ t in (0:ℝ)..1, (rlIntegral β (iteratedDeriv q H) t)^2 := hHnorm
    _ = ∫ t in (0:ℝ)..1,
          (rlIntegral β (fun u => c^q * (iteratedDeriv q F) (c*u-m)) t)^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [show iteratedDeriv q H = iteratedDeriv q (fun x => F (c*x-m)) by rfl,
        hderiv]
    _ = c^(2*α-1) *
          (∫ x in (0:ℝ)..(c-m), (rlIntegral β (iteratedDeriv q F) x)^2) :=
      rlIntegral_dilate_shift_energy q hβq hc hm hmc hβ
        (iteratedDeriv q F) hFq hleft

/-- Extend a causal RL profile by zero to negative time. -/
def causalRLProfile (β : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else rlIntegral β F t

theorem causalRLProfile_measurable {β : ℝ} (hβ : 1/2 < β)
    (F : ℝ → ℝ) (hF : Continuous F) : Measurable (causalRLProfile β F) := by
  apply measurable_of_continuousOn_compl_singleton 0
  rw [isOpen_compl_singleton.continuousOn_iff]
  intro t ht
  have htne : t ≠ 0 := by simpa using ht
  by_cases hneg : t < 0
  · have heq : causalRLProfile β F =ᶠ[𝓝 t] fun _ : ℝ => 0 := by
      filter_upwards [Iio_mem_nhds hneg] with x hx
      have hx' : x < 0 := by simpa using hx
      simp [causalRLProfile, le_of_lt hx']
    exact continuousAt_const.congr heq.symm
  · have hpos : 0 < t := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm htne)
    let T : ℝ := t+1
    have hT : 0 < T := by dsimp [T]; linarith
    have hcont := rlIntegral_continuousOn_compact hβ F hF T hT
    have hmem : t ∈ Set.Icc (0:ℝ) T := by
      constructor
      · exact le_of_lt hpos
      · dsimp [T]; linarith
    have hAt := (hcont.continuousWithinAt hmem).continuousAt
      (Icc_mem_nhds hpos (by dsimp [T]; linarith))
    have heq : (fun x => rlIntegral β F x) =ᶠ[𝓝 t] causalRLProfile β F := by
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      have hx' : 0 < x := by simpa using hx
      simp [causalRLProfile, not_le.mpr hx']
    exact hAt.congr heq

/-- The global causal RL preimage of a smooth compact atom is square
integrable when its order is greater than one half. -/
theorem causalRLProfile_memLp_two {α β : ℝ} (hα : 1/2 < α) (hβ : 1/2 < β)
    (q : ℕ) (hβq : β = (q:ℝ)-α) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j < q, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0)
    (hsupport : ∀ u, 1 ≤ u → iteratedDeriv q F u = 0) :
    MemLp (causalRLProfile β (iteratedDeriv q F)) 2 (volume : Measure ℝ) := by
  let G : ℝ → ℝ := causalRLProfile β (iteratedDeriv q F)
  let G2 : ℝ → ℝ := fun t => (G t)^2
  have hFq : Continuous (iteratedDeriv q F) := by
    simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv q hF).continuous
  have hGm : Measurable G := by
    simpa [G] using causalRLProfile_measurable hβ (iteratedDeriv q F) hFq
  have hG2m : AEStronglyMeasurable G2 (volume : Measure ℝ) := by
    exact (hGm.pow_const 2).aestronglyMeasurable
  have hlocalC : ContinuousOn G (Set.Icc (0:ℝ) 2) := by
    have hC := rlIntegral_continuousOn_compact hβ (iteratedDeriv q F) hFq 2 (by norm_num)
    refine hC.congr ?_
    intro t ht
    by_cases htz : t = 0
    · simp [G, causalRLProfile, htz, rlIntegral]
    · simp [G, causalRLProfile, not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm htz))]
  have hlocalSq : ContinuousOn G2 (Set.Icc (0:ℝ) 2) := hlocalC.pow 2
  have hlocalSq' : ContinuousOn G2 (Set.uIcc (0:ℝ) 2) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    exact hlocalSq
  have hlocalI : IntegrableOn G2 (Set.Ioc (0:ℝ) 2) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 2)).mp
    exact hlocalSq'.intervalIntegrable
  let p : ℝ := -α-1
  let e : ℝ := 2*p
  have he : e < -1 := by dsimp [e,p]; linarith
  have hpow : IntegrableOn (fun t : ℝ => t^e) (Set.Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt he (by norm_num)
  let A : ℝ := |(Real.Gamma β)⁻¹ * (-1:ℝ)^q *
    (descPochhammer ℝ q).eval (β-1)| * (∫ u in (0:ℝ)..1, |F u|)
  have hA : 0 ≤ A := by
    dsimp [A]
    apply mul_nonneg (abs_nonneg _)
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _)
  let C : ℝ := A^2 * (1/2)^e
  have hmajor : IntegrableOn (fun t : ℝ => C * t^e) (Set.Ioi (2:ℝ)) :=
    hpow.const_mul C
  have htail : IntegrableOn G2 (Set.Ioi (2:ℝ)) := by
    apply hmajor.mono'
    · exact hG2m.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht2 : 2 < t := by simpa using ht
      have hdec := rlIntegral_tail_decay hα hβ (le_of_lt ht2) q hβq F hF hzero hsupport
      have hgeq : G t = rlIntegral β (iteratedDeriv q F) t := by
        simp [G, causalRLProfile, not_le.mpr (by linarith : 0 < t)]
      have hbnd : |G t| ≤ A * (t/2)^p := by
        calc
          |G t| = |rlIntegral β (iteratedDeriv q F) t| := by rw [hgeq]
          _ ≤ |(Real.Gamma β)⁻¹ * (-1:ℝ)^q * (descPochhammer ℝ q).eval (β-1)| *
              (t/2)^p * (∫ u in (0:ℝ)..1, |F u|) := by simpa [p] using hdec
          _ = A * (t/2)^p := by simp [A, mul_assoc, mul_left_comm, mul_comm]
      have hy : 0 < t/2 := by linarith
      have hpower : ((t/2)^p)^2 = (t/2)^e := by
        calc
          ((t/2)^p)^2 = ((t/2)^p)^(2:ℝ) := by norm_num
          _ = (t/2)^(p*2) := by rw [← Real.rpow_mul hy.le]
          _ = (t/2)^e := by rw [show p*2=e by dsimp [e]; ring]
      have hsquare : G2 t ≤ A^2 * (t/2)^e := by
        have hnonneg : 0 ≤ A * (t/2)^p := mul_nonneg hA (Real.rpow_nonneg hy.le _)
        have hsq : |G t|^2 ≤ (A * (t/2)^p)^2 :=
          (sq_le_sq₀ (abs_nonneg (G t)) hnonneg).2 hbnd
        simpa [sq_abs, hpower, mul_pow] using hsq
      have hrep : (t/2)^e = (1/2)^e * t^e := by
        rw [show t/2 = (1/2)*t by ring, Real.mul_rpow (by norm_num) (le_of_lt (by linarith : 0 < t))]
      calc
        ‖G2 t‖ = G2 t := by simp [G2, abs_of_nonneg (sq_nonneg (G t))]
        _ ≤ C * t^e := by
          calc
            G2 t ≤ A^2 * (t/2)^e := hsquare
            _ ≤ C * t^e := by rw [hrep]; simp [C, mul_assoc, mul_comm]
  have hIoi0 : IntegrableOn G2 (Set.Ioi (0:ℝ)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 2), integrableOn_union]
    exact ⟨hlocalI, htail⟩
  have hIic0 : IntegrableOn G2 (Set.Iic (0:ℝ)) := by
    have hz : G2 =ᵐ[volume.restrict (Set.Iic (0:ℝ))] fun _ : ℝ => (0:ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      have ht' : t ≤ 0 := by simpa using ht
      simp [G2, G, causalRLProfile, ht']
    have hz0 : Integrable (fun _ : ℝ => (0:ℝ))
        (volume.restrict (Set.Iic (0:ℝ))) :=
      integrable_zero ℝ ℝ (volume.restrict (Set.Iic (0:ℝ)))
    exact hz0.congr hz.symm
  have hsq : Integrable G2 (volume : Measure ℝ) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi_of_le (show (0:ℝ) ≤ 0 by rfl), integrableOn_union]
    exact ⟨hIic0, hIoi0⟩
  exact (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2 hsq

/-- Every finite-horizon energy of a smooth compact-atom RL profile is bounded
by its global `L²` energy. -/
theorem rlIntegral_finite_energy_le_global {α β : ℝ} (hα : 1/2 < α)
    (hβ : 1/2 < β) (q : ℕ) (hβq : β = (q:ℝ)-α)
    (F : ℝ → ℝ) (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hzero : ∀ j < q, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0)
    (hsupport : ∀ u, 1 ≤ u → iteratedDeriv q F u = 0)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in (0:ℝ)..T, (rlIntegral β (iteratedDeriv q F) t)^2) ≤
      ∫ t, (causalRLProfile β (iteratedDeriv q F) t)^2 ∂(volume : Measure ℝ) := by
  have hmem := causalRLProfile_memLp_two hα hβ q hβq F hF hzero hsupport
  have hFq : Continuous (iteratedDeriv q F) := by
    simpa only [iteratedDeriv_eq_iterate] using (ContDiff.iterate_deriv q hF).continuous
  let G : ℝ → ℝ := causalRLProfile β (iteratedDeriv q F)
  let G2 : ℝ → ℝ := fun t => (G t)^2
  have hsq : Integrable G2 (volume : Measure ℝ) := by
    exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
  have hIoc :
      (∫ t in Set.Ioc (0:ℝ) T, (rlIntegral β (iteratedDeriv q F) t)^2) =
        ∫ t in Set.Ioc (0:ℝ) T, G2 t ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    simp [G2, G, causalRLProfile, not_le.mpr ht0]
  calc
    (∫ t in (0:ℝ)..T, (rlIntegral β (iteratedDeriv q F) t)^2) =
        ∫ t in Set.Ioc (0:ℝ) T, (rlIntegral β (iteratedDeriv q F) t)^2 :=
      intervalIntegral.integral_of_le (μ := volume) (f :=
        fun t => (rlIntegral β (iteratedDeriv q F) t)^2) hT.le
    _ = ∫ t in Set.Ioc (0:ℝ) T, G2 t ∂volume := hIoc
    _ ≤ ∫ t, G2 t ∂volume :=
      setIntegral_le_integral hsq (ae_of_all _ fun t => sq_nonneg (G t))
    _ = ∫ t, (causalRLProfile β (iteratedDeriv q F) t)^2 ∂volume := rfl

/-- Uniform global-energy control of the genuine shifted smooth-atom
preimage. The sole atom-dependent constant is the global `L²` energy of the
unshifted causal preimage. -/
theorem smooth_atom_shift_preimage_norm_sq_le_global {α β c m : ℝ}
    (hα : 1/2 < α) (q : ℕ) (hqα : α < q) (hβ : 1/2 < β)
    (hβq : β = (q:ℝ)-α) (hc : 0 < c) (hm : 0 ≤ m) (hmc : m < c)
    (F : ℝ → ℝ) (hF : ContDiff ℝ (∞ : ℕ∞ω) F)
    (hleft : ∀ x ≤ 0, iteratedDeriv q F x = 0)
    (hzero : ∀ j < q, iteratedDeriv j F 0 = 0 ∧ iteratedDeriv j F 1 = 0)
    (hsupport : ∀ u, 1 ≤ u → iteratedDeriv q F u = 0) :
    ‖BrownianSharp.AlignmentFractionalDensity.profileToL2
      (BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ
        (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q
          (fun x => F (c*x-m))
          (hF.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))))‖^2 ≤
      c^(2*α-1) *
        (∫ t, (causalRLProfile β (iteratedDeriv q F) t)^2 ∂(volume : Measure ℝ)) := by
  have hmc_le : m ≤ c := le_of_lt hmc
  have hT : 0 < c-m := sub_pos.mpr hmc
  rw [smooth_atom_shift_preimage_norm_sq hα q hqα hβ hβq hc hm hmc_le
    F hF hleft]
  exact mul_le_mul_of_nonneg_left
    (rlIntegral_finite_energy_le_global hα hβ q hβq F hF hzero hsupport
      (c-m) hT)
    (Real.rpow_nonneg hc.le _)

/-- The certificate's concrete smooth plateau atom has exact unit-L²
Riemann--Liouville preimages at every dyadic scale and translate. The qth
order is selected above α, and the squared source norm is uniformly bounded
by `Cα · 2^((2α-1)s)`. -/
theorem smoothAtom_dyadic_fractional_preimage {α : ℝ} (hα : 1/2 < α) :
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ s : ℕ, ∀ m : ℕ, m < 2^s →
        ∃ g : UnitL2,
          BrownianSharp.AlignmentFractionalTranslation.fractionalRL α hα g =
            BrownianSharp.AlignmentFractionalDensity.restrictProfile
              (fun t => BrownianSharp.smoothAtom (((2^s:ℝ) * t) - m))
              ((BrownianSharp.smoothAtom_contDiff.comp
                ((contDiff_const.mul contDiff_id).sub contDiff_const)).continuous) ∧
          ‖g‖^2 ≤ Cα * (2:ℝ)^((2*α-1)*(s:ℝ)) := by
  let q : ℕ := Nat.ceil α + 2
  have hceilLower : α ≤ (Nat.ceil α:ℝ) := Nat.le_ceil α
  have hqα : α < (q:ℝ) := by
    dsimp [q]
    push_cast
    linarith [hceilLower]
  let β : ℝ := (q:ℝ)-α
  have hβ : 1/2 < β := by
    dsimp [β,q]
    push_cast
    linarith [hceilLower]
  have hβq : β = (q:ℝ)-α := rfl
  rcases smoothAtom_fractional_atom_conditions q with ⟨hzero,hSupport,hleft⟩
  let E : ℝ := ∫ t, (causalRLProfile β
    (iteratedDeriv q BrownianSharp.smoothAtom) t)^2 ∂(volume : Measure ℝ)
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact integral_nonneg_of_ae (ae_of_all _ fun t =>
      sq_nonneg (causalRLProfile β (iteratedDeriv q BrownianSharp.smoothAtom) t))
  refine ⟨E+1, by linarith, ?_⟩
  intro s m hm
  let c : ℝ := (2^s:ℝ)
  let mR : ℝ := m
  have hc : 0 < c := by dsimp [c]; positivity
  have hmR : 0 ≤ mR := by dsimp [mR]; exact Nat.cast_nonneg _
  have hmc : mR < c := by
    dsimp [c,mR]
    exact_mod_cast hm
  let H : ℝ → ℝ := fun t => BrownianSharp.smoothAtom (c*t-mR)
  have hH : ContDiff ℝ (∞ : ℕ∞ω) H := by
    exact BrownianSharp.smoothAtom_contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hjet := shiftedSmoothAtom_jets_zero q hc hmR
  let g : UnitL2 := BrownianSharp.AlignmentFractionalDensity.profileToL2
    (BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ
      (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q H hH))
  have hpre :=
    BrownianSharp.AlignmentFractionalDensity.smooth_atom_fractional_preimage_L2
      α hα q hqα hβ H hH hjet
  have hbound := smooth_atom_shift_preimage_norm_sq_le_global
    hα q hqα hβ hβq hc hmR hmc BrownianSharp.smoothAtom
    BrownianSharp.smoothAtom_contDiff hleft hzero hSupport
  have hboundE : ‖g‖^2 ≤ c^(2*α-1) * E := by
    simpa [g, H, E] using hbound
  have hpow : c^(2*α-1) = (2:ℝ)^((2*α-1)*(s:ℝ)) := by
    dsimp [c]
    rw [← Real.rpow_natCast (2:ℝ) s]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (s:ℝ) (2*α-1)]
    congr 1 <;> ring
  have hfinal : ‖g‖^2 ≤ (E+1) * (2:ℝ)^((2*α-1)*(s:ℝ)) := by
    calc
      ‖g‖^2 ≤ c^(2*α-1) * E := hboundE
      _ ≤ c^(2*α-1) * (E+1) :=
        mul_le_mul_of_nonneg_left (by linarith : E ≤ E+1)
          (Real.rpow_nonneg hc.le _)
      _ = (E+1) * (2:ℝ)^((2*α-1)*(s:ℝ)) := by rw [hpow, mul_comm]
  refine ⟨g, ?_, hfinal⟩
  change BrownianSharp.AlignmentFractionalTranslation.fractionalRL α hα
    (BrownianSharp.AlignmentFractionalDensity.profileToL2
      (BrownianSharp.AlignmentFractionalDensity.fractionalOnC β hβ
        (BrownianSharp.AlignmentFractionalDensity.derivativeProfile q H hH))) =
    BrownianSharp.AlignmentFractionalDensity.restrictProfile H hH.continuous
  exact hpre

end BrownianSharp.AlignmentFractionalTail
