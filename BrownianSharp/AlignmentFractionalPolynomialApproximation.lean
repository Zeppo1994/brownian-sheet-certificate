import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import BrownianSharp.AlignmentFractionalDyadicProjection
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.PSeries

/-! A local Taylor remainder estimate for positive real powers. This is the
calculus input for polynomial approximation of the causal fractional kernel
away from its moving singularity. -/

noncomputable section
open Set
open MeasureTheory
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentFractionalPolynomialApproximation

open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalKernel

/-- A cell average minimizes squared error among all constants. -/
theorem interval_integral_sq_sub_average_le_fixed {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => (f x)^2) volume a b) (c : ℝ) :
    (∫ x in a..b, (f x - average (volume.restrict (Set.Ioc a b)) f)^2) ≤
      ∫ x in a..b, (f x-c)^2 := by
  let μ := volume.restrict (Set.Ioc a b)
  have hμfin : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hμnz : μ ≠ 0 := by
    apply (Measure.measure_univ_ne_zero).mp
    simpa [μ, Real.volume_Ioc] using hab
  haveI hμ : NeZero μ := ⟨hμnz⟩
  have hfμ : Integrable f μ := by
    dsimp [μ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hf
  have hf2μ : Integrable (fun x => f x ^ 2) μ := by
    dsimp [μ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hf2
  let g : ℝ → ℝ := fun x => f x-c
  have hcμ : Integrable (fun _ : ℝ => c) μ := integrable_const _
  have hgμ : Integrable g μ := by
    dsimp [g]
    exact hfμ.sub hcμ
  have hcross : Integrable (fun x => (2*c)*f x) μ := hfμ.const_mul _
  have hconst : Integrable (fun _ : ℝ => c^2) μ := integrable_const _
  have hg2μ : Integrable (fun x => g x ^ 2) μ := by
    have hsum : Integrable (fun x => f x ^ 2 - (2*c)*f x + c^2) μ :=
      (hf2μ.sub hcross).add hconst
    apply hsum.congr
    filter_upwards with x
    dsimp [g]
    ring
  have hvar := integral_sq_sub_average_le hgμ hg2μ
  have havg : average μ g = average μ f-c := by
    change average μ (f - fun _ : ℝ => c) = _
    rw [average_sub hfμ hcμ, average_const]
  have hleft : (∫ x, (g x-average μ g)^2 ∂μ) =
      ∫ x, (f x-average μ f)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [havg]
    dsimp [g]
    ring
  have hright : (∫ x, g x^2 ∂μ) = ∫ x, (f x-c)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rfl
  rw [hleft, hright] at hvar
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
  simpa [μ] using hvar

/-- Taylor's remainder for `x ↦ x^p`, based at the right endpoint `x₀`,
has the expected power bound uniformly on a positive interval. -/
theorem power_taylor_remainder_bound {p : ℝ} {m : ℕ}
    (hm0 : 0 < m) (hpm : p < m) {x x₀ : ℝ}
    (hx : 0 < x) (hxx₀ : x ≤ x₀) :
    |x^p - taylorWithinEval (fun z : ℝ => z^p) (m-1)
        (Set.uIcc x₀ x) x₀ x| ≤
      (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
        (x₀-x)^m * x^(p-m) := by
  by_cases hne : x₀ = x
  · subst x₀
    simp [taylorWithinEval_self, Nat.ne_of_gt hm0]
  have hlt : x < x₀ := lt_of_le_of_ne hxx₀ (Ne.symm hne)
  have hcont : ContDiffOn ℝ (↑(m-1)+1) (fun z : ℝ => z^p) (Set.uIcc x₀ x) := by
    intro y hy
    have hypos : y ≠ 0 := by
      have hyI : y ∈ Set.Icc x x₀ := by
        simpa [Set.uIcc_of_ge hxx₀] using hy
      exact ne_of_gt (lt_of_lt_of_le hx hyI.1)
    exact (Real.contDiffAt_rpow_const (n:=↑(m-1)+1) (p:=p) (x:=y)
      (Or.inl hypos)).contDiffWithinAt
  obtain ⟨y,hy,hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f:=fun z : ℝ => z^p) (x:=x) (x₀:=x₀) (n:=m-1) hne hcont
  have hyI : y ∈ Set.Ioo x x₀ := by
    simpa [Set.uIoo_of_ge hxx₀] using hy
  have hypos : 0 < y := lt_trans hx hyI.1
  have hcoef : iteratedDeriv m (fun z : ℝ => z^p) y =
      (descPochhammer ℝ m).eval p * y^(p-m) := by
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const p y m
  have hq : p-m ≤ 0 := by norm_cast; linarith
  have hpow : y^(p-m) ≤ x^(p-m) :=
    Real.rpow_le_rpow_of_nonpos hx hyI.1.le hq
  have hpow0 : 0 ≤ y^(p-m) := Real.rpow_nonneg hypos.le _
  have hderiv :
      |iteratedDeriv m (fun z : ℝ => z^p) y| ≤
        |(descPochhammer ℝ m).eval p| * x^(p-m) := by
    rw [hcoef, abs_mul, abs_of_nonneg hpow0]
    exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  have hfactorial : 0 < (m.factorial:ℝ) := by positivity
  have hrem' : x^p - taylorWithinEval (fun z : ℝ => z^p) (m-1)
        (Set.uIcc x₀ x) x₀ x =
      iteratedDeriv m (fun z : ℝ => z^p) y * (x-x₀)^m / (m.factorial:ℝ) := by
    simpa [Nat.sub_add_cancel hm0] using hrem
  have hdist : |x-x₀|^m = (x₀-x)^m := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxx₀)]
    congr 1
    ring
  rw [hrem', abs_div, abs_mul, abs_pow, hdist]
  have hdist0 : 0 ≤ (x₀-x)^m := by positivity
  calc
    (|iteratedDeriv m (fun z : ℝ => z^p) y| * (x₀-x)^m) /
        |(m.factorial:ℝ)| ≤
      (|(descPochhammer ℝ m).eval p| * x^(p-m) * (x₀-x)^m) /
        (m.factorial:ℝ) := by
          rw [abs_of_pos hfactorial]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hderiv hdist0) hfactorial.le
    _ = (|(descPochhammer ℝ m).eval p| / (m.factorial:ℝ)) *
          (x₀-x)^m * x^(p-m) := by ring


/-- First-order endpoint oscillation bound, useful on cells separated from
the moving singularity. -/
theorem power_first_order_endpoint_error {p : ℝ} (hp : p < 1)
    {x x₀ : ℝ} (hx : 0 < x) (hxx₀ : x ≤ x₀) :
    |x^p-x₀^p| ≤ |p| * (x₀-x) * x^(p-1) := by
  have h := power_taylor_remainder_bound (p:=p) (m:=1)
    (by norm_num) (by simpa using hp) hx hxx₀
  simpa [taylor_within_zero_eval] using h

/-- On a fixed positive interval, the Taylor polynomial of a power function
has a uniform explicit remainder bound. Unlike the moving-interval Lagrange
form above, the polynomial here is tied to the whole cell, so it can be used
as an element of a finite-dimensional piecewise-polynomial space. -/
theorem power_fixed_cell_taylor_remainder {p a b x : ℝ} {m : ℕ}
    (hm : 0 < m) (hpm : p < m) (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    |x^p - taylorWithinEval (fun z : ℝ => z^p) (m-1)
      (Set.Icc a b) a x| ≤
      (|(descPochhammer ℝ m).eval p| * a^(p-m)) *
        (x-a)^m / (Nat.factorial (m-1):ℝ) := by
  have hcont : ContDiffOn ℝ (↑(m-1)+1) (fun z : ℝ => z^p) (Set.Icc a b) := by
    intro y hy
    have hypos : y ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hy.1)
    exact (Real.contDiffAt_rpow_const (n:=↑(m-1)+1) (p:=p) (x:=y)
      (Or.inl hypos)).contDiffWithinAt
  have hC : ∀ y ∈ Set.Icc a b,
      ‖iteratedDerivWithin m (fun z : ℝ => z^p) (Set.Icc a b) y‖ ≤
        |(descPochhammer ℝ m).eval p| * a^(p-m) := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le ha hy.1
    have hcontAt : ContDiffAt ℝ (↑m) (fun z : ℝ => z^p) y :=
      Real.contDiffAt_rpow_const (n:=↑m) (p:=p) (x:=y) (Or.inl (ne_of_gt hypos))
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      hcontAt hy, iteratedDeriv_eq_iterate]
    rw [Real.iter_deriv_rpow_const p y m]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hypos.le _)]
    have hneg : p-m ≤ 0 := by norm_cast; linarith
    have hpow : y^(p-m) ≤ a^(p-m) := Real.rpow_le_rpow_of_nonpos ha hy.1 hneg
    exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  have hC' : ∀ y ∈ Set.Icc a b,
      ‖iteratedDerivWithin ((m-1)+1) (fun z : ℝ => z^p) (Set.Icc a b) y‖ ≤
        |(descPochhammer ℝ m).eval p| * a^(p-m) := by
    intro y hy
    simpa [Nat.sub_add_cancel hm] using hC y hy
  have hrem := taylor_mean_remainder_bound
    (a:=a) (b:=b) (x:=x) (C:=((|(descPochhammer ℝ m).eval p|) * a^(p-m)))
    (n:=m-1) hab.le hcont hx hC'
  have hpowidx : m-1+1=m := Nat.sub_add_cancel hm
  rw [hpowidx] at hrem
  simpa only [Real.norm_eq_abs] using hrem

/-- Fixed-cell Taylor approximant to the causal fractional kernel, on a cell
strictly to the left of its singularity. -/
noncomputable def causalKernelCellTaylorApprox
    (α t a b : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ *
    taylorWithinEval (fun z : ℝ => z^(α-1)) (m-1)
      (Set.Icc (t-b) (t-a)) (t-b) (t-u)

theorem continuous_taylorWithinEval_right (f : ℝ → ℝ) (n : ℕ)
    (s : Set ℝ) (x₀ : ℝ) :
    Continuous (fun x => taylorWithinEval f n s x₀ x) := by
  have heq : (fun x => taylorWithinEval f n s x₀ x) =
      (fun x => ∑ k ∈ Finset.range (n+1),
        ((k.factorial:ℝ)⁻¹ * (x-x₀)^k) • iteratedDerivWithin k f s x₀) := by
    funext x
    rw [taylor_within_apply]
  rw [heq]
  fun_prop

/-- Pointwise high-order Taylor remainder for an actual causal Gamma kernel
on one regular cell. The approximant is a fixed polynomial on the cell. -/
theorem causalKernel_cell_taylor_error_bound
    {α t a b u : ℝ} {m : ℕ} (hα : 0 < α) (hm : 0 < m)
    (hpm : α-1 < m) (hab : a ≤ u) (hub : u ≤ b) (hab' : a < b) (hbt : b < t) :
    |causalKernel α t u - causalKernelCellTaylorApprox α t a b m u| ≤
      |(Real.Gamma α)⁻¹| *
        (|(descPochhammer ℝ m).eval (α-1)| *
          (t-b)^(α-1-m)) * (b-u)^m / (Nat.factorial (m-1):ℝ) := by
  have hbase : 0 < t-b := by linarith
  have hx : t-u ∈ Set.Icc (t-b) (t-a) := by constructor <;> linarith
  have hrem := power_fixed_cell_taylor_remainder
    (p:=α-1) (a:=t-b) (b:=t-a) (x:=t-u) hm hpm hbase
    (by linarith : t-b<t-a) hx
  have hkernel : causalKernel α t u = (Real.Gamma α)⁻¹*(t-u)^(α-1) := by
    simp [causalKernel, kernel, lt_of_le_of_lt hub hbt]
  rw [hkernel, causalKernelCellTaylorApprox, ← mul_sub, abs_mul]
  have hgap : (t-u)-(t-b)=b-u := by ring
  rw [hgap] at hrem
  calc
    |(Real.Gamma α)⁻¹| *
        |(t-u)^(α-1)-taylorWithinEval (fun z : ℝ => z^(α-1)) (m-1)
          (Set.Icc (t-b) (t-a)) (t-b) (t-u)| ≤
      |(Real.Gamma α)⁻¹| *
        (|(descPochhammer ℝ m).eval (α-1)| * (t-b)^(α-1-m) *
          (b-u)^m / (Nat.factorial (m-1):ℝ)) := by
      apply mul_le_mul_of_nonneg_left hrem (abs_nonneg _)
    _ = _ := by ring

/-- Integrated Taylor approximation error on one regular cell. This is the
local estimate from which the summable polynomial-grid tail can be built. -/
theorem causalKernel_cell_taylor_integral_error_bound
    {α t a b h : ℝ} {m : ℕ} (hα : 0 < α) (hm : 0 < m)
    (hpm : α-1 < m) (hab : a < b) (hwidth : b-a ≤ h)
    (hbt : b < t) (hh : 0 < h) :
    (∫ u in a..b,
      (causalKernel α t u - causalKernelCellTaylorApprox α t a b m u)^2) ≤
      (|(Real.Gamma α)⁻¹| *
        (|(descPochhammer ℝ m).eval (α-1)| * (t-b)^(α-1-m)) /
          (Nat.factorial (m-1):ℝ))^2 * h^(2*m+1) := by
  let B : ℝ := |(Real.Gamma α)⁻¹| *
    (|(descPochhammer ℝ m).eval (α-1)| * (t-b)^(α-1-m)) /
      (Nat.factorial (m-1):ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcontK : ContinuousOn (causalKernel α t) (Set.Icc a b) :=
    causalKernel_continuousOn_of_right_lt hbt
  have hcontA : Continuous (fun u : ℝ => causalKernelCellTaylorApprox α t a b m u) := by
    unfold causalKernelCellTaylorApprox
    exact (continuous_const.mul (continuous_taylorWithinEval_right
      (fun z : ℝ => z^(α-1)) (m-1) (Set.Icc (t-b) (t-a)) (t-b))).comp
        (continuous_const.sub continuous_id)
  have hcontE : ContinuousOn
      (fun u => causalKernel α t u - causalKernelCellTaylorApprox α t a b m u)
      (Set.Icc a b) := hcontK.sub hcontA.continuousOn
  have hcontSq : ContinuousOn
      (fun u => (causalKernel α t u - causalKernelCellTaylorApprox α t a b m u)^2)
      (Set.Icc a b) := hcontE.pow 2
  have hinter : IntervalIntegrable
      (fun u => (causalKernel α t u - causalKernelCellTaylorApprox α t a b m u)^2)
      volume a b := hcontSq.intervalIntegrable_of_Icc hab.le
  have hconst : IntervalIntegrable (fun _ : ℝ => B^2*h^(2*m)) volume a b :=
    intervalIntegrable_const
  have hosc : ∀ u ∈ Set.Icc a b,
      (causalKernel α t u - causalKernelCellTaylorApprox α t a b m u)^2 ≤
        B^2*h^(2*m) := by
    intro u hu
    have herr := causalKernel_cell_taylor_error_bound hα hm hpm hu.1 hu.2
      hab hbt
    have hdist : 0 ≤ b-u ∧ b-u ≤ h := by
      constructor
      · exact sub_nonneg.mpr hu.2
      · calc
          b-u ≤ b-a := sub_le_sub_left hu.1 b
          _ ≤ h := hwidth
    have hpow : (b-u)^m ≤ h^m := by
      exact pow_le_pow_left₀ hdist.1 hdist.2 m
    have hbound : |causalKernel α t u - causalKernelCellTaylorApprox α t a b m u| ≤
        B*(b-u)^m := by
      calc
        _ ≤ |(Real.Gamma α)⁻¹| *
          (|(descPochhammer ℝ m).eval (α-1)| * (t-b)^(α-1-m)) *
            (b-u)^m / (Nat.factorial (m-1):ℝ) := herr
        _ = B*(b-u)^m := by dsimp [B]; ring
    have hdist0 : 0 ≤ b-u := hdist.1
    have hdistpow0 : 0 ≤ (b-u)^m := pow_nonneg hdist0 _
    have hright : 0 ≤ B*(b-u)^m := mul_nonneg hB hdistpow0
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hright).2 hbound
    have hpow2 : ((b-u)^m)^2 ≤ (h^m)^2 := by
      have hdiff : 0 ≤ h^m-(b-u)^m := sub_nonneg.mpr hpow
      have hsum : 0 ≤ h^m+(b-u)^m := add_nonneg (pow_nonneg hh.le m) hdistpow0
      nlinarith [mul_nonneg hsum hdiff]
    have hfinal : |causalKernel α t u - causalKernelCellTaylorApprox α t a b m u|^2 ≤
        B^2*h^(2*m) := by
      calc
        _ ≤ (B*(b-u)^m)^2 := hsquare
        _ = B^2*((b-u)^m)^2 := by rw [mul_pow]
        _ ≤ B^2*(h^m)^2 := mul_le_mul_of_nonneg_left hpow2 (sq_nonneg B)
        _ = B^2*h^(2*m) := by
          congr 1
          calc
            (h^m)^2 = h^(m*2) := by rw [pow_mul]
            _ = h^(2*m) := by rw [Nat.mul_comm]
    simpa [sq_abs] using hfinal
  have hmono := intervalIntegral.integral_mono_on hab.le hinter hconst hosc
  have hlength : b-a ≤ h := hwidth
  calc
    _ ≤ ∫ _u in a..b, B^2*h^(2*m) := hmono
    _ = (b-a)*(B^2*h^(2*m)) := by rw [intervalIntegral.integral_const]; ring
    _ ≤ h*(B^2*h^(2*m)) := mul_le_mul_of_nonneg_right hlength (by positivity)
    _ = B^2*h^(2*m+1) := by rw [pow_succ]; ring

/-- Summed high-order Taylor error on the regular cells of a uniform grid.
The exponent condition `m > α-1/2` is exactly what makes the distance-tail
series summable and produces the sharp squared rate `h^(2α-1)`. -/
theorem causalKernel_regular_grid_taylor_error_sum_le
    {α t h : ℝ} {N m : ℕ} (hα : 0 < α) (hm : 0 < m)
    (horder : α-1+1/2 < m) (hh : 0 < h)
    (hfar : ((N+1:ℕ):ℝ)*h ≤ t) :
    (∑ j ∈ Finset.range N,
      ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
        (causalKernel α t u - causalKernelCellTaylorApprox α t
          ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h) m u)^2) ≤
      ((|(Real.Gamma α)⁻¹| *
        |(descPochhammer ℝ m).eval (α-1)| /
          (Nat.factorial (m-1):ℝ))^2 *
        (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*(α-1-m)))) * h^(2*α-1) := by
  let q : ℝ := 2*(α-1-m)
  let C : ℝ := |(Real.Gamma α)⁻¹| *
    |(descPochhammer ℝ m).eval (α-1)| /
      (Nat.factorial (m-1):ℝ)
  have hq : q < -1 := by dsimp [q]; linarith
  have hseries : Summable (fun k : ℕ => ((k+1:ℕ):ℝ)^q) := by
    have hbase := Real.summable_nat_rpow.mpr hq
    convert hbase.comp_injective Nat.succ_injective using 1
    ext k
    norm_cast
  have hqnonpos : q ≤ 0 := by linarith
  have hqcoef : 0 ≤ C^2 := sq_nonneg C
  have hexponent : 2*(m:ℝ)+1+q = 2*α-1 := by dsimp [q]; push_cast; ring
  have hsumReindex :
      (∑ j ∈ Finset.range N, ((N-j:ℕ):ℝ)^q) =
        ∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)^q := by
    calc
      _ = ∑ j ∈ Finset.range N, (((N-1-j+1:ℕ):ℝ)^q) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        have hjlt : j < N := Finset.mem_range.mp hj
        have hnat : N-1-j+1=N-j := by omega
        exact_mod_cast hnat.symm
      _ = ∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)^q :=
        Finset.sum_range_reflect (fun k : ℕ => ((k+1:ℕ):ℝ)^q) N
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        C^2 * (((N-j:ℕ):ℝ)^q) * h^(2*(m:ℝ)+1+q) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < N := Finset.mem_range.mp hj
      have hjpos : 0 < (N-j:ℕ) := Nat.sub_pos_of_lt hjlt
      have hleft : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
      have hwidth : (((j+1:ℕ):ℝ)*h)-((j:ℝ)*h)=h := by
        have hc : ((j+1:ℕ):ℝ)=(j:ℝ)+1 := by norm_num
        rw [hc]
        ring
      have hfarj : ((j+1:ℕ):ℝ)*h ≤ t := by
        have hnat : j+1≤N+1 := by omega
        exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) hh.le) hfar
      have hgapPos : 0 < t-((j+1:ℕ):ℝ)*h := by
        have hNpos : 0 < ((N-j:ℕ):ℝ)*h := mul_pos (Nat.cast_pos.mpr hjpos) hh
        have hsum : ((j+1:ℕ):ℝ)*h + ((N-j:ℕ):ℝ)*h = ((N+1:ℕ):ℝ)*h := by
          have hn : (j+1)+(N-j)=N+1 := by omega
          calc
            _ = (((j+1)+(N-j):ℕ):ℝ)*h := by push_cast; ring
            _ = ((N+1:ℕ):ℝ)*h := by rw [hn]
        linarith
      have hgap : ((N-j:ℕ):ℝ)*h ≤ t-((j+1:ℕ):ℝ)*h := by
        have hsum : ((j+1:ℕ):ℝ)*h + ((N-j:ℕ):ℝ)*h = ((N+1:ℕ):ℝ)*h := by
          have hn : (j+1)+(N-j)=N+1 := by omega
          calc
            _ = (((j+1)+(N-j):ℕ):ℝ)*h := by push_cast; ring
            _ = ((N+1:ℕ):ℝ)*h := by rw [hn]
        linarith
      have hlocal := causalKernel_cell_taylor_integral_error_bound
        hα hm (by linarith [horder] : α-1<m)
        (by
          have hstep : (j:ℝ) < ((j+1:ℕ):ℝ) := by exact_mod_cast Nat.lt_succ_self j
          exact mul_lt_mul_of_pos_right hstep hh)
        hwidth.le (sub_pos.mp hgapPos) hh
      have hCpos : 0 ≤ C := by dsimp [C]; positivity
      have hcoef :
          (|(Real.Gamma α)⁻¹| *
            (|(descPochhammer ℝ m).eval (α-1)| *
              (t-((j+1:ℕ):ℝ)*h)^(α-1-m)) /
              (Nat.factorial (m-1):ℝ))^2 =
            C^2 * (t-((j+1:ℕ):ℝ)*h)^q := by
        let d : ℝ := t-((j+1:ℕ):ℝ)*h
        have hpow : ((t-((j+1:ℕ):ℝ)*h)^(α-1-m))^2 =
            (t-((j+1:ℕ):ℝ)*h)^(2*(α-1-m)) := by
          calc
            _ = d^(α-1-m) * d^(α-1-m) := by rw [pow_two]
            _ = d^((α-1-m)+(α-1-m)) :=
              (Real.rpow_add (by dsimp [d]; exact hgapPos) (α-1-m) (α-1-m)).symm
            _ = _ := by congr 1 <;> ring
        calc
          _ = (C*((t-((j+1:ℕ):ℝ)*h)^(α-1-m)))^2 := by dsimp [C]; ring
          _ = C^2*((t-((j+1:ℕ):ℝ)*h)^(α-1-m))^2 := by ring
          _ = C^2*(t-((j+1:ℕ):ℝ)*h)^(2*(α-1-m)) := by rw [hpow]
      rw [hcoef] at hlocal
      rw [← Real.rpow_natCast h (2*m+1)] at hlocal
      have hexpNat : ((2*m+1:ℕ):ℝ)=2*(m:ℝ)+1 := by push_cast; ring
      rw [hexpNat] at hlocal
      have hcompare : (t-((j+1:ℕ):ℝ)*h)^q ≤
          ((N-j:ℕ):ℝ)^q*h^q := by
        calc
          _ ≤ (((N-j:ℕ):ℝ)*h)^q :=
            Real.rpow_le_rpow_of_nonpos (mul_pos (Nat.cast_pos.mpr hjpos) hh) hgap hqnonpos
          _ = ((N-j:ℕ):ℝ)^q*h^q := Real.mul_rpow (Nat.cast_nonneg _) hh.le
      have hlocal' :
          (∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
            (causalKernel α t u - causalKernelCellTaylorApprox α t
              ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h) m u)^2) ≤
            C^2*((N-j:ℕ):ℝ)^q*h^(2*(m:ℝ)+1+q) := by
        calc
          _ ≤ C^2*(t-((j+1:ℕ):ℝ)*h)^q*h^(2*(m:ℝ)+1) := hlocal
          _ = (C^2*(t-((j+1:ℕ):ℝ)*h)^q)*h^(2*(m:ℝ)+1) := by ring
          _ ≤ (C^2*(((N-j:ℕ):ℝ)^q*h^q))*h^(2*(m:ℝ)+1) := by
            have hpowh : h^(2*(m:ℝ)+1) ≥ 0 := Real.rpow_nonneg hh.le _
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcompare hqcoef) hpowh
          _ = C^2*((N-j:ℕ):ℝ)^q*(h^q*h^(2*(m:ℝ)+1)) := by ring
          _ = C^2*((N-j:ℕ):ℝ)^q*h^(q+(2*(m:ℝ)+1)) := by
            rw [← Real.rpow_add hh]
          _ = C^2*((N-j:ℕ):ℝ)^q*h^(2*(m:ℝ)+1+q) := by congr 1 <;> ring
      exact hlocal'
    _ = C^2*h^(2*(m:ℝ)+1+q) *
        ∑ j ∈ Finset.range N, ((N-j:ℕ):ℝ)^q := by
      calc
        _ = ∑ j ∈ Finset.range N,
              (C^2*h^(2*(m:ℝ)+1+q))*((N-j:ℕ):ℝ)^q := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ = C^2*h^(2*(m:ℝ)+1+q) *
        ∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)^q := by rw [hsumReindex]
    _ ≤ C^2*h^(2*(m:ℝ)+1+q) * ∑' k : ℕ, ((k+1:ℕ):ℝ)^q := by
      apply mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum (Finset.range N) (by intro k hk; positivity) hseries)
      positivity
    _ = _ := by dsimp [C,q]; rw [hexponent]; ring

/-- Away from the causal boundary, the kernel oscillation on a cell is
controlled by its distance to the singularity. This is the scalar estimate
needed to improve piecewise-constant approximation above order one. -/
theorem causalKernel_cell_oscillation_bound {α t a u b : ℝ}
    (hα1 : 1 ≤ α) (hα15 : α ≤ 3/2)
    (hau : a ≤ u) (hub : u ≤ b) (hbt : b < t) :
    |causalKernel α t u - causalKernel α t a| ≤
      (Real.Gamma α)⁻¹ * (α-1) * (b-a) * (t-b)^(α-2) := by
  have hp0 : 0 ≤ α-1 := by linarith
  have hp1 : α-1 < 1 := by linarith
  have hx : 0 < t-u := by linarith
  have hxx0 : t-u ≤ t-a := by linarith
  have hnear := power_first_order_endpoint_error hp1 hx hxx0
  have habs : |α-1| = α-1 := abs_of_nonneg hp0
  have hdistEq : t-a-(t-u)=u-a := by ring
  have hexpEq : α-1-1=α-2 := by ring
  rw [habs, hdistEq, hexpEq] at hnear
  have hdist : 0 ≤ u-a := by linarith
  have hdistle : u-a ≤ b-a := by linarith
  have hneg : α-2 ≤ 0 := by linarith
  have hpos : 0 < t-b := by linarith
  have hpow : (t-u)^(α-2) ≤ (t-b)^(α-2) :=
    Real.rpow_le_rpow_of_nonpos hpos (by linarith) hneg
  have hbase : |(t-u)^(α-1)-(t-a)^(α-1)| ≤
      (α-1)*(u-a)*(t-b)^(α-2) := by
    calc
      _ ≤ (α-1)*(u-a)*(t-u)^(α-2) := by simpa [sub_sub] using hnear
      _ ≤ (α-1)*(u-a)*(t-b)^(α-2) := by
        apply mul_le_mul_of_nonneg_left hpow
        exact mul_nonneg hp0 hdist
  have hkernel :
      causalKernel α t u - causalKernel α t a =
        (Real.Gamma α)⁻¹ * ((t-u)^(α-1)-(t-a)^(α-1)) := by
    have hu : u < t := lt_of_le_of_lt hub hbt
    have ha : a < t := lt_of_le_of_lt hau (lt_of_le_of_lt hub hbt)
    simp [causalKernel, kernel, hu, ha]
    <;> ring
  rw [hkernel, abs_mul, abs_of_nonneg
    (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith : 0 < α)).le)]
  calc
    (Real.Gamma α)⁻¹ * |(t-u)^(α-1)-(t-a)^(α-1)| ≤
      (Real.Gamma α)⁻¹ * ((α-1)*(u-a)*(t-b)^(α-2)) :=
        mul_le_mul_of_nonneg_left hbase
          (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith : 0 < α)).le)
    _ ≤ (Real.Gamma α)⁻¹ * ((α-1)*(b-a)*(t-b)^(α-2)) := by
      apply mul_le_mul_of_nonneg_left _
        (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith : 0 < α)).le)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hpos.le _)
      exact mul_le_mul_of_nonneg_left hdistle hp0
    _ = (Real.Gamma α)⁻¹*(α-1)*(b-a)*(t-b)^(α-2) := by ring

/-- Squared cell-average error on a regular cell for `1 ≤ α ≤ 3/2`.
This is the local `h^3 distance^(2α-4)` estimate underlying the sharper
`h^(2α-1)` grid sum in this range. -/
theorem causalKernel_cell_average_error_bound {α t a b : ℝ}
    (hα1 : 1 ≤ α) (hα15 : α ≤ 3/2) (hab : a < b) (hbt : b < t) :
    (∫ u in a..b, (causalKernel α t u -
      average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * (α-1)^2 * (b-a)^3 * ((t-b)^(α-2))^2 := by
  have ha : a < t := lt_trans hab hbt
  have hcont : ContinuousOn (causalKernel α t) (Set.Icc a b) :=
    causalKernel_continuousOn_of_right_lt hbt
  have hf : IntervalIntegrable (causalKernel α t) volume a b :=
    hcont.intervalIntegrable_of_Icc hab.le
  have hcontsq : ContinuousOn (fun u => (causalKernel α t u - causalKernel α t a)^2)
      (Set.Icc a b) := (hcont.sub continuousOn_const).pow 2
  have hf2 : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b :=
    hcont.pow 2 |>.intervalIntegrable_of_Icc hab.le
  have hconstInt : IntervalIntegrable
      (fun _ : ℝ => ((Real.Gamma α)⁻¹*(α-1))^2*(b-a)^2*((t-b)^(α-2))^2)
      volume a b := intervalIntegrable_const
  have hbaseNonneg : 0 ≤ (Real.Gamma α)⁻¹*(α-1) := by
    apply mul_nonneg
    · exact inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith : 0 < α)).le
    · linarith
  have hdistNonneg : 0 ≤ b-a := le_of_lt (sub_pos.mpr hab)
  have hosc : ∀ u ∈ Set.Icc a b,
      (causalKernel α t u-causalKernel α t a)^2 ≤
        ((Real.Gamma α)⁻¹*(α-1))^2*(b-a)^2*((t-b)^(α-2))^2 := by
    intro u hu
    have hpoint := causalKernel_cell_oscillation_bound hα1 hα15 hu.1 hu.2 hbt
    have hright : 0 ≤ (Real.Gamma α)⁻¹*(α-1)*(b-a)*(t-b)^(α-2) :=
      mul_nonneg (mul_nonneg hbaseNonneg hdistNonneg) (Real.rpow_nonneg (by linarith) _)
    have hsquare : |causalKernel α t u-causalKernel α t a|^2 ≤
        ((Real.Gamma α)⁻¹*(α-1)*(b-a)*(t-b)^(α-2))^2 :=
      (sq_le_sq₀ (abs_nonneg _) hright).2 hpoint
    rw [sq_abs, mul_pow, mul_pow, mul_pow] at hsquare
    convert hsquare using 1 <;> ring
  have hcomp := intervalIntegral.integral_mono_on hab.le
      (hcontsq.intervalIntegrable_of_Icc hab.le) hconstInt hosc
  calc
    _ ≤ ∫ u in a..b, (causalKernel α t u-causalKernel α t a)^2 :=
      interval_integral_sq_sub_average_le_fixed hab hf hf2 (causalKernel α t a)
    _ ≤ ∫ u in a..b,
          ((Real.Gamma α)⁻¹*(α-1))^2*(b-a)^2*((t-b)^(α-2))^2 := hcomp
    _ = ((Real.Gamma α)⁻¹)^2*(α-1)^2*(b-a)^3*((t-b)^(α-2))^2 := by
      rw [intervalIntegral.integral_const]
      ring

/-- The sum of regular-cell projection errors on a uniform grid has the
sharp `h^(2α-1)` order when the grid stays at least one cell away from the
moving singularity. The two boundary cells are intentionally left for a
separate local energy estimate. -/
theorem causalKernel_regular_grid_average_error_sum_le
    {α t h : ℝ} {N : ℕ} (hα1 : 1 ≤ α) (hα15 : α < 3/2)
    (hh : 0 < h) (hfar : ((N+1:ℕ):ℝ)*h ≤ t) :
    (∑ j ∈ Finset.range N,
      ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
        (causalKernel α t u - average (volume.restrict
          (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * (α-1)^2 * h^3 * h^(2*α-4) *
        ∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4) := by
  let q : ℝ := 2*α-4
  have hq : q < -1 := by dsimp [q]; linarith
  have hsum : Summable (fun k : ℕ => ((k+1:ℕ):ℝ)^q) := by
    have hbase := Real.summable_nat_rpow.mpr hq
    convert hbase.comp_injective Nat.succ_injective using 1
    ext k
    norm_cast
  have hsumReindex :
      (∑ j ∈ Finset.range N, ((N-j:ℕ):ℝ)^q) =
        ∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)^q := by
    calc
      _ = ∑ j ∈ Finset.range N, (((N-1-j+1:ℕ):ℝ)^q) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        have hjlt : j < N := Finset.mem_range.mp hj
        have hnat : N-1-j+1=N-j := by omega
        exact_mod_cast hnat.symm
      _ = ∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)^q :=
        Finset.sum_range_reflect (fun k : ℕ => ((k+1:ℕ):ℝ)^q) N
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*h^q*((N-j:ℕ):ℝ)^q := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < N := Finset.mem_range.mp hj
      have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
      have hj1 : 0 < (N-j:ℕ) := Nat.sub_pos_of_lt hjlt
      have hd : 0 < t-(((j+1:ℕ):ℝ)*h) := by
        have hgap' : ((j+1:ℕ):ℝ)*h + ((N-j:ℕ):ℝ)*h ≤ t := by
          have hdiffNat : (j+1)+(N-j)=N+1 := by omega
          have hdiff : (((j+1)+(N-j):ℕ):ℝ) = ((N+1:ℕ):ℝ) := by exact_mod_cast hdiffNat
          calc
            _ = (((j+1)+(N-j):ℕ):ℝ)*h := by push_cast; ring
            _ = ((N+1:ℕ):ℝ)*h := by rw [hdiff]
            _ ≤ t := hfar
        have hgapPos : 0 < ((N-j:ℕ):ℝ)*h := mul_pos (Nat.cast_pos.mpr hj1) hh
        linarith
      have hgap : (((N-j:ℕ):ℝ)*h) ≤ t-(((j+1:ℕ):ℝ)*h) := by
        have hgap' : ((j+1:ℕ):ℝ)*h + ((N-j:ℕ):ℝ)*h ≤ t := by
          have hdiffNat : (j+1)+(N-j)=N+1 := by omega
          have hdiff : (((j+1)+(N-j):ℕ):ℝ) = ((N+1:ℕ):ℝ) := by exact_mod_cast hdiffNat
          calc
            _ = (((j+1)+(N-j):ℕ):ℝ)*h := by push_cast; ring
            _ = ((N+1:ℕ):ℝ)*h := by rw [hdiff]
            _ ≤ t := hfar
        have hgapPos : 0 < ((N-j:ℕ):ℝ)*h := mul_pos (Nat.cast_pos.mpr hj1) hh
        linarith
      have htower : 0 < t := lt_of_lt_of_le (mul_pos (by positivity) hh) hfar
      have hcell := causalKernel_cell_average_error_bound hα1 (by linarith : α ≤ 3/2)
        (by push_cast; nlinarith [hh] : (j:ℝ)*h < ((j+1:ℕ):ℝ)*h)
        (by nlinarith [hd] : ((j+1:ℕ):ℝ)*h < t)
      have hpowSq : ((t-((j+1:ℕ):ℝ)*h)^(α-2))^2 =
          (t-((j+1:ℕ):ℝ)*h)^q := by
        dsimp [q]
        calc
          (Real.rpow (t-((j+1:ℕ):ℝ)*h) (α-2))^2 =
              Real.rpow (t-((j+1:ℕ):ℝ)*h) (α-2) *
                Real.rpow (t-((j+1:ℕ):ℝ)*h) (α-2) := by rw [pow_two]
          _ = Real.rpow (t-((j+1:ℕ):ℝ)*h) ((α-2)+(α-2)) :=
            (Real.rpow_add hd _ _).symm
          _ = Real.rpow (t-((j+1:ℕ):ℝ)*h) (2*α-4) := by congr 1 <;> ring
      have hcompare : (t-((j+1:ℕ):ℝ)*h)^q ≤ (((N-j:ℕ):ℝ)*h)^q :=
        Real.rpow_le_rpow_of_nonpos (mul_pos (Nat.cast_pos.mpr hj1) hh) hgap
          (by dsimp [q]; linarith)
      have hscale : (((N-j:ℕ):ℝ)*h)^q =
          ((N-j:ℕ):ℝ)^q*h^q := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) hh.le]
      have hcoef : 0 ≤ ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3 := by positivity
      rw [hpowSq] at hcell
      have hwidth : (((j+1:ℕ):ℝ)*h)-((j:ℝ)*h)=h := by
        push_cast
        ring
      calc
        _ ≤ ((Real.Gamma α)⁻¹)^2*(α-1)^2*
              ((((j+1:ℕ):ℝ)*h)-((j:ℝ)*h))^3*
              (t-((j+1:ℕ):ℝ)*h)^q := hcell
        _ = ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*
              (t-((j+1:ℕ):ℝ)*h)^q := by rw [hwidth]
        _ ≤ ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*(((N-j:ℕ):ℝ)*h)^q :=
          mul_le_mul_of_nonneg_left hcompare hcoef
        _ = ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*h^q*((N-j:ℕ):ℝ)^q := by
          rw [hscale]
          ring
    _ = ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*h^q *
        ∑ j ∈ Finset.range N, ((N-j:ℕ):ℝ)^q := by rw [Finset.mul_sum]
    _ = ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*h^q *
        ∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)^q := by rw [hsumReindex]
    _ ≤ ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*h^q * ∑' k : ℕ, ((k+1:ℕ):ℝ)^q := by
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum (Finset.range N)
          (by intro k hk; positivity) hsum) (by positivity)
    _ = _ := by simp [q]

/-- The two cells adjacent to the moving singularity contribute only their
total local kernel energy. This complements the regular-grid estimate above;
the four interval-integrability inputs are provided by the actual unit-source
`L²` kernel theorem when the block lies in `[0,1]`. -/
theorem causalKernel_two_cell_average_error_le
    {α t a b c h : ℝ} (hα : 1/2 < α) (ha : 0 ≤ a)
    (hab : a < b) (hbc : b < c) (hat : a ≤ t) (htc : t ≤ c)
    (hc : c ≤ 1) (hwidth : c-a ≤ 2*h) (hh : 0 < h)
    (hf1 : IntervalIntegrable (causalKernel α t) volume a b)
    (hf1sq : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b)
    (hf2 : IntervalIntegrable (causalKernel α t) volume b c)
    (hf2sq : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume b c) :
    (∫ u in a..b, (causalKernel α t u -
      average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2) +
    (∫ u in b..c, (causalKernel α t u -
      average (volume.restrict (Set.Ioc b c)) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) := by
  have hvar1 := interval_integral_sq_sub_average_le hab hf1 hf1sq
  have hvar2 := interval_integral_sq_sub_average_le hbc hf2 hf2sq
  have hblock := causalKernel_singular_cell_energy hα ha hat htc hc
  have hexp : 0 < 2*α-1 := by linarith
  have hbase : 0 ≤ t-a := sub_nonneg.mpr hat
  have hbasele : t-a ≤ 2*h := by linarith
  have hpow : (t-a)^(2*α-1) ≤ (2*h)^(2*α-1) :=
    Real.rpow_le_rpow hbase hbasele hexp.le
  have hGamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  calc
    _ ≤ (∫ u in a..b, (causalKernel α t u)^2) +
        (∫ u in b..c, (causalKernel α t u)^2) := add_le_add hvar1 hvar2
    _ = ∫ u in a..c, (causalKernel α t u)^2 :=
      intervalIntegral.integral_add_adjacent_intervals hf1sq hf2sq
    _ = ((Real.Gamma α)⁻¹)^2 * ((t-a)^(2*α-1)/(2*α-1)) := hblock
    _ ≤ ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) := by
      apply mul_le_mul_of_nonneg_left _ hGamma
      exact div_le_div_of_nonneg_right hpow hexp.le

/-- Restrict the already-proved unit-source kernel `L²` fact to a cell; this
provides the integrability needed by the two-cell boundary estimate. -/
theorem causalKernel_intervalIntegrable_of_unit
    {α t a b : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    IntervalIntegrable (causalKernel α t) volume a b ∧
      IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b := by
  let μ := volume.restrict (Set.Ioc a b)
  let μunit := volume.restrict (Set.Icc (0:ℝ) 1)
  have hsubset : Set.Ioc a b ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    exact ⟨le_trans ha hx.1.le, le_trans hx.2 hb⟩
  have hmeasure : μ ≤ μunit := by
    dsimp [μ, μunit]
    exact Measure.restrict_mono_set volume hsubset
  have hunit := causalKernel_memLp_unit hα ht0 ht1
  have hcell := hunit.mono_measure hmeasure
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  haveI : IsFiniteMeasure μunit := by dsimp [μunit]; infer_instance
  have hcell1 : MemLp (causalKernel α t) 1 μ :=
    hcell.mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hfμ : Integrable (causalKernel α t) μ := by
    exact (memLp_one_iff_integrable.mp hcell1)
  have hf2μ : Integrable (fun u => (causalKernel α t u)^2) μ := hcell.integrable_sq
  have hf : IntervalIntegrable (causalKernel α t) volume a b := by
    dsimp [μ] at hfμ
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr hfμ
  have hf2 : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b := by
    dsimp [μ] at hf2μ
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr hf2μ
  exact ⟨hf,hf2⟩

/-- Actual two-cell boundary energy estimate, with local integrability
discharged from the unit-source kernel theorem. -/
theorem causalKernel_two_cell_average_error_le_actual
    {α t a b c h : ℝ} (hα : 1/2 < α) (ha : 0 ≤ a)
    (hab : a < b) (hbc : b < c) (hat : a ≤ t) (htc : t ≤ c)
    (hc : c ≤ 1) (hwidth : c-a ≤ 2*h) (hh : 0 < h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u in a..b, (causalKernel α t u -
      average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2) +
    (∫ u in b..c, (causalKernel α t u -
      average (volume.restrict (Set.Ioc b c)) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) := by
  have hcell1 := causalKernel_intervalIntegrable_of_unit hα ht0 ht1 ha hab (le_trans hbc.le hc)
  have hcell2 := causalKernel_intervalIntegrable_of_unit hα ht0 ht1 (le_trans ha hab.le)
      hbc hc
  exact causalKernel_two_cell_average_error_le hα ha hab hbc hat htc hc hwidth hh
    hcell1.1 hcell1.2 hcell2.1 hcell2.2

/-- Full uniform-grid source projection residual for `1 ≤ α < 3/2`, including
the two cells adjacent to the moving singularity and the zero causal tail.
This is the actual `L²` cell-average projection error, with no regularity or
tail estimates assumed. -/
theorem causalKernel_full_grid_average_error_sum_le
    {α t h : ℝ} {M N : ℕ} (hα1 : 1 ≤ α) (hα15 : α < 3/2)
    (hh : 0 < h) (hM : (M:ℝ)*h=1) (hNM : N+2≤M)
    (hfar : ((N+1:ℕ):ℝ)*h ≤ t) (hnear : t ≤ ((N+2:ℕ):ℝ)*h) :
    (∑ j ∈ Finset.range M, causalKernelCellError α t h j) ≤
      ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*h^(2*α-4)*
        ∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4) +
      ((Real.Gamma α)⁻¹)^2*((2*h)^(2*α-1)/(2*α-1)) := by
  have hunit : ((N+2:ℕ):ℝ)*h ≤ 1 := by
    calc
      _ ≤ (M:ℝ)*h := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hNM
        · exact hh.le
      _ = 1 := hM
  have ht0 : 0 ≤ t := le_trans (by positivity : 0 ≤ ((N+1:ℕ):ℝ)*h) hfar
  have ht1 : t ≤ 1 := le_trans hnear hunit
  have hreg := causalKernel_regular_grid_average_error_sum_le hα1 hα15 hh hfar
  have hN1 : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_cast
  have hN2 : ((N+2:ℕ):ℝ) = (N:ℝ)+2 := by norm_cast
  have hstep1 : (N:ℝ)*h < ((N+1:ℕ):ℝ)*h := by rw [hN1]; nlinarith [hh]
  have hstep2 : ((N+1:ℕ):ℝ)*h < ((N+2:ℕ):ℝ)*h := by rw [hN1,hN2]; nlinarith [hh]
  have hhat : (N:ℝ)*h ≤ t := le_trans hstep1.le hfar
  have hwidth : ((N+2:ℕ):ℝ)*h-(N:ℝ)*h ≤ 2*h := by
    rw [hN2]
    ring_nf
    exact le_rfl
  have hboundary := causalKernel_two_cell_average_error_le_actual
    (by linarith : 1/2<α) (by positivity : 0 ≤ (N:ℝ)*h)
    hstep1 hstep2 hhat hnear hunit hwidth hh ht0 ht1
  have htail :
      (∑ j ∈ Finset.Ico (N+2) M, causalKernelCellError α t h j)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hNj : N+2≤j := (Finset.mem_Ico.mp hj).1
    exact causalKernelCellError_eq_zero_of_right hh hnear hNj
  have hsplit :
      (∑ j ∈ Finset.range M, causalKernelCellError α t h j) =
        (∑ j ∈ Finset.range N, causalKernelCellError α t h j) +
          (causalKernelCellError α t h N + causalKernelCellError α t h (N+1)) := by
    rw [← Finset.sum_range_add_sum_Ico (causalKernelCellError α t h)
      (show N+2≤M by omega), Finset.sum_range_succ, Finset.sum_range_succ]
    simp [htail, add_assoc]
  have hreg' :
      (∑ j ∈ Finset.range N, causalKernelCellError α t h j) ≤
        ((Real.Gamma α)⁻¹)^2*(α-1)^2*h^3*h^(2*α-4)*
          ∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4) := by
    simpa [causalKernelCellError] using hreg
  have hbound' : causalKernelCellError α t h N+
      causalKernelCellError α t h (N+1) ≤
        ((Real.Gamma α)⁻¹)^2*((2*h)^(2*α-1)/(2*α-1)) := by
    simpa [causalKernelCellError, Nat.add_assoc] using hboundary
  rw [hsplit]
  exact add_le_add hreg' hbound'

/-- The completed-grid residual has the sharp fractional power in the range
`1 ≤ α < 3/2`.  This normalized form is convenient when it is consumed by
the actual Haar coefficient inequality. -/
theorem causalKernel_full_grid_average_error_sum_le_rate
    {α t h : ℝ} {M N : ℕ} (hα1 : 1 ≤ α) (hα15 : α < 3/2)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : (M:ℝ)*h=1) (hNM : N+2≤M)
    (hfar : ((N+1:ℕ):ℝ)*h ≤ t) (hnear : t ≤ ((N+2:ℕ):ℝ)*h) :
    (∑ j ∈ Finset.range M, causalKernelCellError α t h j) ≤
      (((Real.Gamma α)⁻¹)^2 * (α-1)^2 *
        (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4)) +
        ((Real.Gamma α)⁻¹)^2 * (2^(2*α-1)/(2*α-1))) *
        h^(2*α-1) := by
  have hfull := causalKernel_full_grid_average_error_sum_le
    hα1 hα15 hh hM hNM hfar hnear
  have hp : 0 < 2*α-1 := by linarith
  have hpow2 : (2*h)^(2*α-1) = 2^(2*α-1)*h^(2*α-1) :=
    Real.mul_rpow (by norm_num) hh.le
  have hpow3 : h^3*h^(2*α-4) = h^(2*α-1) := by
    rw [← Real.rpow_natCast h 3, ← Real.rpow_add hh]
    congr 1 <;> ring
  have hcoef1 : 0 ≤ ((Real.Gamma α)⁻¹)^2*(α-1)^2 := by positivity
  have hcoef2 : 0 ≤ ((Real.Gamma α)⁻¹)^2 := by positivity
  have hden : 0 < 2*α-1 := hp
  calc
    _ ≤ ((Real.Gamma α)⁻¹)^2*(α-1)^2 * h^3 * h^(2*α-4) *
          ∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4) +
        ((Real.Gamma α)⁻¹)^2 *
          ((2*h)^(2*α-1)/(2*α-1)) := hfull
    _ = (((Real.Gamma α)⁻¹)^2 * (α-1)^2 *
          (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4)) +
        ((Real.Gamma α)⁻¹)^2 * (2^(2*α-1)/(2*α-1))) *
          h^(2*α-1) := by
      calc
        _ = (((Real.Gamma α)⁻¹)^2*(α-1)^2) *
              (h^3*h^(2*α-4)) *
              (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4)) +
            ((Real.Gamma α)⁻¹)^2 *
              ((2*h)^(2*α-1)/(2*α-1)) := by ring
        _ = (((Real.Gamma α)⁻¹)^2*(α-1)^2) *
              h^(2*α-1) *
              (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*α-4)) +
            ((Real.Gamma α)⁻¹)^2 *
              (2^(2*α-1)*h^(2*α-1)/(2*α-1)) := by rw [hpow3,hpow2]
        _ = _ := by ring

/-- The actual squared error of the cellwise Taylor candidate on the regular
cells, together with the two cells meeting the causal singularity, has the
sharp fractional grid rate.  On the regular cells use the degree `m-1`
Taylor polynomial; on the two cells containing the singularity use zero.
All later cells have zero causal kernel.  This is the analytic approximation
estimate consumed by the nested piecewise-polynomial source spaces. -/
theorem causalKernel_full_grid_taylor_candidate_error_sum_le_rate
    {α t h : ℝ} {M N m : ℕ} (hα : 1/2 < α)
    (hm : 0 < m) (horder : α-1+1/2 < m)
    (hh : 0 < h) (hM : (M:ℝ)*h=1) (hNM : N+2≤M)
    (hfar : ((N+1:ℕ):ℝ)*h ≤ t) (hnear : t ≤ ((N+2:ℕ):ℝ)*h) :
    (∑ j ∈ Finset.range N,
      ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
        (causalKernel α t u - causalKernelCellTaylorApprox α t
          ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h) m u)^2) +
      (∫ u in ((N:ℝ)*h)..(((N+1:ℕ):ℝ)*h),
        (causalKernel α t u)^2) +
      (∫ u in (((N+1:ℕ):ℝ)*h)..(((N+2:ℕ):ℝ)*h),
        (causalKernel α t u)^2) ≤
      (((|(Real.Gamma α)⁻¹| *
          |(descPochhammer ℝ m).eval (α-1)| /
            (Nat.factorial (m-1):ℝ))^2 *
          (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*(α-1-m))) +
        ((Real.Gamma α)⁻¹)^2 * (2^(2*α-1)/(2*α-1))) *
        h^(2*α-1)) := by
  have hαpos : 0 < α := by linarith
  have hreg := causalKernel_regular_grid_taylor_error_sum_le
    hαpos hm horder hh hfar
  have hunit : ((N+2:ℕ):ℝ)*h ≤ 1 := by
    calc
      _ ≤ (M:ℝ)*h := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hNM
        · exact hh.le
      _ = 1 := hM
  have ht0 : 0 ≤ t := le_trans (by positivity : 0 ≤ ((N+1:ℕ):ℝ)*h) hfar
  have ht1 : t ≤ 1 := le_trans hnear hunit
  have hN1 : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_cast
  have hN2 : ((N+2:ℕ):ℝ) = (N:ℝ)+2 := by norm_cast
  have hstep1 : (N:ℝ)*h < ((N+1:ℕ):ℝ)*h := by rw [hN1]; nlinarith [hh]
  have hstep2 : ((N+1:ℕ):ℝ)*h < ((N+2:ℕ):ℝ)*h := by
    rw [hN1,hN2]
    nlinarith [hh]
  have hhat : (N:ℝ)*h ≤ t := le_trans hstep1.le hfar
  have hwidth : ((N+2:ℕ):ℝ)*h-(N:ℝ)*h ≤ 2*h := by
    rw [hN2]
    ring_nf
    nlinarith
  have hboundaryEnergy :
      (∫ u in ((N:ℝ)*h)..(((N+1:ℕ):ℝ)*h), (causalKernel α t u)^2) +
      (∫ u in (((N+1:ℕ):ℝ)*h)..(((N+2:ℕ):ℝ)*h), (causalKernel α t u)^2) ≤
      ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) := by
    have hcell1 := causalKernel_intervalIntegrable_of_unit hα ht0 ht1
      (by positivity : 0 ≤ (N:ℝ)*h) hstep1 (le_trans hstep2.le hunit)
    have hcell2 := causalKernel_intervalIntegrable_of_unit hα ht0 ht1
      (by positivity : 0 ≤ ((N+1:ℕ):ℝ)*h) hstep2 hunit
    have hblock := causalKernel_singular_cell_energy hα
      (by positivity : 0 ≤ (N:ℝ)*h) hhat hnear hunit
    have hpow : (t-(N:ℝ)*h)^(2*α-1) ≤ (2*h)^(2*α-1) := by
      apply Real.rpow_le_rpow (by linarith : 0 ≤ t-(N:ℝ)*h)
        (by linarith : t-(N:ℝ)*h ≤ 2*h)
      linarith
    have hGamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
    calc
      _ = ∫ u in ((N:ℝ)*h)..(((N+2:ℕ):ℝ)*h), (causalKernel α t u)^2 :=
        intervalIntegral.integral_add_adjacent_intervals hcell1.2 hcell2.2
      _ = ((Real.Gamma α)⁻¹)^2 *
          ((t-(N:ℝ)*h)^(2*α-1)/(2*α-1)) := by
        simpa [pow_two] using hblock
      _ ≤ ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) := by
        apply mul_le_mul_of_nonneg_left _ hGamma
        exact div_le_div_of_nonneg_right hpow (by linarith : 0 ≤ 2*α-1)
  have hpow2 : (2*h)^(2*α-1) = 2^(2*α-1)*h^(2*α-1) :=
    Real.mul_rpow (by norm_num) hh.le
  have hgamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  have hexp : 0 < 2*α-1 := by linarith
  have hreg' :
      (∑ j ∈ Finset.range N,
        ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
          (causalKernel α t u - causalKernelCellTaylorApprox α t
            ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h) m u)^2) ≤
      ((|(Real.Gamma α)⁻¹| *
          |(descPochhammer ℝ m).eval (α-1)| /
            (Nat.factorial (m-1):ℝ))^2 *
          (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*(α-1-m)))) * h^(2*α-1) := by
    simpa [div_pow, mul_assoc] using hreg
  calc
    _ =
        (∑ j ∈ Finset.range N,
          ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
            (causalKernel α t u - causalKernelCellTaylorApprox α t
              ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h) m u)^2) +
          ((∫ u in ((N:ℝ)*h)..(((N+1:ℕ):ℝ)*h), (causalKernel α t u)^2) +
            (∫ u in (((N+1:ℕ):ℝ)*h)..(((N+2:ℕ):ℝ)*h),
              (causalKernel α t u)^2)) := by ring
    _ ≤
        ((|(Real.Gamma α)⁻¹| *
            |(descPochhammer ℝ m).eval (α-1)| /
              (Nat.factorial (m-1):ℝ))^2 *
            (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*(α-1-m)))) * h^(2*α-1) +
          ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) :=
      add_le_add hreg' hboundaryEnergy
    _ = _ := by
      rw [hpow2]
      ring

end BrownianSharp.AlignmentFractionalPolynomialApproximation
