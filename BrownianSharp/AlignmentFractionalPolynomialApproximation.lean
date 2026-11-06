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
