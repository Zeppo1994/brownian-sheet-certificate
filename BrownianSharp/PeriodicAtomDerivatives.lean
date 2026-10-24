import BrownianSharp.PeriodicNativeGrid
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace BrownianSharp

open BrownianSharp.Torus

/-- The real representative of a one-dimensional periodized dyadic atom. -/
def smoothDyadicAtomReal (s j : ℕ) (x : ℝ) : ℝ :=
  smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ))

/-- Iterated derivatives of the real representative scale by the expected
dyadic chain-rule factor. -/
theorem iteratedDeriv_smoothDyadicAtomReal (s j k : ℕ) :
    iteratedDeriv k (smoothDyadicAtomReal s j) =
      fun x => (2 : ℝ) ^ (s * k) *
        iteratedDeriv k smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ)) := by
  let c : ℝ := (2 : ℝ) ^ s
  let g : ℝ → ℝ := fun y => smoothAtom (y - (j : ℝ))
  have haffine : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => y - (j : ℝ)) := by
    fun_prop
  have hgTop : ContDiff ℝ (⊤ : ℕ∞) g := by
    change ContDiff ℝ (⊤ : ℕ∞) (smoothAtom ∘ fun y : ℝ => y - (j : ℝ))
    exact ContDiff.comp (n := (⊤ : ℕ∞)) smoothAtom_contDiff haffine
  have hg : ContDiff ℝ k g := by
    exact hgTop.of_le (by simp)
  have hscale := iteratedDeriv_comp_const_mul (n := k) (f := g) hg c
  have hoffset := iteratedDeriv_comp_sub_const (n := k)
    (f := smoothAtom) (s := (j : ℝ))
  funext x
  have h := congrFun hscale x
  have ho := congrFun hoffset (c * x)
  change iteratedDeriv k (fun x => smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ))) x = _
  rw [show (fun x : ℝ => smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ))) =
      (fun x => g (c * x)) by
        funext y
        simp [g, c]]
  rw [h, ho]
  rw [show c ^ k = (2 : ℝ) ^ (s * k) by dsimp [c]; rw [← pow_mul]]

/-- Every derivative of the bump vanishes to the left of its support. The
strict support margin in `smoothAtom_support_inner` gives a neighborhood
where the function itself is identically zero. -/
theorem iteratedDeriv_smoothAtom_eq_zero_of_nonpos (k : ℕ) {x : ℝ}
    (hx : x ≤ 0) : iteratedDeriv k smoothAtom x = 0 := by
  let U : Set ℝ := Set.Ioo (x - 1) (1 / 8)
  have hU : IsOpen U := isOpen_Ioo
  have hxU : x ∈ U := by
    constructor
    · linarith
    · norm_num
      exact lt_of_le_of_lt hx (by norm_num)
  have hEq : Set.EqOn smoothAtom (fun _ : ℝ => 0) U := by
    intro y hy
    exact smoothAtom_support_inner y (Or.inl (le_of_lt hy.2))
  calc
    iteratedDeriv k smoothAtom x = iteratedDerivWithin k smoothAtom U x :=
      (iteratedDerivWithin_of_isOpen hU hxU).symm
    _ = iteratedDerivWithin k (fun _ : ℝ => 0) U x :=
      iteratedDerivWithin_congr hEq hxU
    _ = 0 := by simp

/-- Every derivative of the bump vanishes to the right of its support. -/
theorem iteratedDeriv_smoothAtom_eq_zero_of_one_le (k : ℕ) {x : ℝ}
    (hx : 1 ≤ x) : iteratedDeriv k smoothAtom x = 0 := by
  let U : Set ℝ := Set.Ioo (7 / 8) (x + 1)
  have hU : IsOpen U := isOpen_Ioo
  have hxU : x ∈ U := by
    constructor
    · exact lt_of_lt_of_le (by norm_num) hx
    · linarith
  have hEq : Set.EqOn smoothAtom (fun _ : ℝ => 0) U := by
    intro y hy
    exact smoothAtom_support_inner y (Or.inr (le_of_lt hy.1))
  calc
    iteratedDeriv k smoothAtom x = iteratedDerivWithin k smoothAtom U x :=
      (iteratedDerivWithin_of_isOpen hU hxU).symm
    _ = iteratedDerivWithin k (fun _ : ℝ => 0) U x :=
      iteratedDerivWithin_congr hEq hxU
    _ = 0 := by simp

/-- A C∞ representative of the `k`th derivative on the quotient circle.
Its lift on `[0,1]` is the real iterated derivative of the affine bump. -/
noncomputable def periodizedDyadicAtomDerivative1 (s j : ℕ)
    (hj : j < 2 ^ s) (k : ℕ) : C(UnitAddCircle, ℝ) := by
  let f : ℝ → ℝ := iteratedDeriv k (smoothDyadicAtomReal s j)
  have hfend : f 0 = f 1 := by
    rw [show f = iteratedDeriv k (smoothDyadicAtomReal s j) by rfl,
      iteratedDeriv_smoothDyadicAtomReal]
    have hleft : (2 : ℝ) ^ s * 0 - (j : ℝ) ≤ 0 := by simp
    have hright : 1 ≤ (2 : ℝ) ^ s * 1 - (j : ℝ) := by
      have hj' : j + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hj
      have hjr : (j : ℝ) + 1 ≤ (2 : ℝ) ^ s := by exact_mod_cast hj'
      nlinarith
    change (2 : ℝ) ^ (s * k) *
        iteratedDeriv k smoothAtom ((2 : ℝ) ^ s * 0 - (j : ℝ)) =
      (2 : ℝ) ^ (s * k) *
        iteratedDeriv k smoothAtom ((2 : ℝ) ^ s * 1 - (j : ℝ))
    rw [iteratedDeriv_smoothAtom_eq_zero_of_nonpos k hleft,
      iteratedDeriv_smoothAtom_eq_zero_of_one_le k hright]
  have hcont : Continuous f := by
    have haffine : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ => (2 : ℝ) ^ s * x - (j : ℝ)) := by fun_prop
    have htop : ContDiff ℝ (⊤ : ℕ∞) (smoothDyadicAtomReal s j) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (smoothAtom ∘ fun x : ℝ => (2 : ℝ) ^ s * x - (j : ℝ))
      exact ContDiff.comp (n := (⊤ : ℕ∞)) smoothAtom_contDiff haffine
    have hi := htop.continuous_iteratedDeriv k (by simp)
    simpa [f] using hi
  exact ⟨AddCircle.liftIco (1 : ℝ) 0 f,
    AddCircle.liftIco_zero_continuous (p := (1 : ℝ)) hfend hcont.continuousOn⟩

/-- The quotient derivative agrees with its real lift on the fundamental
interval. -/
theorem periodizedDyadicAtomDerivative1_unit_interval (s j : ℕ)
    (hj : j < 2 ^ s) (k : ℕ) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    periodizedDyadicAtomDerivative1 s j hj k (x : UnitAddCircle) =
      iteratedDeriv k (smoothDyadicAtomReal s j) x := by
  change AddCircle.liftIco (1 : ℝ) 0
    (iteratedDeriv k (smoothDyadicAtomReal s j)) (x : UnitAddCircle) = _
  exact AddCircle.liftIco_zero_coe_apply hx

/-- At derivative order zero this construction is the existing periodized
atom used by the periodic covering argument. -/
theorem periodizedDyadicAtomDerivative1_zero_eq_existing
    (s j : ℕ) (hj : j < 2 ^ s) :
    periodizedDyadicAtomDerivative1 s j hj 0 =
      PeriodicCover.periodizedDyadicAtom1 s j hj := by
  ext x
  let y : Set.Ico (0 : ℝ) (0 + 1) := AddCircle.equivIco 1 0 x
  have hx : (y.val : UnitAddCircle) = x := by
    dsimp [y]
    simpa using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x))
  rw [← hx]
  have hy : y.val ∈ Set.Ico (0 : ℝ) 1 := by simpa using y.property
  rw [periodizedDyadicAtomDerivative1_unit_interval s j hj 0 y.val hy,
    periodizedDyadicAtom1_unit_interval s j hj y.val hy]
  simp [smoothDyadicAtomReal, iteratedDeriv_zero]

/-- A derivative of the periodized atom vanishes off its addressed dyadic
cell on the fundamental interval. -/
theorem periodizedDyadicAtomDerivative1_zero_of_outside_cell
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hout : x ≤ (j : ℝ) / (2 : ℝ) ^ s ∨
      ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ s ≤ x) :
    periodizedDyadicAtomDerivative1 s j hj k (x : UnitAddCircle) = 0 := by
  rw [periodizedDyadicAtomDerivative1_unit_interval s j hj k x hx,
    iteratedDeriv_smoothDyadicAtomReal]
  have hpow : 0 < (2 : ℝ) ^ s := by positivity
  rcases hout with hleft | hright
  · have harg : (2 : ℝ) ^ s * x - (j : ℝ) ≤ 0 := by
      rw [le_div_iff₀ hpow] at hleft
      nlinarith
    change (2 : ℝ) ^ (s * k) *
      iteratedDeriv k smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ)) = 0
    rw [iteratedDeriv_smoothAtom_eq_zero_of_nonpos k harg]
    simp
  · have harg : 1 ≤ (2 : ℝ) ^ s * x - (j : ℝ) := by
      rw [div_le_iff₀ hpow] at hright
      push_cast at hright
      nlinarith
    change (2 : ℝ) ^ (s * k) *
      iteratedDeriv k smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ)) = 0
    rw [iteratedDeriv_smoothAtom_eq_zero_of_one_le k harg]
    simp

/-- A finite global bound for each fixed iterated derivative of the bump. It
is obtained by maximizing on `[0,1]`; outside that interval all derivatives
vanish by the support lemmas above. -/
theorem exists_smoothAtom_iteratedDeriv_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |iteratedDeriv k smoothAtom x| ≤ C := by
  let f : ℝ → ℝ := fun x => |iteratedDeriv k smoothAtom x|
  have hf : Continuous f := by
    exact (smoothAtom_contDiff.continuous_iteratedDeriv k (by simp)).abs
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hnonempty : (Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨0, by constructor <;> norm_num⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hcompact.exists_isMaxOn hnonempty hf.continuousOn
  let C : ℝ := f x₀ + 1
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · calc
        f x ≤ f x₀ := hmax hx
        _ ≤ C := by dsimp [C]; linarith
    · have hx' : x ≤ 0 ∨ 1 ≤ x := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · exact Or.inl (le_of_lt hx)
        · exact Or.inr (le_of_lt hx)
      rcases hx' with hx' | hx'
      · rw [iteratedDeriv_smoothAtom_eq_zero_of_nonpos k hx']
        simp [f, C]
        positivity
      · rw [iteratedDeriv_smoothAtom_eq_zero_of_one_le k hx']
        simp [f, C]
        positivity

/-- If a continuous function is supported in `[0,1]`, its squared integral on
any interval containing `[0,1]` is bounded by the square of a global bound. -/
theorem intervalIntegral_sq_le_of_support_Icc
    {g : ℝ → ℝ} {A B C : ℝ}
    (hA : A ≤ 0) (hB : 1 ≤ B)
    (hg : Continuous g)
    (hleft : ∀ x ≤ 0, g x = 0)
    (hright : ∀ x, 1 ≤ x → g x = 0)
    (hbound : ∀ x, |g x| ≤ C) :
    (∫ x in A..B, |g x| ^ 2) ≤ C ^ 2 := by
  let f : ℝ → ℝ := fun x => |g x| ^ 2
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hInt : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hf.intervalIntegrable a b
  have hleftzero : (∫ x in A..0, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with x hx
    have hx0 : x ≤ 0 := by simpa [max_eq_right hA] using hx.2
    simp [f, hleft x hx0]
  have hrightzero : (∫ x in 1..B, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with x hx
    have hx1 : 1 ≤ x := by
      have hx1' : 1 < x := by simpa [min_eq_left hB] using hx.1
      exact le_of_lt hx1'
    simp [f, hright x hx1]
  have hdecomp : (∫ x in A..B, f x) =
      (∫ x in A..0, f x) + (∫ x in 0..1, f x) + (∫ x in 1..B, f x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hInt A 0) (hInt 0 B),
      ← intervalIntegral.integral_add_adjacent_intervals (hInt 0 1) (hInt 1 B)]
    ring
  have hmid : (∫ x in 0..1, f x) ≤ C ^ 2 := by
    calc
      (∫ x in 0..1, f x) ≤ ∫ x in 0..1, (fun _ : ℝ => C ^ 2) x := by
        apply intervalIntegral.integral_mono_on (hab := by norm_num)
          (hf := hInt 0 1) (hg := by simp)
        intro x hx
        dsimp [f]
        have hC : 0 ≤ C := le_trans (abs_nonneg (g x)) (hbound x)
        exact (sq_le_sq₀ (abs_nonneg (g x)) hC).2 (hbound x)
      _ = C ^ 2 := by simp
  rw [hdecomp, hleftzero, hrightzero, zero_add, add_zero]
  exact hmid

/-- The squared L² mass of the `k`th derivative on one period is bounded by
the dyadic cell length times the squared derivative supremum. -/
theorem periodizedDyadicAtomDerivative1_L2_sq_le
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) (hk : 1 ≤ k)
    {C : ℝ} (hC : ∀ x : ℝ, |iteratedDeriv k smoothAtom x| ≤ C) :
    (∫ x : UnitAddCircle,
      ‖(periodizedDyadicAtomDerivative1 s j hj k x : ℂ)‖ ^ 2
        ∂AddCircle.haarAddCircle) ≤ C ^ 2 * (2 : ℝ) ^ ((2 * k - 1) * s) := by
  let H : UnitAddCircle → ℝ := fun x =>
    ‖(periodizedDyadicAtomDerivative1 s j hj k x : ℂ)‖ ^ 2
  have hpre := AddCircle.intervalIntegral_preimage (T := 1) (t := (0 : ℝ)) H
  have hunit : (∫ x : UnitAddCircle, H x ∂AddCircle.haarAddCircle) =
      ∫ x in (0 : ℝ)..1, |iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ 2 := by
    rw [AddCircle.integral_haarAddCircle]
    norm_num
    rw [← hpre]
    norm_num only [zero_add]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    change ‖(periodizedDyadicAtomDerivative1 s j hj k (x : UnitAddCircle) : ℂ)‖ ^ 2 = _
    rw [periodizedDyadicAtomDerivative1_unit_interval s j hj k x
      ⟨hx.1.le, hx.2⟩]
    simp [H]
  have hcont : Continuous (iteratedDeriv k smoothAtom) :=
    smoothAtom_contDiff.continuous_iteratedDeriv k (by simp)
  have hzeroL : ∀ x ≤ 0, iteratedDeriv k smoothAtom x = 0 :=
    fun x hx => iteratedDeriv_smoothAtom_eq_zero_of_nonpos k hx
  have hzeroR : ∀ x, 1 ≤ x → iteratedDeriv k smoothAtom x = 0 :=
    fun x hx => iteratedDeriv_smoothAtom_eq_zero_of_one_le k hx
  have hpow : 0 < (2 : ℝ) ^ s := by positivity
  have hjle : j + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hj
  have hA : -(j : ℝ) ≤ 0 := by exact neg_nonpos.mpr (Nat.cast_nonneg j)
  have hjcast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ s := by exact_mod_cast hjle
  have hB : 1 ≤ (2 : ℝ) ^ s - j := by linarith
  have hbase := intervalIntegral_sq_le_of_support_Icc
    (g := iteratedDeriv k smoothAtom) (A := -(j : ℝ))
    (B := (2 : ℝ) ^ s - j) (C := C) hA hB hcont hzeroL hzeroR hC
  let g : ℝ → ℝ := fun x => |iteratedDeriv k smoothAtom x| ^ 2
  have hmeasure :
      (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), g x) ≤ C ^ 2 := by
    simpa [g] using hbase
  have hscale :
      (∫ x in (0 : ℝ)..1, |iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ 2) =
        ((2 : ℝ) ^ (s * k)) ^ 2 *
          ((2 : ℝ) ^ s)⁻¹ *
            (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), g x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1,
          ((2 : ℝ) ^ (s * k)) ^ 2 *
            g ((2 : ℝ) ^ s * x - j) := by
          apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
          intro x hx
          change |iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ 2 = _
          rw [iteratedDeriv_smoothDyadicAtomReal]
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (s * k))]
          calc
            ((2 : ℝ) ^ (s * k) * |iteratedDeriv k smoothAtom ((2 : ℝ) ^ s * x - j)|) ^ 2 =
                ((2 : ℝ) ^ (s * k)) ^ 2 *
                  |iteratedDeriv k smoothAtom ((2 : ℝ) ^ s * x - j)| ^ 2 := by ring
            _ = _ := by simp [g, sq_abs]
      _ = ((2 : ℝ) ^ (s * k)) ^ 2 *
          (∫ x in (0 : ℝ)..1, g ((2 : ℝ) ^ s * x - j)) := by
          rw [intervalIntegral.integral_const_mul]
      _ = ((2 : ℝ) ^ (s * k)) ^ 2 *
          ((2 : ℝ) ^ s)⁻¹ *
            (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), g x) := by
          rw [intervalIntegral.integral_comp_mul_sub g
            (by positivity : (2 : ℝ) ^ s ≠ 0) (j : ℝ)]
          simp [g, smul_eq_mul]
          ring
  have hsqint :
      (∫ x in (0 : ℝ)..1, |iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ 2) ≤
        ((2 : ℝ) ^ (s * k)) ^ 2 * ((2 : ℝ) ^ s)⁻¹ * C ^ 2 := by
    rw [hscale]
    have hfac : 0 ≤ ((2 : ℝ) ^ (s * k)) ^ 2 * ((2 : ℝ) ^ s)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hmeasure hfac
  calc
    (∫ x : UnitAddCircle,
      ‖(periodizedDyadicAtomDerivative1 s j hj k x : ℂ)‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      (∫ x in (0 : ℝ)..1, |iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ 2) := hunit
    _ ≤ ((2 : ℝ) ^ (s * k)) ^ 2 * ((2 : ℝ) ^ s)⁻¹ * C ^ 2 := hsqint
    _ = C ^ 2 * (2 : ℝ) ^ ((2 * k - 1) * s) := by
      have hsub : (2 * k - 1) + 1 = 2 * k := by omega
      have he : (s * k) * 2 = s + (2 * k - 1) * s := by
        calc
          (s * k) * 2 = s * (k * 2) := Nat.mul_assoc s k 2
          _ = s * (2 * k) := by rw [Nat.mul_comm k 2]
          _ = s * ((2 * k - 1) + 1) := by rw [hsub]
          _ = s * (2 * k - 1) + s := by rw [Nat.mul_add, Nat.mul_one]
          _ = s + (2 * k - 1) * s := by ring
      rw [← pow_mul, show (s * k) * 2 = s + (2 * k - 1) * s from he,
        pow_add]
      field_simp
      <;> ring

/-- At a fixed dyadic depth, two distinct addressed derivative atoms have
disjoint supports; their complex product therefore vanishes pointwise. -/
theorem periodizedDyadicAtomDerivative1_pairwise_product_eq_zero
    (s j j' : ℕ) (hj : j < 2 ^ s) (hj' : j' < 2 ^ s)
    (hjj' : j ≠ j') (k : ℕ) (x : UnitAddCircle) :
    (periodizedDyadicAtomDerivative1 s j hj k x : ℂ) *
      star (periodizedDyadicAtomDerivative1 s j' hj' k x : ℂ) = 0 := by
  let y : Set.Ico (0 : ℝ) (0 + 1) := AddCircle.equivIco 1 0 x
  have hx : (y.val : UnitAddCircle) = x := by
    dsimp [y]
    simpa using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x))
  rw [← hx]
  have hy : y.val ∈ Set.Ico (0 : ℝ) 1 := by simpa using y.property
  have hpow : 0 < (2 : ℝ) ^ s := by positivity
  have hzero :
      periodizedDyadicAtomDerivative1 s j hj k (y.val : UnitAddCircle) = 0 ∨
      periodizedDyadicAtomDerivative1 s j' hj' k (y.val : UnitAddCircle) = 0 := by
    rcases lt_or_gt_of_ne hjj' with hjlt | hjgt
    · have hsep : ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ s ≤
          (j' : ℝ) / (2 : ℝ) ^ s := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (Nat.succ_le_of_lt hjlt)
        · positivity
      by_cases hxcut : y.val ≤ ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ s
      · right
        exact periodizedDyadicAtomDerivative1_zero_of_outside_cell
          s j' hj' k y.val hy (Or.inl (le_trans hxcut hsep))
      · left
        exact periodizedDyadicAtomDerivative1_zero_of_outside_cell
          s j hj k y.val hy (Or.inr (le_of_not_ge hxcut))
    · have hsep : ((j' + 1 : ℕ) : ℝ) / (2 : ℝ) ^ s ≤
          (j : ℝ) / (2 : ℝ) ^ s := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (Nat.succ_le_of_lt hjgt)
        · positivity
      by_cases hxcut : y.val ≤ ((j' + 1 : ℕ) : ℝ) / (2 : ℝ) ^ s
      · left
        exact periodizedDyadicAtomDerivative1_zero_of_outside_cell
          s j hj k y.val hy (Or.inl (le_trans hxcut hsep))
      · right
        exact periodizedDyadicAtomDerivative1_zero_of_outside_cell
          s j' hj' k y.val hy (Or.inr (le_of_not_ge hxcut))
  rcases hzero with hzero | hzero
  · simp [hzero]
  · simp [hzero]

/-- Distinct equal-depth derivatives are orthogonal in scalar `L²`; the
integrand vanishes pointwise by cell support. -/
theorem periodizedDyadicAtomDerivative1_pairwise_inner_eq_zero
    (s j j' : ℕ) (hj : j < 2 ^ s) (hj' : j' < 2 ^ s)
    (hjj' : j ≠ j') (k : ℕ) :
    (∫ x : UnitAddCircle,
      (periodizedDyadicAtomDerivative1 s j hj k x : ℂ) *
        star (periodizedDyadicAtomDerivative1 s j' hj' k x : ℂ)
        ∂AddCircle.haarAddCircle) = 0 := by
  have hfun : (fun x : UnitAddCircle =>
      (periodizedDyadicAtomDerivative1 s j hj k x : ℂ) *
        star (periodizedDyadicAtomDerivative1 s j' hj' k x : ℂ)) =
      (fun _ => 0) := by
    funext x
    exact periodizedDyadicAtomDerivative1_pairwise_product_eq_zero
      s j j' hj hj' hjj' k x
  rw [hfun, integral_zero]

/-- Pointwise derivative size of the dyadic atom: the scale contributes the
expected `2^(s k)`, while the constant depends only on the derivative order. -/
theorem smoothDyadicAtomReal_iteratedDeriv_abs_le (s j k : ℕ) {C : ℝ}
    (hC : ∀ x : ℝ, |iteratedDeriv k smoothAtom x| ≤ C) (x : ℝ) :
    |iteratedDeriv k (smoothDyadicAtomReal s j) x| ≤
      C * (2 : ℝ) ^ (s * k) := by
  rw [iteratedDeriv_smoothDyadicAtomReal]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (s * k))]
  have hp : 0 ≤ (2 : ℝ) ^ (s * k) := pow_nonneg (by norm_num) _
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (hC ((2 : ℝ) ^ s * x - (j : ℝ))) hp

/-- Corresponding derivative bound on the periodic quotient. -/
theorem periodizedDyadicAtomDerivative1_abs_le_on_unit_interval
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) {C : ℝ}
    (hC : ∀ x : ℝ, |iteratedDeriv k smoothAtom x| ≤ C)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    |periodizedDyadicAtomDerivative1 s j hj k (x : UnitAddCircle)| ≤
      C * (2 : ℝ) ^ (s * k) := by
  rw [periodizedDyadicAtomDerivative1_unit_interval s j hj k x hx]
  exact smoothDyadicAtomReal_iteratedDeriv_abs_le s j k hC x

/-- The pointwise derivative bound holds on the entire quotient circle. -/
theorem periodizedDyadicAtomDerivative1_abs_le
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) {C : ℝ}
    (hC : ∀ x : ℝ, |iteratedDeriv k smoothAtom x| ≤ C)
    (x : UnitAddCircle) :
    |periodizedDyadicAtomDerivative1 s j hj k x| ≤ C * (2 : ℝ) ^ (s * k) := by
  let y : Set.Ico (0 : ℝ) (0 + 1) := AddCircle.equivIco 1 0 x
  have hx : (y.val : UnitAddCircle) = x := by
    dsimp [y]
    simpa using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x))
  rw [← hx]
  apply periodizedDyadicAtomDerivative1_abs_le_on_unit_interval s j hj k hC y.val
  simpa using y.property

/-- Casting the real-valued quotient derivative to `ℂ` commutes with its
fundamental-interval lift. -/
theorem periodizedDyadicAtomDerivative1_complex_eq_lift
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) :
    (fun x : UnitAddCircle =>
      (periodizedDyadicAtomDerivative1 s j hj k x : ℂ)) =
    AddCircle.liftIco 1 0
      (fun x : ℝ => ((iteratedDeriv k (smoothDyadicAtomReal s j) x : ℝ) : ℂ)) := by
  funext x
  let y : Set.Ico (0 : ℝ) (0 + 1) := AddCircle.equivIco 1 0 x
  have hx : (y.val : UnitAddCircle) = x := by
    dsimp [y]
    simpa using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x))
  rw [← hx]
  have hy : y.val ∈ Set.Ico (0 : ℝ) 1 := by simpa using y.property
  rw [periodizedDyadicAtomDerivative1_unit_interval s j hj k y.val hy]
  rw [AddCircle.liftIco_coe_apply y.property]

/-- Integration by parts on the unit circle: differentiating a periodized
atom multiplies its `n`th Fourier coefficient by `2π i n`.  The restriction
`n ≠ 0` is precisely the nonzero-frequency hypothesis needed by the Fourier
integration-by-parts theorem. -/
theorem periodizedDyadicAtomDerivative1_fourier_step
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff
      (fun x : UnitAddCircle =>
        (periodizedDyadicAtomDerivative1 s j hj (k + 1) x : ℂ)) n =
    (2 * Real.pi * Complex.I * (n : ℂ)) *
      fourierCoeff
        (fun x : UnitAddCircle =>
          (periodizedDyadicAtomDerivative1 s j hj k x : ℂ)) n := by
  let f : ℝ → ℂ := fun x =>
    ((iteratedDeriv k (smoothDyadicAtomReal s j) x : ℝ) : ℂ)
  let f' : ℝ → ℂ := fun x =>
    ((iteratedDeriv (k + 1) (smoothDyadicAtomReal s j) x : ℝ) : ℂ)
  have hfderiv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    dsimp [f, f']
    have haffine : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ => (2 : ℝ) ^ s * y - (j : ℝ)) := by fun_prop
    have htop : ContDiff ℝ (⊤ : ℕ∞)
        (smoothDyadicAtomReal s j) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (smoothAtom ∘ fun y : ℝ => (2 : ℝ) ^ s * y - (j : ℝ))
      exact ContDiff.comp (n := (⊤ : ℕ∞)) smoothAtom_contDiff haffine
    have htop' : ContDiff ℝ (↑(k + 1) : ℕ∞)
        (smoothDyadicAtomReal s j) := htop.of_le (by simp)
    have hd : Differentiable ℝ (iteratedDeriv k
        (smoothDyadicAtomReal s j)) := htop'.differentiable_iteratedDeriv' k
    have hda : HasDerivAt (iteratedDeriv k
        (smoothDyadicAtomReal s j))
        (iteratedDeriv (k + 1) (smoothDyadicAtomReal s j) x) x := by
      have h := (hd x).hasDerivAt
      simpa only [iteratedDeriv_succ] using h
    exact hda.ofReal_comp
  have hend : f 0 = f 1 := by
    dsimp [f]
    have h0 := congrFun (iteratedDeriv_smoothDyadicAtomReal s j k) 0
    have h1 := congrFun (iteratedDeriv_smoothDyadicAtomReal s j k) 1
    rw [h0, h1]
    have hleft : (2 : ℝ) ^ s * 0 - (j : ℝ) ≤ 0 := by simp
    have hj' : j + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hj
    have hjr : (j : ℝ) + 1 ≤ (2 : ℝ) ^ s := by exact_mod_cast hj'
    have hright : 1 ≤ (2 : ℝ) ^ s * 1 - (j : ℝ) := by nlinarith
    rw [iteratedDeriv_smoothAtom_eq_zero_of_nonpos k hleft,
      iteratedDeriv_smoothAtom_eq_zero_of_one_le k hright]
  have hcont : Continuous f' := by
    dsimp [f']
    have haffine : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ => (2 : ℝ) ^ s * x - (j : ℝ)) := by fun_prop
    have htop : ContDiff ℝ (⊤ : ℕ∞)
        (smoothDyadicAtomReal s j) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (smoothAtom ∘ fun x : ℝ => (2 : ℝ) ^ s * x - (j : ℝ))
      exact ContDiff.comp (n := (⊤ : ℕ∞)) smoothAtom_contDiff haffine
    exact RCLike.continuous_ofReal.comp
      (htop.continuous_iteratedDeriv (k + 1) (by simp))
  have hcoeff := fourierCoeff_liftIco_eq (T := 1) (a := 0) f n
  have hcoeff' := fourierCoeff_liftIco_eq (T := 1) (a := 0) f' n
  have hparts := fourierCoeffOn_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (by norm_num) hn
      (f := f) (f' := f') (fun x _ => hfderiv x)
      (hcont.intervalIntegrable 0 1)
  have hparts' : fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n =
      (1 / (-2 * Real.pi * Complex.I * (n : ℂ))) *
        (fourier (-n) (0 : UnitAddCircle) * (f 1 - f 0) -
        (1 : ℝ) * fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f' n) := by
    simpa using hparts
  rw [periodizedDyadicAtomDerivative1_complex_eq_lift s j hj (k + 1),
    periodizedDyadicAtomDerivative1_complex_eq_lift s j hj k]
  have hcoeff1 : fourierCoeff (AddCircle.liftIco 1 0
      (fun x : ℝ => ((iteratedDeriv k (smoothDyadicAtomReal s j) x : ℝ) : ℂ))) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
    simpa [f] using hcoeff
  have hcoeff2 : fourierCoeff (AddCircle.liftIco 1 0
      (fun x : ℝ => ((iteratedDeriv (k + 1) (smoothDyadicAtomReal s j) x : ℝ) : ℂ))) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f' n := by
    simpa [f'] using hcoeff'
  rw [hcoeff2, hcoeff1]
  have hend' : f 1 - f 0 = 0 := by rw [hend]; ring
  rw [hend'] at hparts'
  have hparts'' := hparts'
  field_simp [hn] at hparts''
  have hrel : fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f' n =
      (2 * Real.pi * Complex.I * (n : ℂ)) *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
    have hparts''' : fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n *
        (2 * Real.pi * Complex.I * (n : ℂ)) =
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f' n := by
      simpa [mul_assoc] using hparts''
    calc
      _ = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n *
          (2 * Real.pi * Complex.I * (n : ℂ)) := hparts'''.symm
      _ = _ := by ring
  simpa [f, f'] using hrel

/-- Iterating the one-step identity gives the exact multiplier for every
derivative order. -/
theorem periodizedDyadicAtomDerivative1_fourier_eq_pow
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff
        (fun x : UnitAddCircle =>
          (periodizedDyadicAtomDerivative1 s j hj k x : ℂ)) n =
      (2 * Real.pi * Complex.I * (n : ℂ)) ^ k *
        fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)) n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [periodizedDyadicAtomDerivative1_fourier_step s j hj k n hn, ih]
      rw [pow_succ]
      ring

/-- A Fourier coefficient on the normalized circle is bounded by a uniform
pointwise bound. -/
theorem fourierCoeff_norm_le_of_forall_norm_le
    {f : UnitAddCircle → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ C := by
  rw [fourierCoeff]
  have hbound' : ∀ x : UnitAddCircle, ‖fourier (-n) x • f x‖ ≤ C := by
    intro x
    rw [norm_smul]
    have hchar : ‖fourier (-n) x‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    rw [hchar, one_mul]
    exact hbound x
  calc
    ‖∫ x, fourier (-n) x • f x ∂AddCircle.haarAddCircle‖ ≤
        C * (AddCircle.haarAddCircle).real Set.univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ hbound')
    _ = C := by simp

/-- Fourier coefficients of the original atom have modulus at most one. -/
theorem periodizedDyadicAtomDerivative1_fourierCoeff_zero_norm_le_one
    (s j : ℕ) (hj : j < 2 ^ s) (n : ℤ) :
    ‖fourierCoeff (fun x : UnitAddCircle =>
      (periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)) n‖ ≤ 1 := by
  apply fourierCoeff_norm_le_of_forall_norm_le (by norm_num)
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa using periodizedDyadicAtomDerivative1_abs_le s j hj 0
    smoothAtom_abs_le_one x

/-- Repeated integration by parts yields inverse-frequency decay for the atom
itself, with the sharp dyadic derivative scaling displayed explicitly. -/
theorem periodizedDyadicAtomDerivative1_fourierCoeff_norm_le
    (s j : ℕ) (hj : j < 2 ^ s) (k : ℕ) (n : ℤ) (hn : n ≠ 0)
    {C : ℝ} (hC : ∀ x : ℝ, |iteratedDeriv k smoothAtom x| ≤ C) :
    ‖fourierCoeff (fun x : UnitAddCircle =>
      (periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)) n‖ ≤
        (C * (2 : ℝ) ^ (s * k)) / (2 * Real.pi * |(n : ℝ)|) ^ k := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (iteratedDeriv k smoothAtom 0))
    (hC 0)
  have hderiv : ∀ x : UnitAddCircle,
      ‖(periodizedDyadicAtomDerivative1 s j hj k x : ℂ)‖ ≤
        C * (2 : ℝ) ^ (s * k) := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact periodizedDyadicAtomDerivative1_abs_le s j hj k hC x
  have hcoeff := fourierCoeff_norm_le_of_forall_norm_le
    (mul_nonneg hC0 (by positivity : 0 ≤ (2 : ℝ) ^ (s * k))) hderiv n
  have hpow := periodizedDyadicAtomDerivative1_fourier_eq_pow s j hj k n hn
  have hA : ‖(2 * Real.pi * Complex.I * (n : ℂ))‖ =
      2 * Real.pi * |(n : ℝ)| := by
    simp [norm_mul, abs_of_pos Real.pi_pos, Complex.norm_intCast]
  have hden : 0 < 2 * Real.pi * |(n : ℝ)| := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (abs_pos.mpr (by exact_mod_cast hn))
  have hnorm : ‖fourierCoeff (fun x : UnitAddCircle =>
      (periodizedDyadicAtomDerivative1 s j hj k x : ℂ)) n‖ =
      (2 * Real.pi * |(n : ℝ)|) ^ k *
        ‖fourierCoeff (fun x : UnitAddCircle =>
          (periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)) n‖ := by
    rw [hpow, norm_mul, norm_pow, hA]
  calc
    ‖fourierCoeff (fun x : UnitAddCircle =>
        (periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)) n‖ =
      ‖fourierCoeff (fun x : UnitAddCircle =>
        (periodizedDyadicAtomDerivative1 s j hj k x : ℂ)) n‖ /
        (2 * Real.pi * |(n : ℝ)|) ^ k := by
          rw [hnorm]
          field_simp [ne_of_gt (pow_pos hden k)]
    _ ≤ (C * (2 : ℝ) ^ (s * k)) / (2 * Real.pi * |(n : ℝ)|) ^ k :=
      div_le_div_of_nonneg_right hcoeff (pow_nonneg hden.le _)

end BrownianSharp
