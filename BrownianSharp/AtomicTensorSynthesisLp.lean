import BrownianSharp.AtomicSynthesisLp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic

/-! Finite-p synthesis estimates for fixed tensor dyadic shapes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp

private theorem prod_le_prod_nonneg_real {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hle : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact mul_le_mul (hle i (Finset.mem_insert_self _ _)) (ih
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hg j (Finset.mem_insert_of_mem hj))
        (fun j hj => hle j (Finset.mem_insert_of_mem hj)))
        (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (hg i (Finset.mem_insert_self _ _))

/-- Raising the absolute value of a finite product to a positive real power
factorizes coordinatewise. -/
theorem abs_finset_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (p : ℝ) :
    |∏ i ∈ s, f i| ^ p = ∏ i ∈ s, |f i| ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, abs_mul]
      calc
        (|f i| * |∏ j ∈ s, f j|) ^ p =
            |f i| ^ p * |∏ j ∈ s, f j| ^ p :=
          Real.mul_rpow (abs_nonneg _) (abs_nonneg _)
        _ = |f i| ^ p * ∏ j ∈ s, |f j| ^ p := by
          exact congrArg (fun z : ℝ => |f i| ^ p * z) ih

/-- Cell addresses for one fixed dyadic shape in a product torus. -/
abbrev DyadicShapeCell (d : ℕ) (s : Fin d → ℕ) :=
  ∀ i : Fin d, Fin (2 ^ (s i))

/-- Tensor-product smooth atom at fixed coordinate depths and cell address. -/
def dyadicShapeAtom {d : ℕ} (s : Fin d → ℕ) (j : DyadicShapeCell d s)
    (x : UnitAddTorus (Fin d)) : ℝ :=
  ∏ i : Fin d,
    periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0 (x i)

/-- A tensor atom's `p`th integral is at most the product of the dyadic cell
lengths. This is the actual Haar product integral, not a support assumption. -/
theorem dyadicShapeAtom_rpow_integral_le
    {d : ℕ} (s : Fin d → ℕ) (j : DyadicShapeCell d s)
    (p : ℝ) (hp : 0 < p) :
    (∫ x : UnitAddTorus (Fin d), |dyadicShapeAtom s j x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹ := by
  classical
  let coord : (i : Fin d) → UnitAddCircle → ℝ := fun i x =>
    |periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0 x| ^ p
  have hfun : (fun x : UnitAddTorus (Fin d) => |dyadicShapeAtom s j x| ^ p) =
      (fun x => ∏ i : Fin d, coord i (x i)) := by
    funext x
    dsimp [coord, dyadicShapeAtom]
    exact abs_finset_prod_rpow (Finset.univ : Finset (Fin d))
      (fun i => periodizedDyadicAtomDerivative1
        (s i) (j i).val (j i).isLt 0 (x i)) p
  rw [hfun, MeasureTheory.integral_fintype_prod_eq_prod]
  apply prod_le_prod_nonneg_real Finset.univ
  · intro i hi
    apply integral_nonneg_of_ae
    exact ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  · intro i hi
    exact inv_nonneg.mpr (by positivity)
  · intro i hi
    simpa [coord] using
      periodizedDyadicAtomDerivative1_rpow_integral_le
        (s i) (j i).val (j i).isLt p 1 hp

/-- One tensor coefficient on one cell contributes at most its `p`th power
times that cell's volume. -/
theorem dyadicShapeAtom_smul_rpow_integral_le
    {d : ℕ} (s : Fin d → ℕ) (j : DyadicShapeCell d s)
    (p c : ℝ) (hp : 0 < p) :
    (∫ x : UnitAddTorus (Fin d), |c * dyadicShapeAtom s j x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      |c| ^ p * ∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹ := by
  have hfactor : ∀ x : UnitAddTorus (Fin d),
      |c * dyadicShapeAtom s j x| ^ p = |c| ^ p * |dyadicShapeAtom s j x| ^ p := by
    intro x
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [show (fun x : UnitAddTorus (Fin d) => |c * dyadicShapeAtom s j x| ^ p) =
      (fun x => |c| ^ p * |dyadicShapeAtom s j x| ^ p) from by funext x; exact hfactor x,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (dyadicShapeAtom_rpow_integral_le s j p hp)
    (Real.rpow_nonneg (abs_nonneg c) _)

/-- At one fixed tensor shape, distinct cell addresses have disjoint nonzero
sets. -/
theorem dyadicShapeAtom_mul_eq_zero_of_ne
    {d : ℕ} (s : Fin d → ℕ) (j j' : DyadicShapeCell d s)
    (hjj' : j ≠ j') (x : UnitAddTorus (Fin d)) :
    dyadicShapeAtom s j x * dyadicShapeAtom s j' x = 0 := by
  classical
  have hcoord : ∃ i : Fin d, j i ≠ j' i := by
    by_contra h
    push_neg at h
    exact hjj' (funext h)
  obtain ⟨i, hji⟩ := hcoord
  have hval : (j i).val ≠ (j' i).val := by
    intro h
    exact hji (Fin.ext h)
  have hdisj := periodizedDyadicAtomDerivative1_pairwise_product_eq_zero
    (s i) (j i).val (j' i).val (j i).isLt (j' i).isLt hval 0 (x i)
  have hcoordzero :
      periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0 (x i) *
        periodizedDyadicAtomDerivative1 (s i) (j' i).val (j' i).isLt 0 (x i) = 0 := by
    have hcast :
        (((periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0 (x i) *
          periodizedDyadicAtomDerivative1 (s i) (j' i).val (j' i).isLt 0 (x i)) : ℝ) : ℂ) = 0 := by
      simpa [Complex.star_def] using hdisj
    exact_mod_cast hcast
  rw [dyadicShapeAtom, dyadicShapeAtom, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hcoordzero

/-- A tensor atom is pointwise bounded by one. -/
theorem dyadicShapeAtom_abs_le_one {d : ℕ} (s : Fin d → ℕ)
    (j : DyadicShapeCell d s) (x : UnitAddTorus (Fin d)) :
    |dyadicShapeAtom s j x| ≤ 1 := by
  classical
  rw [dyadicShapeAtom, Finset.abs_prod]
  calc
    (∏ i : Fin d,
      |periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0 (x i)|) ≤
      ∏ _i : Fin d, (1 : ℝ) := by
        apply prod_le_prod_nonneg_real (Finset.univ : Finset (Fin d))
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          norm_num
        · intro i hi
          simpa using periodizedDyadicAtomDerivative1_abs_le (s i)
            (j i).val (j i).isLt 0 smoothAtom_abs_le_one (x i)
    _ = 1 := by simp

private theorem dyadicShapeAtom_continuous {d : ℕ} (s : Fin d → ℕ)
    (j : DyadicShapeCell d s) :
    Continuous (dyadicShapeAtom s j) := by
  unfold dyadicShapeAtom
  exact continuous_finsetProd Finset.univ fun i hi =>
    (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0).continuous.comp
      (continuous_apply i)

/-- At a fixed rectangular dyadic shape, finite tensor synthesis has the
expected normalized `Lᵖ` power bound.  The cell supports are disjoint, and
each tensor cell has volume the product of its coordinate lengths. -/
theorem dyadicShapeLevel_rpow_integral_le
    {d : ℕ} (s : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p : ℝ) (hp : 0 < p) :
    (∫ x : UnitAddTorus (Fin d),
      |∑ j : DyadicShapeCell d s, c j * dyadicShapeAtom s j x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p := by
  classical
  let term : DyadicShapeCell d s → UnitAddTorus (Fin d) → ℝ :=
    fun j x => c j * dyadicShapeAtom s j x
  have hpairsum (x : UnitAddTorus (Fin d)) :
      |∑ j : DyadicShapeCell d s, term j x| ^ p =
        ∑ j : DyadicShapeCell d s, |term j x| ^ p := by
    apply abs_sum_rpow_eq_sum_abs_rpow_of_pairwise_mul_eq_zero
      (fun j => term j x) p hp
    intro i j hij
    have hzero := dyadicShapeAtom_mul_eq_zero_of_ne s i j hij x
    dsimp [term]
    calc
      (c i * dyadicShapeAtom s i x) * (c j * dyadicShapeAtom s j x) =
          (c i * c j) *
            (dyadicShapeAtom s i x * dyadicShapeAtom s j x) := by ring
      _ = 0 := by rw [hzero]; ring
  have hterm_cont (j : DyadicShapeCell d s) :
      Continuous (fun x : UnitAddTorus (Fin d) => |term j x| ^ p) := by
    dsimp [term]
    apply (Real.continuous_rpow_const hp.le).comp
    exact continuous_abs.comp
      (continuous_const.mul (dyadicShapeAtom_continuous s j))
  have hterm_bound (j : DyadicShapeCell d s) :
      ∀ x : UnitAddTorus (Fin d), |term j x| ^ p ≤ |c j| ^ p := by
    intro x
    dsimp [term]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    rw [abs_mul]
    have hatom : |dyadicShapeAtom s j x| ≤ 1 := dyadicShapeAtom_abs_le_one s j x
    calc
      |c j| * |dyadicShapeAtom s j x| ≤ |c j| * 1 :=
        mul_le_mul_of_nonneg_left hatom (abs_nonneg _)
      _ = |c j| := by simp
  have hterm_int (j : DyadicShapeCell d s) :
      Integrable (fun x : UnitAddTorus (Fin d) => |term j x| ^ p)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    apply MeasureTheory.Integrable.of_bound
      (hterm_cont j).aestronglyMeasurable (|c j| ^ p)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hterm_bound j x
  have hsum_int : Integrable
      (fun x : UnitAddTorus (Fin d) =>
        ∑ j : DyadicShapeCell d s, |term j x| ^ p)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
    MeasureTheory.integrable_finset_sum Finset.univ (fun j hj => hterm_int j)
  have hsum_integral := MeasureTheory.integral_finset_sum
    (μ := Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
    Finset.univ (fun j hj => hterm_int j)
  have hsum_eq :
      (fun x : UnitAddTorus (Fin d) =>
        |∑ j : DyadicShapeCell d s, term j x| ^ p) =
      (fun x => ∑ j : DyadicShapeCell d s, |term j x| ^ p) := by
    funext x
    exact hpairsum x
  rw [hsum_eq, hsum_integral]
  calc
    (∑ j : DyadicShapeCell d s,
        ∫ x : UnitAddTorus (Fin d), |term j x| ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∑ j : DyadicShapeCell d s,
        |c j| ^ p * ∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹ := by
          apply Finset.sum_le_sum
          intro j hj
          simpa only [term] using dyadicShapeAtom_smul_rpow_integral_le
            s j p (c j) hp
    _ = (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p := by
          calc
            _ = ∑ j : DyadicShapeCell d s,
                (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) * |c j| ^ p := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) *
                ∑ j : DyadicShapeCell d s, |c j| ^ p := by
                  rw [Finset.mul_sum]

/-- A derivative of one periodized atom has the expected finite-`p` bound:
the derivative contributes the dyadic factor, while its support still has
length at most one cell. -/
theorem periodizedDyadicAtomDerivative1_order_rpow_integral_le
    (s j k : ℕ) (hj : j < 2 ^ s) (p c C : ℝ) (hp : 0 < p)
    (hC : 0 ≤ C)
    (hderiv : ∀ x : ℝ, |iteratedDeriv k smoothAtom x| ≤ C) :
    (∫ x : UnitAddCircle,
      |c * periodizedDyadicAtomDerivative1 s j hj k x| ^ p
        ∂AddCircle.haarAddCircle) ≤
      ((2 : ℝ) ^ s)⁻¹ *
        (|c| * (2 : ℝ) ^ (s * k) * C) ^ p := by
  let H : UnitAddCircle → ℝ := fun x =>
    |c * periodizedDyadicAtomDerivative1 s j hj k x| ^ p
  have hpre := AddCircle.intervalIntegral_preimage (T := 1) (t := (0 : ℝ)) H
  have hunit : (∫ x : UnitAddCircle, H x ∂AddCircle.haarAddCircle) =
      ∫ x in (0 : ℝ)..1,
        |c * iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ p := by
    rw [AddCircle.integral_haarAddCircle]
    norm_num
    rw [← hpre]
    norm_num only [zero_add]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    change |c * periodizedDyadicAtomDerivative1 s j hj k
      (x : UnitAddCircle)| ^ p = _
    rw [periodizedDyadicAtomDerivative1_unit_interval s j hj k x
      ⟨hx.1.le, hx.2⟩]
    rw [abs_mul]
  let g : ℝ → ℝ := fun x =>
    c * (2 : ℝ) ^ (s * k) * iteratedDeriv k smoothAtom x
  have hg : Continuous g := by
    change Continuous (fun x : ℝ =>
      (c * (2 : ℝ) ^ (s * k)) * iteratedDeriv k smoothAtom x)
    exact continuous_const.mul
      (smoothAtom_contDiff.continuous_iteratedDeriv k (by simp))
  have hleft : ∀ x ≤ 0, g x = 0 := by
    intro x hx
    dsimp [g]
    rw [iteratedDeriv_smoothAtom_eq_zero_of_nonpos k hx]
    ring
  have hright : ∀ x, 1 ≤ x → g x = 0 := by
    intro x hx
    dsimp [g]
    rw [iteratedDeriv_smoothAtom_eq_zero_of_one_le k hx]
    ring
  let C' : ℝ := |c| * (2 : ℝ) ^ (s * k) * C
  have hC' : 0 ≤ C' := by
    dsimp [C']
    positivity
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ C' := by
    intro x hx
    dsimp [g, C']
    rw [abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)]
    calc
      |c| * (2 : ℝ) ^ (s * k) * |iteratedDeriv k smoothAtom x| ≤
          |c| * (2 : ℝ) ^ (s * k) * C :=
            mul_le_mul_of_nonneg_left (hderiv x)
              (mul_nonneg (abs_nonneg c) (pow_nonneg (by norm_num) _))
      _ = C' := by rfl
  have hpow : 0 < (2 : ℝ) ^ s := by positivity
  have hjle : j + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hj
  have hjcast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ s := by exact_mod_cast hjle
  have hA : -(j : ℝ) ≤ 0 := by exact neg_nonpos.mpr (Nat.cast_nonneg j)
  have hB : 1 ≤ (2 : ℝ) ^ s - j := by nlinarith
  have hbase := intervalIntegral_rpow_le_of_support_Icc
    (A := -(j : ℝ)) (B := (2 : ℝ) ^ s - j) hA hB hC' hp hg hleft hright hbound
  have hscale :
      (∫ x in (0 : ℝ)..1,
        |c * iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ p) =
        ((2 : ℝ) ^ s)⁻¹ * (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j),
          |g x| ^ p) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, |g ((2 : ℝ) ^ s * x - j)| ^ p := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp [g]
        rw [iteratedDeriv_smoothDyadicAtomReal]
        congr 1
        congr 1
        ring
      _ = ((2 : ℝ) ^ s)⁻¹ *
          (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), |g x| ^ p) := by
        rw [intervalIntegral.integral_comp_mul_sub (fun y : ℝ => |g y| ^ p)
          (by positivity : (2 : ℝ) ^ s ≠ 0) (j : ℝ)]
        simp [smul_eq_mul]
  calc
    (∫ x : UnitAddCircle,
      |c * periodizedDyadicAtomDerivative1 s j hj k x| ^ p
        ∂AddCircle.haarAddCircle) =
      (∫ x in (0 : ℝ)..1,
        |c * iteratedDeriv k (smoothDyadicAtomReal s j) x| ^ p) := by
          simpa [H] using hunit
    _ = ((2 : ℝ) ^ s)⁻¹ *
        (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), |g x| ^ p) := hscale
    _ ≤ ((2 : ℝ) ^ s)⁻¹ * C' ^ p :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hpow.le)
    _ = ((2 : ℝ) ^ s)⁻¹ *
        (|c| * (2 : ℝ) ^ (s * k) * C) ^ p := by rfl

/-- Tensor product of coordinatewise derivative atoms, allowing an order
depending on the coordinate. -/
def dyadicShapeDerivativeAtom {d : ℕ} (s k : Fin d → ℕ)
    (j : DyadicShapeCell d s) (x : UnitAddTorus (Fin d)) : ℝ :=
  ∏ i : Fin d,
    periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt (k i) (x i)

/-- The finite-`p` integral of a tensor derivative factors over coordinates.
Each coordinate's derivative contributes its scale to order `k i`, while
the support measure contributes one inverse cell length. -/
theorem dyadicShapeDerivativeAtom_rpow_integral_le
    {d : ℕ} (s k : Fin d → ℕ) (j : DyadicShapeCell d s)
    (p : ℝ) (hp : 0 < p) (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i x, |iteratedDeriv (k i) smoothAtom x| ≤ C i) :
    (∫ x : UnitAddTorus (Fin d),
      |dyadicShapeDerivativeAtom s k j x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∏ i : Fin d,
        (((2 : ℝ) ^ (s i))⁻¹ *
          (C i * (2 : ℝ) ^ (s i * k i)) ^ p) := by
  classical
  let coord : (i : Fin d) → UnitAddCircle → ℝ := fun i x =>
    |periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt (k i) x| ^ p
  have hfun : (fun x : UnitAddTorus (Fin d) =>
      |dyadicShapeDerivativeAtom s k j x| ^ p) =
      (fun x => ∏ i : Fin d, coord i (x i)) := by
    funext x
    dsimp [coord, dyadicShapeDerivativeAtom]
    exact abs_finset_prod_rpow (Finset.univ : Finset (Fin d))
      (fun i => periodizedDyadicAtomDerivative1
        (s i) (j i).val (j i).isLt (k i) (x i)) p
  rw [hfun, MeasureTheory.integral_fintype_prod_eq_prod]
  apply prod_le_prod_nonneg_real Finset.univ
  · intro i hi
    apply integral_nonneg_of_ae
    exact ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  · intro i hi
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Real.rpow_nonneg (mul_nonneg (hC i) (by positivity)) _)
  · intro i hi
    simpa [coord, mul_comm, mul_left_comm, mul_assoc] using
      periodizedDyadicAtomDerivative1_order_rpow_integral_le
        (s i) (j i).val (k i) (j i).isLt p 1 (C i) hp (hC i)
          (hderiv i)

/-- Distinct cells at a fixed rectangular shape have disjoint supports also
for coordinatewise derivatives of any fixed orders. -/
theorem dyadicShapeDerivativeAtom_mul_eq_zero_of_ne
    {d : ℕ} (s k : Fin d → ℕ) (j j' : DyadicShapeCell d s)
    (hjj' : j ≠ j') (x : UnitAddTorus (Fin d)) :
    dyadicShapeDerivativeAtom s k j x * dyadicShapeDerivativeAtom s k j' x = 0 := by
  classical
  have hcoord : ∃ i : Fin d, j i ≠ j' i := by
    by_contra h
    push_neg at h
    exact hjj' (funext h)
  obtain ⟨i, hji⟩ := hcoord
  have hval : (j i).val ≠ (j' i).val := by
    intro h
    exact hji (Fin.ext h)
  have hdisj := periodizedDyadicAtomDerivative1_pairwise_product_eq_zero
    (s i) (j i).val (j' i).val (j i).isLt (j' i).isLt hval (k i) (x i)
  have hcoordzero :
      periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt (k i) (x i) *
        periodizedDyadicAtomDerivative1 (s i) (j' i).val (j' i).isLt (k i) (x i) = 0 := by
    have hcast :
        (((periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt (k i) (x i) *
          periodizedDyadicAtomDerivative1 (s i) (j' i).val (j' i).isLt (k i) (x i)) : ℝ) : ℂ) = 0 := by
      simpa [Complex.star_def] using hdisj
    exact_mod_cast hcast
  rw [dyadicShapeDerivativeAtom, dyadicShapeDerivativeAtom, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hcoordzero

/-- Uniform pointwise envelope for a tensor derivative atom. -/
theorem dyadicShapeDerivativeAtom_abs_le
    {d : ℕ} (s k : Fin d → ℕ) (j : DyadicShapeCell d s)
    (x : UnitAddTorus (Fin d)) (C : Fin d → ℝ)
    (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i) :
    |dyadicShapeDerivativeAtom s k j x| ≤
      ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i)) := by
  classical
  rw [dyadicShapeDerivativeAtom, Finset.abs_prod]
  apply prod_le_prod_nonneg_real (Finset.univ : Finset (Fin d))
  · intro i hi
    exact abs_nonneg _
  · intro i hi
    exact mul_nonneg (hC i) (by positivity)
  · intro i hi
    simpa [mul_comm] using
      periodizedDyadicAtomDerivative1_abs_le (s i) (j i).val (j i).isLt (k i)
        (hderiv i) (x i)

private theorem dyadicShapeDerivativeAtom_continuous {d : ℕ}
    (s k : Fin d → ℕ) (j : DyadicShapeCell d s) :
    Continuous (dyadicShapeDerivativeAtom s k j) := by
  unfold dyadicShapeDerivativeAtom
  exact continuous_finsetProd Finset.univ fun i hi =>
    (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt (k i)).continuous.comp
      (continuous_apply i)

theorem dyadicShapeDerivativeAtom_smul_rpow_integral_le
    {d : ℕ} (s k : Fin d → ℕ) (j : DyadicShapeCell d s)
    (p c : ℝ) (hp : 0 < p) (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i x, |iteratedDeriv (k i) smoothAtom x| ≤ C i) :
    (∫ x : UnitAddTorus (Fin d),
      |c * dyadicShapeDerivativeAtom s k j x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      |c| ^ p * ∏ i : Fin d,
        (((2 : ℝ) ^ (s i))⁻¹ *
          (C i * (2 : ℝ) ^ (s i * k i)) ^ p) := by
  have hfactor : ∀ x : UnitAddTorus (Fin d),
      |c * dyadicShapeDerivativeAtom s k j x| ^ p =
        |c| ^ p * |dyadicShapeDerivativeAtom s k j x| ^ p := by
    intro x
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [show (fun x : UnitAddTorus (Fin d) =>
      |c * dyadicShapeDerivativeAtom s k j x| ^ p) =
      (fun x => |c| ^ p * |dyadicShapeDerivativeAtom s k j x| ^ p) from by
        funext x
        exact hfactor x,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (dyadicShapeDerivativeAtom_rpow_integral_le s k j p hp C hC hderiv)
    (Real.rpow_nonneg (abs_nonneg c) _)

/-- Finite tensor synthesis of a fixed derivative shape has a cellwise
`Lᵖ` estimate, with all scale dependence explicit. -/
theorem dyadicShapeDerivativeLevel_rpow_integral_le
    {d : ℕ} (s k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p : ℝ) (hp : 0 < p) (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i x, |iteratedDeriv (k i) smoothAtom x| ≤ C i) :
    (∫ x : UnitAddTorus (Fin d),
      |∑ j : DyadicShapeCell d s,
        c j * dyadicShapeDerivativeAtom s k j x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d,
        (((2 : ℝ) ^ (s i))⁻¹ *
          (C i * (2 : ℝ) ^ (s i * k i)) ^ p)) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p := by
  classical
  let term : DyadicShapeCell d s → UnitAddTorus (Fin d) → ℝ :=
    fun j x => c j * dyadicShapeDerivativeAtom s k j x
  have hpairsum (x : UnitAddTorus (Fin d)) :
      |∑ j : DyadicShapeCell d s, term j x| ^ p =
        ∑ j : DyadicShapeCell d s, |term j x| ^ p := by
    apply abs_sum_rpow_eq_sum_abs_rpow_of_pairwise_mul_eq_zero
      (fun j => term j x) p hp
    intro i j hij
    have hzero := dyadicShapeDerivativeAtom_mul_eq_zero_of_ne s k i j hij x
    dsimp [term]
    calc
      (c i * dyadicShapeDerivativeAtom s k i x) *
          (c j * dyadicShapeDerivativeAtom s k j x) =
          (c i * c j) *
            (dyadicShapeDerivativeAtom s k i x * dyadicShapeDerivativeAtom s k j x) := by ring
      _ = 0 := by rw [hzero]; ring
  let factor : ℝ := ∏ i : Fin d,
      (((2 : ℝ) ^ (s i))⁻¹ *
        (C i * (2 : ℝ) ^ (s i * k i)) ^ p)
  have hfactor_nonneg : 0 ≤ factor := by
    dsimp [factor]
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Real.rpow_nonneg (mul_nonneg (hC i) (by positivity)) _)
  have hterm_cont (j : DyadicShapeCell d s) :
      Continuous (fun x : UnitAddTorus (Fin d) => |term j x| ^ p) := by
    dsimp [term]
    apply (Real.continuous_rpow_const hp.le).comp
    exact continuous_abs.comp
      (continuous_const.mul (dyadicShapeDerivativeAtom_continuous s k j))
  have hAtomBound (j : DyadicShapeCell d s) (x : UnitAddTorus (Fin d)) :
      |term j x| ^ p ≤
        |c j| ^ p *
          (∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i))) ^ p := by
    dsimp [term]
    have hA : 0 ≤ ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i)) := by
      apply Finset.prod_nonneg
      intro i hi
      exact mul_nonneg (hC i) (by positivity)
    have hpoint : |c j| * |dyadicShapeDerivativeAtom s k j x| ≤
        |c j| * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i)) := by
      exact mul_le_mul_of_nonneg_left
        (dyadicShapeDerivativeAtom_abs_le s k j x C hC hderiv)
        (abs_nonneg _)
    calc
      |c j * dyadicShapeDerivativeAtom s k j x| ^ p =
          (|c j| * |dyadicShapeDerivativeAtom s k j x|) ^ p := by rw [abs_mul]
      _ ≤ (|c j| * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i))) ^ p :=
        Real.rpow_le_rpow (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hpoint hp.le
      _ = |c j| ^ p *
          (∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i))) ^ p :=
        Real.mul_rpow (abs_nonneg _) hA
  have hterm_int (j : DyadicShapeCell d s) :
      Integrable (fun x : UnitAddTorus (Fin d) => |term j x| ^ p)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    apply MeasureTheory.Integrable.of_bound
      (hterm_cont j).aestronglyMeasurable
      (|c j| ^ p * (∏ i : Fin d,
        (C i * (2 : ℝ) ^ (s i * k i))) ^ p)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hAtomBound j x
  have hsum_integral := MeasureTheory.integral_finset_sum
    (μ := Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
    Finset.univ (fun j hj => hterm_int j)
  have hsum_eq :
      (fun x : UnitAddTorus (Fin d) =>
        |∑ j : DyadicShapeCell d s, term j x| ^ p) =
      (fun x => ∑ j : DyadicShapeCell d s, |term j x| ^ p) := by
    funext x
    exact hpairsum x
  rw [hsum_eq, hsum_integral]
  calc
    (∑ j : DyadicShapeCell d s,
        ∫ x : UnitAddTorus (Fin d), |term j x| ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∑ j : DyadicShapeCell d s, |c j| ^ p * factor := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [factor, term] using
          dyadicShapeDerivativeAtom_smul_rpow_integral_le s k j p (c j) hp C hC hderiv
    _ = factor * ∑ j : DyadicShapeCell d s, |c j| ^ p := by
      calc
        _ = ∑ j : DyadicShapeCell d s, factor * |c j| ^ p := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = factor * ∑ j : DyadicShapeCell d s, |c j| ^ p := by
          rw [Finset.mul_sum]

/-- The corresponding finite-exponent `Lᵖ` norm bound, obtained from the
integral estimate rather than assumed as a synthesis hypothesis. -/
theorem dyadicShapeDerivativeLevel_lpNorm_le
    {d : ℕ} (s k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p : ℝ) (hp : 0 < p) (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i x, |iteratedDeriv (k i) smoothAtom x| ≤ C i) :
    MeasureTheory.lpNorm
      (fun x : UnitAddTorus (Fin d) =>
        ∑ j : DyadicShapeCell d s,
          c j * dyadicShapeDerivativeAtom s k j x)
      (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) ≤
      ((∏ i : Fin d,
        (((2 : ℝ) ^ (s i))⁻¹ *
          (C i * (2 : ℝ) ^ (s i * k i)) ^ p)) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p) ^ p⁻¹ := by
  classical
  let f : UnitAddTorus (Fin d) → ℝ := fun x =>
    ∑ j : DyadicShapeCell d s,
      c j * dyadicShapeDerivativeAtom s k j x
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  have hfcont : Continuous f := by
    dsimp [f]
    exact continuous_finsetSum Finset.univ fun j hj =>
      continuous_const.mul (dyadicShapeDerivativeAtom_continuous s k j)
  have hmeasure : μ =
      Measure.pi fun _ : Fin d => AddCircle.haarAddCircle := rfl
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hp0 hptop
    hfcont.aestronglyMeasurable]
  rw [ENNReal.toReal_ofReal hp.le]
  simp_rw [Real.norm_eq_abs]
  apply Real.rpow_le_rpow (by
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    _ (inv_nonneg.mpr hp.le)
  exact dyadicShapeDerivativeLevel_rpow_integral_le s k c p hp C hC hderiv


end BrownianSharp
