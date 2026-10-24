import BrownianSharp.AlignmentFractionalTensorHaar
import BrownianSharp.AlignmentFractionalHaarBand
import BrownianSharp.AlignmentFractionalTranslation
import BrownianSharp.AlignmentFractionalHaarProjection
import BrownianSharp.AlignmentGaussianFractionalHaar
import BrownianSharp.AlignmentFractionalSharpBudgets
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalTensorHaarEnergy
open BrownianSharp
open BrownianSharp.AlignmentFractionalTensorHaar
open BrownianSharp.AlignmentFractionalHaarBand
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalSharpBudgets
open BrownianSharp.AlignmentFractionalHaarProjection
open BrownianSharp.AlignmentGaussianFractionalHaar
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation

def scalarAxisExponent (α : ℝ) : ℝ := min (2*α-1) 1

def scalarAxisDecay (α : ℝ) : ℝ := (2:ℝ)^(-scalarAxisExponent α)

theorem scalarAxisDecay_mem_Ioo {α : ℝ} (hα : 1/2 < α) :
    scalarAxisDecay α ∈ Set.Ioo 0 1 := by
  have hβ : 0 < scalarAxisExponent α := by
    dsimp [scalarAxisExponent]
    apply lt_min <;> linarith
  constructor
  · dsimp [scalarAxisDecay]
    exact Real.rpow_pos_of_pos (by norm_num) _
  · dsimp [scalarAxisDecay]
    rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
      (by linarith)

def scalarAxisBandConstant (α : ℝ) : ℝ :=
  ((Real.Gamma α)⁻¹)^2 * (2 + 2^(2*α-1)/(2*α-1))

def scalarAxisEnvelope (α : ℝ) (hα : 1/2 < α) : ℝ :=
  2*‖fullKernelVector α hα‖^2 + 2*scalarAxisBandConstant α + 1

/-- Uniform bound for the father coefficient, inherited from the full
translation orbit of the scalar kernel. -/
theorem father_coefficient_sq_le {α t : ℝ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (inner ℝ (kernelVector α t hα ht0 ht1)
      (sourceHaarFamily 0 none))^2 ≤ ‖fullKernelVector α hα‖^2 := by
  have hfather : ‖sourceHaarFamily 0 none‖ = 1 := by
    have hsq : ⟪sourceHaarFamily 0 none, sourceHaarFamily 0 none⟫ = 1 := by
      simpa [sourceHaarFamily] using
        (sourceDyadicCellIndicator_inner_self (n := 0) (j := ⟨0, by norm_num⟩))
    rw [real_inner_self_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (sourceHaarFamily 0 none)]
  have hkernel : ‖kernelVector α t hα ht0 ht1‖ ≤ ‖fullKernelVector α hα‖ := by
    rw [← translatedUnitKernelFamily_eq_kernelVector α t hα ht0 ht1]
    exact translatedUnitKernelFamily_norm_le α hα ⟨t, ⟨ht0, ht1⟩⟩
  have habs : |inner ℝ (kernelVector α t hα ht0 ht1)
      (sourceHaarFamily 0 none)| ≤ ‖fullKernelVector α hα‖ := by
    calc
      |inner ℝ (kernelVector α t hα ht0 ht1) (sourceHaarFamily 0 none)| ≤
          ‖kernelVector α t hα ht0 ht1‖ * ‖sourceHaarFamily 0 none‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ ‖fullKernelVector α hα‖ := by rw [hfather, mul_one]; exact hkernel
  have habsSq : |inner ℝ (kernelVector α t hα ht0 ht1)
      (sourceHaarFamily 0 none)|^2 =
        (inner ℝ (kernelVector α t hα ht0 ht1) (sourceHaarFamily 0 none))^2 := by
    rw [sq_abs]
  rw [← habsSq]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 habs

/-- Positive shifted grades in the finite source family are exactly one
ordinary mother band. This converts the scalar dyadic estimate into an
estimate for the actual grade fibers used by the tensor decomposition. -/
theorem scalarAxisGrade_succ_energy_le {α t : ℝ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (N r : ℕ) (hrN : r < N) (hr : 1 ≤ r) :
    (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r+1},
      (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^r)^(min (2*α-1) 1) := by
  classical
  let e : Fin (2^r) ≃
      {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r+1} :=
    Equiv.ofBijective
      (fun j => (⟨some ⟨⟨r, hrN⟩, j⟩, by simp [finiteHaarAxisGrade]⟩ :
        {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r+1}))
      (by
        constructor
        · intro j k hjk
          have h := congrArg Subtype.val hjk
          simp at h
          exact h
        · intro a
          rcases a with ⟨a, haGrade⟩
          cases a with
          | none => simp [finiteHaarAxisGrade] at haGrade
          | some b =>
              rcases b with ⟨s,j⟩
              have hs : s.val = r := by
                simp [finiteHaarAxisGrade] at haGrade
                omega
              have hsr : s = ⟨r, hrN⟩ := Fin.ext hs
              subst s
              exact ⟨j, by apply Subtype.ext; rfl⟩)
  calc
    (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r+1},
        (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) =
      ∑ j : Fin (2^r), (inner ℝ (kernelVector α t hα ht0 ht1)
        (tensorHaarAxis (e j).1))^2 := (Equiv.sum_comp e _).symm
    _ = ∑ j : Fin (2^r), (inner ℝ (kernelVector α t hα ht0 ht1)
        (sourceDyadicHaarMother r j))^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          change (inner ℝ (kernelVector α t hα ht0 ht1)
            (tensorHaarAxis (some ⟨⟨r, hrN⟩, j⟩)))^2 = _
          simp [tensorHaarAxis, sourceHaarFamily]
    _ = ∑ j : Fin (2^r), (inner ℝ (sourceDyadicHaarMother r j)
        (kernelVector α t hα ht0 ht1))^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [real_inner_comm]
    _ ≤ ((Real.Gamma α)⁻¹)^2 * (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^r)^(min (2*α-1) 1) :=
          causalKernelVector_haar_level_energy_le_rate hα ht0 ht1 r hr

/-- The first shifted grade consists of the single depth-zero mother and is
bounded uniformly by the full scalar kernel norm. -/
theorem scalarAxisGrade_one_energy_le {α t : ℝ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (N : ℕ) :
    (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 1},
      (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) ≤
      ‖fullKernelVector α hα‖^2 := by
  classical
  by_cases hN : 0 < N
  · let e : Fin 1 ≃ {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 1} :=
      Equiv.ofBijective
        (fun _ => (⟨some ⟨⟨0,hN⟩,⟨0,by norm_num⟩⟩, by simp [finiteHaarAxisGrade]⟩ :
          {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 1}))
        (by
          constructor
          · intro j k hjk
            apply Fin.ext
            have hj := j.isLt
            have hk := k.isLt
            omega
          · intro a
            rcases a with ⟨a, ha⟩
            cases a with
            | none => simp [finiteHaarAxisGrade] at ha
            | some b =>
                rcases b with ⟨s,j⟩
                have hs : s.val = 0 := by
                  simp [finiteHaarAxisGrade] at ha
                  omega
                have hzero : s = ⟨0,hN⟩ := Fin.ext hs
                subst s
                have hj : j = ⟨0, by norm_num⟩ := Fin.ext (by
                  have hj := j.isLt
                  simp at hj
                  omega)
                subst j
                exact ⟨⟨0,by norm_num⟩, by apply Subtype.ext; rfl⟩)
    have hmother : ‖sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0))‖ = 1 := by
      have hsq : ⟪sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0)),
          sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0))⟫ = 1 := by
        simpa using (orthonormal_iff_ite.mp
          (sourceDyadicHaarMother_orthonormal 0)
          (⟨0,by norm_num⟩ : Fin (2^0)) (⟨0,by norm_num⟩ : Fin (2^0)))
      rw [real_inner_self_eq_norm_sq] at hsq
      nlinarith [norm_nonneg (sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0)))]
    have hkernel : ‖kernelVector α t hα ht0 ht1‖ ≤ ‖fullKernelVector α hα‖ := by
      rw [← translatedUnitKernelFamily_eq_kernelVector α t hα ht0 ht1]
      exact translatedUnitKernelFamily_norm_le α hα ⟨t, ⟨ht0, ht1⟩⟩
    have habs : |inner ℝ (kernelVector α t hα ht0 ht1)
        (sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0)))| ≤ ‖fullKernelVector α hα‖ := by
      calc
        _ ≤ ‖kernelVector α t hα ht0 ht1‖ *
            ‖sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0))‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖fullKernelVector α hα‖ := by rw [hmother, mul_one]; exact hkernel
    have habsSq : |inner ℝ (kernelVector α t hα ht0 ht1)
        (sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0)))|^2 =
          (inner ℝ (kernelVector α t hα ht0 ht1)
            (sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0))))^2 := by
      rw [sq_abs]
    calc
      _ = (inner ℝ (kernelVector α t hα ht0 ht1)
          (sourceDyadicHaarMother 0 (⟨0,by norm_num⟩ : Fin (2^0))))^2 := by
            rw [(Equiv.sum_comp e (fun a =>
              (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2)).symm]
            simp [e, tensorHaarAxis, sourceHaarFamily]
      _ ≤ ‖fullKernelVector α hα‖^2 := by
            rw [← habsSq]
            exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 habs
  · have hempty : IsEmpty {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 1} := by
      refine ⟨fun a => ?_⟩
      rcases a with ⟨a, ha⟩
      cases a with
      | none => simp [finiteHaarAxisGrade] at ha
      | some b =>
          rcases b with ⟨s,j⟩
          have hs : s.val + 1 = 1 := by simpa [finiteHaarAxisGrade] using ha
          have hN0 : N = 0 := by omega
          have hlt : s.val < N := s.isLt
          omega
    letI : IsEmpty {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 1} := hempty
    simp

/-- The grade-zero axis fiber is just the father. -/
theorem scalarAxisGrade_zero_energy_le {α t : ℝ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (N : ℕ) :
    (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 0},
      (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) ≤
      ‖fullKernelVector α hα‖^2 := by
  classical
  have hsum :
      (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 0},
        (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) =
      (inner ℝ (kernelVector α t hα ht0 ht1)
        (sourceHaarFamily N none))^2 := by
    have huniq : ∀ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = 0},
        a.1 = none := by
      intro a
      rcases a with ⟨a, ha⟩
      cases a with
      | none => rfl
      | some b => simp [finiteHaarAxisGrade] at ha
    rw [Finset.sum_eq_single ⟨none, by simp [finiteHaarAxisGrade]⟩]
    · simp [tensorHaarAxis]
    · intro b hb hba
      have hval := huniq b
      exact (hba (Subtype.ext hval)).elim
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  rw [hsum]
  simpa [tensorHaarAxis, sourceHaarFamily] using father_coefficient_sq_le hα ht0 ht1

/-- Uniform scalar dyadic-grade envelope, including the father and the
depth-zero mother. The positive higher bands use the actual RL projection
estimate proved from cell averages. -/
theorem scalarAxisGrade_decay_bound {α t : ℝ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (N g : ℕ) :
    (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = g},
      (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) ≤
      scalarAxisEnvelope α hα * scalarAxisDecay α ^ g := by
  classical
  let β := scalarAxisExponent α
  let q := scalarAxisDecay α
  let B := ‖fullKernelVector α hα‖^2
  let D := scalarAxisBandConstant α
  have hβ0 : 0 < β := by
    dsimp [β, scalarAxisExponent]
    apply lt_min <;> linarith
  have hβ1 : β ≤ 1 := by dsimp [β, scalarAxisExponent]; exact min_le_right _ _
  have hq0 : 0 < q := by
    dsimp [q, scalarAxisDecay]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hqhalf : 1/2 ≤ q := by
    dsimp [q, scalarAxisDecay]
    calc
      (1/2:ℝ) = (2:ℝ)^(-1:ℝ) := by norm_num [Real.rpow_neg_one]
      _ ≤ (2:ℝ)^(-β) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (show (-1:ℝ) ≤ -β by linarith)
  have hB : 0 ≤ B := sq_nonneg _
  have hD : 0 ≤ D := by
    have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos (by linarith)
    have hden : 0 < 2*α-1 := by linarith
    dsimp [D, scalarAxisBandConstant]
    positivity
  have hC : 0 ≤ scalarAxisEnvelope α hα := by
    dsimp [scalarAxisEnvelope, D, B]
    positivity
  have hrate (r : ℕ) :
      (1/(2:ℝ)^r)^β = q^r := by
    dsimp [q, scalarAxisDecay]
    calc
      (1/(2:ℝ)^r)^β = ((2:ℝ)^r)^(-β) := by
        rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
      _ = (2:ℝ)^((r:ℝ) * (-β)) := by
        rw [← Real.rpow_natCast (2:ℝ) r]
        exact (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (r:ℝ) (-β)).symm
      _ = (2:ℝ)^(-β * (r:ℝ)) := by congr 1 <;> ring
      _ = ((2:ℝ)^(-β))^r := by
        simpa using AlignmentFractionalSharpBudgets.dyadic_decay_eq_pow β r
  by_cases hg0 : g = 0
  · subst g
    have h := scalarAxisGrade_zero_energy_le hα ht0 ht1 N
    calc
      _ ≤ B := by simpa [B] using h
      _ ≤ scalarAxisEnvelope α hα * scalarAxisDecay α ^ 0 := by
        have hc : B ≤ 2*B + 2*D + 1 := by linarith [hB, hD]
        simpa [scalarAxisEnvelope, B, D, pow_zero] using hc
  · by_cases hg1 : g = 1
    · subst g
      have h := scalarAxisGrade_one_energy_le hα ht0 ht1 N
      have hstep : B ≤ (2*B + 2*D + 1) * q := by
        calc
          B = (2:ℝ)*B*(1/2:ℝ) := by ring
          _ ≤ 2*B*q := by gcongr
          _ ≤ (2*B + 2*D + 1)*q := by
            apply mul_le_mul_of_nonneg_right _ hq0.le
            nlinarith [hB, hD]
      calc
        _ ≤ B := by simpa [B] using h
        _ ≤ scalarAxisEnvelope α hα * scalarAxisDecay α ^ 1 := by
          simpa [scalarAxisEnvelope, scalarAxisBandConstant, scalarAxisDecay,
            B, D, q] using hstep
    · have hg2 : 2 ≤ g := by omega
      by_cases hgN : g ≤ N
      · let r : ℕ := g-1
        have hrN : r < N := by dsimp [r]; omega
        have hrpos : 1 ≤ r := by dsimp [r]; omega
        have hband := scalarAxisGrade_succ_energy_le hα ht0 ht1 N r hrN hrpos
        have hgrade : r+1 = g := by dsimp [r]; omega
        have hrate' :
            (1/(2:ℝ)^r)^(min (2*α-1) 1) = q^r := by
          simpa [β, scalarAxisExponent] using hrate r
        have hstep : D*q^r ≤ (2*B+2*D+1)*q^g := by
          have hqbound : D ≤ 2*D*q := by nlinarith [hD, hqhalf]
          calc
            D*q^r = q^r*D := by ring
            _ ≤ q^r*(2*D*q) := mul_le_mul_of_nonneg_left hqbound
              (pow_nonneg hq0.le r)
            _ = 2*D*q^(r+1) := by rw [pow_succ]; ring
            _ ≤ (2*B+2*D+1)*q^(r+1) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq0.le (r+1))
              nlinarith [hB]
            _ = (2*B+2*D+1)*q^g := by rw [hgrade]
        calc
          _ ≤ D*q^r := by
            have hband' :
                (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r+1},
                  (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) ≤
                D*q^r := by
              calc
                _ ≤ scalarAxisBandConstant α *
                    (1/(2:ℝ)^r)^(min (2*α-1) 1) := by simpa [D, scalarAxisBandConstant] using hband
                _ = D*q^r := by
                  simpa [D, scalarAxisBandConstant] using
                    congrArg (fun x : ℝ => scalarAxisBandConstant α * x) hrate'
            rw [← hgrade]
            exact hband'
          _ ≤ scalarAxisEnvelope α hα * scalarAxisDecay α ^ g := by
            simpa [scalarAxisEnvelope, scalarAxisBandConstant, B, D, q] using hstep
      · have hempty : IsEmpty {a : FiniteHaarAxis N // finiteHaarAxisGrade a = g} := by
          refine ⟨fun a => ?_⟩
          rcases a with ⟨a, ha⟩
          cases a with
          | none =>
              have h0 : (0:ℕ) = g := by simpa [finiteHaarAxisGrade] using ha
              have hgzero : g = 0 := by omega
              omega
          | some b =>
              rcases b with ⟨r,j⟩
              have hrN : r.val + 1 ≤ N := Nat.succ_le_of_lt r.isLt
              have hgrade : r.val + 1 = g := by simpa [finiteHaarAxisGrade] using ha
              omega
        letI : IsEmpty {a : FiniteHaarAxis N // finiteHaarAxisGrade a = g} := hempty
        have hsum :
            (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = g},
              (inner ℝ (kernelVector α t hα ht0 ht1) (tensorHaarAxis a.1))^2) = 0 := by
          simp
        rw [hsum]
        exact mul_nonneg hC (pow_nonneg hq0.le g)



private def tensorGradeProfileOf {d N n : ℕ}
    (a : FiniteHaarGradeLayer d N n) : FiniteHaarGradeProfile d n :=
  ⟨fun i => finiteHaarAxisGrade (a.1 i), by
    simpa [finiteHaarGrade] using a.2⟩

private def tensorGradeProfileEquiv {d N n : ℕ} :
    FiniteHaarGradeLayer d N n ≃
      Σ r : FiniteHaarGradeProfile d n, FiniteHaarProfileFiber (N := N) r.1 where
  toFun a := ⟨tensorGradeProfileOf a, ⟨a.1, fun _ => rfl⟩⟩
  invFun p := ⟨p.2.1, by
    calc
      finiteHaarGrade p.2.1 = ∑ i : Fin d, finiteHaarAxisGrade (p.2.1 i) := by
        simp [finiteHaarGrade]
      _ = ∑ i : Fin d, p.1.1 i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact p.2.2 i
      _ = n := p.1.2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨r, a⟩
    have hsum : finiteHaarGrade a.1 = n := by
      calc
        finiteHaarGrade a.1 = ∑ i : Fin d, finiteHaarAxisGrade (a.1 i) := by
          simp [finiteHaarGrade]
        _ = ∑ i : Fin d, r.1 i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact a.2 i
        _ = n := r.2
    let x : FiniteHaarGradeLayer d N n := ⟨a.1, hsum⟩
    have hr : tensorGradeProfileOf x = r := by
      apply Subtype.ext
      funext i
      exact a.2 i
    apply Sigma.ext
    · change tensorGradeProfileOf x = r
      exact hr
    · have hshape : ∀ i, (tensorGradeProfileOf x).1 i = r.1 i := by
        intro i
        exact congrArg (fun z : FiniteHaarGradeProfile d n => z.1 i) hr
      have hnew : ∀ i, finiteHaarAxisGrade (x.1 i) = (tensorGradeProfileOf x).1 i := by
        intro i
        rfl
      change HEq (⟨x.1, hnew⟩ : FiniteHaarProfileFiber (N := N)
        (tensorGradeProfileOf x).1) a
      apply (Subtype.heq_iff_coe_eq (fun b => by
        constructor
        · intro hb i
          change finiteHaarAxisGrade (b i) = r.1 i
          rw [← hshape i]
          exact hb i
        · intro hb i
          change finiteHaarAxisGrade (b i) = (tensorGradeProfileOf x).1 i
          rw [hshape i]
          exact hb i)).2
      rfl

/-- The number of shifted-grade profiles is bounded by the expected
polynomial factor. -/
theorem tensorGradeProfile_card_le {d n : ℕ} (hd : 0 < d) :
    (Fintype.card (FiniteHaarGradeProfile d n) : ℝ) ≤ (n+1:ℝ)^(d-1) := by
  rw [finiteHaarGradeProfile_card d n hd]
  have heq : n + d - 1 = n + (d-1) := by omega
  rw [heq]
  have hnat := Nat.choose_add_le_add_one_pow n (d-1)
  exact_mod_cast hnat

/-- Actual tensor RL coefficients have an exponentially decaying total
Haar-grade energy, with the weak-composition polynomial multiplicity. -/
theorem tensorHaarGrade_energy_le {d N g : ℕ} (hd : 0 < d)
    (α : ℝ) (hα : 1/2 < α) (t : HaarQuarter.BrownianCubeAnchor d) :
    (∑ a : FiniteHaarGradeLayer d N g,
      tensorHaarCoefficient (fun _ : Fin d => α)
        (fun _ : Fin d => hα) t a.1 ^ 2) ≤
      scalarAxisEnvelope α hα ^ d *
        (g+1:ℝ)^(d-1) * scalarAxisDecay α ^ g := by
  classical
  let A := scalarAxisEnvelope α hα
  let q := scalarAxisDecay α
  have hα0 : 0 < α := by linarith
  have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
  have hden : 0 < 2*α-1 := by linarith
  have hD : 0 ≤ scalarAxisBandConstant α := by
    dsimp [scalarAxisBandConstant]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A, scalarAxisEnvelope]
    positivity
  have hq0 : 0 < q := by dsimp [q, scalarAxisDecay]; positivity
  rw [Fintype.sum_equiv (tensorGradeProfileEquiv (d := d) (N := N) (n := g))
    (fun a => tensorHaarCoefficient (fun _ : Fin d => α)
      (fun _ : Fin d => hα) t a.1 ^ 2)
    (fun p => tensorHaarCoefficient (fun _ : Fin d => α)
      (fun _ : Fin d => hα) t p.2.1 ^ 2)
    (by intro a; rfl)]
  rw [Fintype.sum_sigma]
  have hprofile (r : FiniteHaarGradeProfile d g) :
      (∑ a : FiniteHaarProfileFiber (N := N) r.1,
        tensorHaarCoefficient (fun _ : Fin d => α)
          (fun _ : Fin d => hα) t a.1 ^ 2) ≤ A^d*q^g := by
    rw [tensorHaarProfile_energy_eq_product
      (α := fun _ : Fin d => α) (hα := fun _ : Fin d => hα) t r.1 r.2]
    have hfac (i : Fin d) :
        (∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r.1 i},
          (inner ℝ (kernelVector α (t.val i) hα (t.property i).1 (t.property i).2)
            (tensorHaarAxis a.1))^2) ≤ A*q^(r.1 i) := by
      simpa [A, q, scalarAxisDecay] using
        scalarAxisGrade_decay_bound hα (t.property i).1 (t.property i).2 N (r.1 i)
    have hprod :
        (∏ i : Fin d,
          ∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r.1 i},
            (inner ℝ (kernelVector α (t.val i) hα (t.property i).1 (t.property i).2)
              (tensorHaarAxis a.1))^2) ≤
        ∏ i : Fin d, A*q^(r.1 i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg fun a ha => sq_nonneg
          (inner ℝ (kernelVector α (t.val i) hα (t.property i).1 (t.property i).2)
            (tensorHaarAxis a.1))
      · intro i hi
        exact hfac i
    calc
      _ ≤ ∏ i : Fin d, A*q^(r.1 i) := hprod
      _ = A^d*q^g := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ]
        rw [Finset.prod_pow_eq_pow_sum]
        simp [r.2]
  calc
    _ = ∑ r : FiniteHaarGradeProfile d g,
        ∑ a : FiniteHaarProfileFiber (N := N) r.1,
          tensorHaarCoefficient (fun _ : Fin d => α)
            (fun _ : Fin d => hα) t a.1 ^ 2 := by
        simp only [Fintype.sum_sigma]
    _ ≤ ∑ _r : FiniteHaarGradeProfile d g, A^d*q^g := by
        apply Finset.sum_le_sum
        intro r hr
        exact hprofile r
    _ = (Fintype.card (FiniteHaarGradeProfile d g) : ℝ) * (A^d*q^g) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (g+1:ℝ)^(d-1) * (A^d*q^g) := by
        apply mul_le_mul_of_nonneg_right (tensorGradeProfile_card_le hd)
          (mul_nonneg (pow_nonneg hA d) (pow_nonneg hq0.le g))
    _ = A^d * (g+1:ℝ)^(d-1) * q^g := by ring

