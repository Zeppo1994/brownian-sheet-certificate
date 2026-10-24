import BrownianSharp.FiniteHaarLayerEnergy

set_option maxHeartbeats 1000000

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace BrownianSharp
open HaarQuarter

noncomputable section

/-- All finite mixed-Haar indices whose shifted grades sum to `n`. -/
abbrev FiniteHaarGradeLayer (d N n : ℕ) :=
  {a : FiniteHaarIndex d N // finiteHaarGrade a = n}

/-- A weak-composition profile written as a finite function. -/
abbrev FiniteHaarGradeProfile (d n : ℕ) :=
  {r : Fin d → ℕ // ∑ i : Fin d, r i = n}

noncomputable instance finiteHaarGradeProfileFintype (d n : ℕ) :
    Fintype (FiniteHaarGradeProfile d n) := by
  classical
  apply Fintype.ofInjective
    (fun r : FiniteHaarGradeProfile d n => fun i =>
      (⟨r.1 i, Nat.lt_succ_of_le (by
        have hle : r.1 i ≤ n := by
          calc
            r.1 i ≤ ∑ j : Fin d, r.1 j :=
              Finset.single_le_sum (fun j _ => Nat.zero_le (r.1 j))
                (Finset.mem_univ i)
            _ = n := r.2
        exact hle)⟩ : Fin (n + 1)))
  intro r s h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

private def finiteHaarGradeProfileOf {d N n : ℕ}
    (a : FiniteHaarGradeLayer d N n) : FiniteHaarGradeProfile d n :=
  ⟨fun i => finiteHaarAxisGrade (a.1 i), by
    simpa [finiteHaarGrade] using a.2⟩

private def finiteHaarGradeProfileEquiv {d N n : ℕ} :
    FiniteHaarGradeLayer d N n ≃
      Σ r : FiniteHaarGradeProfile d n, FiniteHaarProfileFiber (N := N) r.1 where
  toFun a := ⟨finiteHaarGradeProfileOf a, ⟨a.1, fun _ => rfl⟩⟩
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
    have hr : finiteHaarGradeProfileOf x = r := by
      apply Subtype.ext
      funext i
      exact a.2 i
    apply Sigma.ext
    · change finiteHaarGradeProfileOf x = r
      exact hr
    · have hshape : ∀ i, (finiteHaarGradeProfileOf x).1 i = r.1 i := by
        intro i
        exact congrArg (fun z : FiniteHaarGradeProfile d n => z.1 i) hr
      have hnew : ∀ i, finiteHaarAxisGrade (x.1 i) =
          (finiteHaarGradeProfileOf x).1 i := by intro i; rfl
      change HEq (⟨x.1, hnew⟩ : FiniteHaarProfileFiber (N := N)
        (finiteHaarGradeProfileOf x).1) a
      apply (Subtype.heq_iff_coe_eq (fun b => by
        constructor
        · intro hb i
          change finiteHaarAxisGrade (b i) = r.1 i
          rw [← hshape i]
          exact hb i
        · intro hb i
          change finiteHaarAxisGrade (b i) = (finiteHaarGradeProfileOf x).1 i
          rw [hshape i]
          exact hb i)).2
      rfl

private def finiteHaarShapeOfProfile {d n : ℕ}
    (r : FiniteHaarGradeProfile d n) : Shape d n := by
  refine ⟨Finsupp.equivFunOnFinite.symm r.1, ?_⟩
  apply Finset.mem_finsuppAntidiag'.2
  constructor
  · simpa [Finsupp.sum_fintype] using r.2
  · simp

private def finiteHaarProfileShapeEquiv {d n : ℕ} :
    FiniteHaarGradeProfile d n ≃ Shape d n where
  toFun := finiteHaarShapeOfProfile
  invFun r := ⟨fun i => r.1 i, by
    have h := (Finset.mem_finsuppAntidiag'.mp r.2).1
    simpa [Finsupp.sum_fintype] using h⟩
  left_inv r := by
    apply Subtype.ext
    rfl
  right_inv r := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rfl

theorem finiteHaarGradeProfile_card (d n : ℕ) (hd : 0 < d) :
    Fintype.card (FiniteHaarGradeProfile d n) = Nat.choose (n + d - 1) (d - 1) := by
  classical
  rw [Fintype.card_congr finiteHaarProfileShapeEquiv, shape_card d n hd]

/-- The total squared endpoint-feature energy in shifted grade `n` is at most
`2^-n` times the number of weak compositions of `n` into `d` coordinates. -/
theorem finiteHaarGrade_grid_energy_le {d N n : ℕ} (hd : 0 < d)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    (∑ a : FiniteHaarGradeLayer d N n,
      finiteHaarGridCoefficient a.1 t ht ^ 2) ≤
      (Nat.choose (n + d - 1) (d - 1) : ℝ) / (2 : ℝ) ^ n := by
  classical
  rw [Fintype.sum_equiv
    (finiteHaarGradeProfileEquiv (d := d) (N := N) (n := n))
    (fun a => finiteHaarGridCoefficient a.1 t ht ^ 2)
    (fun p => finiteHaarGridCoefficient p.2.1 t ht ^ 2)
    (by intro a; rfl)]
  rw [Fintype.sum_sigma]
  calc
    (∑ r : FiniteHaarGradeProfile d n,
      ∑ a : FiniteHaarProfileFiber (N := N) r.1,
        finiteHaarGridCoefficient a.1 t ht ^ 2) ≤
      ∑ _r : FiniteHaarGradeProfile d n, (1 / (2 : ℝ) ^ n) := by
        apply Finset.sum_le_sum
        intro r hr
        simpa [r.2] using finiteHaarProfile_grid_energy_le
          (N := N) (r := r.1) t ht
    _ = (Nat.choose (n + d - 1) (d - 1) : ℝ) / (2 : ℝ) ^ n := by
      rw [Finset.sum_const, Finset.card_univ, finiteHaarGradeProfile_card d n hd]
      rw [one_div]
      ring

end
end BrownianSharp
