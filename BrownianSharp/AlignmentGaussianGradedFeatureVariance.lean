import BrownianSharp.AlignmentGaussianGradedTotalBudget

/-! Actual finite-coordinate variance bounds obtained from natural grade fibers. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentGaussianGradedFeatureVariance
open AlignmentGaussianDiagonalCoordinates AlignmentGaussianGradedTotalBudget
open AlignmentGeometricRanks
variable {ι : Type} [Fintype ι]

theorem graded_contracted_square_sum_le (grade : ι → ℕ) (c : ι → ℝ)
    {q η C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hη : η^2=q/2)
    (hC : 0 ≤ C) (k N L : ℕ) (hbound : ∀ i, grade i < N+1+L)
    (henergy : ∀ g : ℕ, (∑ i : {i : ι // grade i = g}, (c i.val)^2) ≤
      C * ((g+1:ℕ):ℝ)^k*q^g) :
    (∑ i, (contractionScale η N (grade i)*c i)^2) ≤
      C*q^N*((N+1:ℕ):ℝ)^k*
        (polynomialBudget (1/2) 0 + polynomialBudget q k) := by
  classical
  let gradeFin : ι → Fin (N+1+L) := fun i => ⟨grade i,hbound i⟩
  have hfiber (g : Fin (N+1+L)) :
      (∑ i : {i : ι // gradeFin i = g},
        (contractionScale η N (grade i.val)*c i.val)^2) ≤
        (contractionScale η N g.val)^2 *
          (C*((g.val+1:ℕ):ℝ)^k*q^g.val) := by
    let eg : {i : ι // gradeFin i = g} ≃ {i : ι // grade i = g.val} :=
      { toFun := fun i => ⟨i.val,congrArg Fin.val i.property⟩
        invFun := fun i => ⟨i.val,Fin.ext i.property⟩
        left_inv := by intro i; rfl
        right_inv := by intro i; rfl }
    have heq : (∑ i : {i : ι // gradeFin i = g}, (c i.val)^2) =
        ∑ i : {i : ι // grade i = g.val}, (c i.val)^2 := by
      exact (Equiv.sum_comp eg
        (fun i : {i : ι // grade i = g.val} => (c i.val)^2))
    calc
      _ = ∑ i : {i : ι // gradeFin i = g},
          (contractionScale η N g.val)^2*(c i.val)^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiGrade : grade i.val = g.val := congrArg Fin.val i.property
        rw [hiGrade,mul_pow]
      _ = (contractionScale η N g.val)^2 *
          (∑ i : {i : ι // gradeFin i = g}, (c i.val)^2) := by rw [Finset.mul_sum]
      _ ≤ (contractionScale η N g.val)^2 *
          (C*((g.val+1:ℕ):ℝ)^k*q^g.val) := by
        rw [heq]
        exact mul_le_mul_of_nonneg_left (henergy g.val) (sq_nonneg _)
  have htotal := contracted_total_energy_sum_le hq0 hq1 hη k N L
  calc
    _ = ∑ g : Fin (N+1+L), ∑ i : {i : ι // gradeFin i = g},
        (contractionScale η N (grade i.val)*c i.val)^2 :=
      (Fintype.sum_fiberwise gradeFin
        (fun i => (contractionScale η N (grade i)*c i)^2)).symm
    _ ≤ ∑ g : Fin (N+1+L), (contractionScale η N g.val)^2 *
        (C*((g.val+1:ℕ):ℝ)^k*q^g.val) :=
      Finset.sum_le_sum (fun g hg => hfiber g)
    _ = C * (∑ g : Fin (N+1+L), (contractionScale η N g.val)^2 *
        (((g.val+1:ℕ):ℝ)^k*q^g.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ ≤ C * (q^N*((N+1:ℕ):ℝ)^k*
        (polynomialBudget (1/2) 0 + polynomialBudget q k)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [Fin.sum_univ_eq_sum_range (fun g : ℕ =>
        (contractionScale η N g)^2*(((g+1:ℕ):ℝ)^k*q^g)) (N+1+L)]
      exact htotal
    _ = _ := by ring

theorem graded_contracted_square_sum_le_uniform (grade : ι → ℕ) (c : ι → ℝ)
    {q η C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hη : η^2=q/2)
    (hC : 0 ≤ C) (k N : ℕ)
    (henergy : ∀ g : ℕ, (∑ i : {i : ι // grade i = g}, (c i.val)^2) ≤
      C * ((g+1:ℕ):ℝ)^k*q^g) :
    (∑ i, (contractionScale η N (grade i)*c i)^2) ≤
      C*q^N*((N+1:ℕ):ℝ)^k*
        (polynomialBudget (1/2) 0 + polynomialBudget q k) := by
  let L := (∑ i : ι, grade i)+1
  apply graded_contracted_square_sum_le grade c hq0 hq1 hη hC k N L _ henergy
  intro i
  have hi : grade i ≤ ∑ j : ι, grade j :=
    Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  dsimp [L]
  omega

end BrownianSharp.AlignmentGaussianGradedFeatureVariance
