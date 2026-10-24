import BrownianSharp.HaarGridCoordinates

/-! Exact low/high grade partition of the finite Haar coordinate space. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter CameronMartin

theorem finiteHaarGrade_le {d N : ℕ} (a : FiniteHaarIndex d N) :
    finiteHaarGrade a≤d*N := by
  have haxis (i : Fin d) : finiteHaarAxisGrade (a i)≤N := by
    cases h : a i with
    | none => simp [finiteHaarAxisGrade]
    | some b => obtain ⟨r,j⟩ := b; simpa [finiteHaarAxisGrade] using r.isLt
  calc
    _ ≤ ∑ i : Fin d,N := Finset.sum_le_sum (fun i _ => haxis i)
    _ = _ := by simp

abbrev HaarHighGradeIndex (d N n₀ : ℕ) := Fin (d*N+1-n₀)

/-- All grades below `n₀` form one exact component; every higher grade is a
separate component for finite dictionary approximation. -/
def haarLowHighGrade {d N : ℕ} (n₀ : ℕ) (a : FiniteHaarIndex d N) :
    Option (HaarHighGradeIndex d N n₀) :=
  if h : finiteHaarGrade a<n₀ then none else
    some ⟨finiteHaarGrade a-n₀,by have := finiteHaarGrade_le a; omega⟩

@[simp] theorem haarLowHighGrade_eq_none {d N n₀ : ℕ} (a : FiniteHaarIndex d N) :
    haarLowHighGrade n₀ a=none ↔ finiteHaarGrade a<n₀ := by
  unfold haarLowHighGrade
  split_ifs <;> simp_all

@[simp] theorem haarLowHighGrade_eq_some {d N n₀ : ℕ}
    (a : FiniteHaarIndex d N) (j : HaarHighGradeIndex d N n₀) :
    haarLowHighGrade n₀ a=some j ↔ finiteHaarGrade a=n₀+j.val := by
  unfold haarLowHighGrade
  split_ifs with h
  · constructor
    · intro heq; cases heq
    · intro heq; omega
  · simp only [Option.some.injEq,Fin.ext_iff]
    omega

/-- Squared row norm of a high component is precisely the energy of the
corresponding actual mixed-Haar grade. -/
theorem haarHighGradeRow_norm_sq {d N n₀ : ℕ}
    (j : HaarHighGradeIndex d N n₀) (g : CubeDyadicGrid d N) :
    ‖coordinateLayerMask (haarLowHighGrade n₀) (some j) (haarGridRows d N g)‖^2 =
      ∑ a : {a : FiniteHaarIndex d N // finiteHaarGrade a=n₀+j.val},
        ⟪finiteHaarVector a.val,featureVector (cubeDyadicAnchor g)⟫^2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [coordinateLayerMask_apply,haarLowHighGrade_eq_some,haarGridRows,
    PiLp.toLp_apply]
  have heq : (∑ a : FiniteHaarIndex d N,
      if finiteHaarGrade a=n₀+j.val then
        ⟪finiteHaarVector a,featureVector (cubeDyadicAnchor g)⟫^2 else 0) =
      ∑ a : {a : FiniteHaarIndex d N // finiteHaarGrade a=n₀+j.val},
        ⟪finiteHaarVector a.val,featureVector (cubeDyadicAnchor g)⟫^2 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter (fun a : FiniteHaarIndex d N => finiteHaarGrade a=n₀+j.val))
      (by intro a; simp) (fun a => ⟪finiteHaarVector a,featureVector (cubeDyadicAnchor g)⟫^2)
  simpa [Real.norm_eq_abs,sq_abs] using heq

end BrownianSharp
