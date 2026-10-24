import BrownianSharp.AlignmentPartitionDictionary
import BrownianSharp.UnitTorusMeasure
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open scoped BigOperators
open Set Metric
namespace BrownianSharp.AlignmentTorusSampling

def torusGridPoint {d N : ℕ} (j : Fin d → Fin (N+1)) :
    UnitAddTorus (Fin d) :=
  fun i => ((j i).val / (N : ℝ) : ℝ)

theorem circle_grid_close (N : ℕ) (hN : 0 < N) (x : AddCircle (1:ℝ)) :
    ∃ j : Fin (N+1), dist x ((j.val / (N:ℝ) : ℝ) : AddCircle (1:ℝ)) < 2/(N:ℝ) := by
  let y : ℝ := AddCircle.equivIco (1:ℝ) 0 x
  have hy0 : 0 ≤ y := (AddCircle.equivIco (1:ℝ) 0 x).property.1
  have hy1 : y < 1 := by simpa using (AddCircle.equivIco (1:ℝ) 0 x).property.2
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  let j : ℕ := ⌊(N:ℝ)*y⌋₊
  have hj : j ≤ N := Nat.floor_le_of_le (by nlinarith : (N:ℝ)*y ≤ (N:ℝ))
  refine ⟨⟨j, by omega⟩, ?_⟩
  have hlo : (j:ℝ) ≤ (N:ℝ)*y := Nat.floor_le (mul_nonneg hNr.le hy0)
  have hhi : (N:ℝ)*y < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have herr : |y-(j:ℝ)/(N:ℝ)| < 2/(N:ℝ) := by
    rw [abs_of_nonneg (by exact sub_nonneg.mpr ((div_le_iff₀ hNr).2 (by nlinarith)))]
    apply (lt_div_iff₀ hNr).2
    have hcancel : (j:ℝ)/(N:ℝ)*(N:ℝ) = j := div_mul_cancel₀ _ hNr.ne'
    nlinarith
  have heq : (y : AddCircle (1:ℝ)) = x := AddCircle.coe_equivIco
  have hdist : dist (y : AddCircle (1:ℝ)) (((j:ℝ)/(N:ℝ) : ℝ) : AddCircle (1:ℝ)) < 2/(N:ℝ) := by
    rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
    exact (QuotientAddGroup.norm_mk_le_norm).trans_lt (by simpa [Real.norm_eq_abs] using herr)
  exact (congrArg (fun z : AddCircle (1:ℝ) => dist z (((j:ℝ)/(N:ℝ) : ℝ) : AddCircle (1:ℝ))) heq).symm ▸ hdist

theorem torus_grid_close {d : ℕ} (N : ℕ) (hN : 0<N)
    (x : UnitAddTorus (Fin d)) :
    ∃ j : Fin d → Fin (N+1), dist x (torusGridPoint j) < 2/(N:ℝ) := by
  classical
  choose j hj using fun i => circle_grid_close N hN (x i)
  refine ⟨j, (dist_pi_lt_iff (by positivity)).2 ?_⟩
  exact hj

theorem torus_grid_partition {d : ℕ} (N : ℕ) (hN : 0<N) :
    ∃ φ : (Fin d → Fin (N+1)) → C(UnitAddTorus (Fin d),ℝ),
      (∀ j t, 0 ≤ φ j t) ∧
      (∀ t, ∑ j, φ j t = 1) ∧
      (∀ j t, φ j t ≠ 0 → dist t (torusGridPoint j) < 2/(N:ℝ)) := by
  classical
  let U : (Fin d → Fin (N+1)) → Set (UnitAddTorus (Fin d)) :=
    fun j => Metric.ball (torusGridPoint j) (2/(N:ℝ))
  have hcover : Set.univ ⊆ ⋃ j, U j := by
    intro t _
    obtain ⟨j,hj⟩ := torus_grid_close N hN t
    exact Set.mem_iUnion.mpr ⟨j,hj⟩
  obtain ⟨φ,hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U
    (fun _ => isOpen_ball) hcover
  refine ⟨fun j => φ j, φ.nonneg, ?_, ?_⟩
  · intro t
    simpa only [finsum_eq_sum_of_fintype] using φ.sum_eq_one (Set.mem_univ t)
  · intro j t ht
    exact hφ j (subset_closure ht)

theorem torus_grid_card (d N : ℕ) :
    Fintype.card (Fin d → Fin (N+1)) = (N+1)^d := by simp

end BrownianSharp.AlignmentTorusSampling
