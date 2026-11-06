import BrownianSharp.AlignmentPaperContinuumConfinement
import BrownianSharp.SmoothPeriodicConditional

/-! Exact equality between the real-cube atom sum and the periodic synthesis,
including both faces of the closed fundamental cube. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperContinuumSynthesis
open Torus AlignmentPaperContinuumGoodRegion AlignmentPaperContinuumConfinement

def realCubeToTorus {d:ℕ} (x:Fin d→ℝ) : UnitAddTorus (Fin d) :=
  fun i=>(x i:UnitAddCircle)

theorem periodizedDyadicAtom1_closed_interval (s j:ℕ) (hj:j<2^s)
    (x:ℝ) (hx:x∈Set.Icc (0:ℝ) 1) :
    PeriodicCover.periodizedDyadicAtom1 s j hj (x:UnitAddCircle)=
      smoothAtom ((2:ℝ)^s*x-(j:ℝ)) := by
  by_cases hlt:x<1
  · exact periodizedDyadicAtom1_unit_interval s j hj x ⟨hx.1,hlt⟩
  · have hxeq:x=1 := by linarith [hx.2]
    subst x
    have hone:((1:ℝ):UnitAddCircle)=0 := by
      exact_mod_cast AddCircle.coe_period (p:=(1:ℝ))
    rw [hone]
    have hz := periodizedDyadicAtom1_unit_interval s j hj 0 (by norm_num)
    rw [show ((0:ℝ):UnitAddCircle)=0 from rfl] at hz
    rw [hz]
    have hneg : (2:ℝ)^s*0-(j:ℝ)≤0 := by simp
    have hpos : 1≤(2:ℝ)^s*1-(j:ℝ) := by
      have hjr : (j:ℝ)+1≤(2:ℝ)^s := by exact_mod_cast Nat.succ_le_of_lt hj
      linarith
    rw [smoothAtom_support _ (Or.inl hneg),smoothAtom_support _ (Or.inr hpos)]

theorem periodicNativeAtom_realCubeToTorus {d n:ℕ}
    (a:LayerIndex d n) (x:Fin d→ℝ) (hx:x∈cubeSet d) :
    periodicNativeAtom a (realCubeToTorus x)=smoothCubeAtom x a := by
  change (∏i:Fin d,PeriodicCover.periodizedDyadicAtom1
    (layerIndexDepth a i) (layerIndexCell a i) (layerIndexCell_lt a i)
      (x i:UnitAddCircle))= _
  unfold smoothCubeAtom
  apply Finset.prod_congr rfl
  intro i hi
  apply periodizedDyadicAtom1_closed_interval
  exact hx i (Set.mem_univ i)

theorem smoothPeriodicSynthesis_realCubeToTorus {d n:ℕ}
    (z:LayerIndex d n→ℝ) (x:Fin d→ℝ) (hx:x∈cubeSet d) :
    smoothPeriodicSynthesis z (realCubeToTorus x)=cubeSynthesis z x := by
  unfold smoothPeriodicSynthesis cubeSynthesis
  apply Finset.sum_congr rfl
  intro a ha
  rw [periodicNativeAtom_realCubeToTorus a x hx]
  simp [smul_eq_mul,mul_comm]

end BrownianSharp.AlignmentPaperContinuumSynthesis
