import BrownianSharp.AlignmentPaperQuantization
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperQuantizationAtomicBridge

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

def boundedIndex {m : ℕ} (hm : 0 < m) (n : ℕ) : Fin m :=
  if hn : n < m then ⟨n, hn⟩ else ⟨0, hm⟩

theorem exists_nearest_index {m : ℕ} (hm : 0 < m) (c : Fin m → X) (x : X) :
    ∃ n : ℕ, n < m ∧ ∀ j : Fin m,
      edist x (c (boundedIndex hm n)) ≤ edist x (c j) := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin m => edist x (c i)) (by
      exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
  refine ⟨i.val, i.isLt, ?_⟩
  intro j
  simpa [boundedIndex, i.isLt] using hmin j (Finset.mem_univ j)

def nearestIndex {m : ℕ} (hm : 0 < m) (c : Fin m → X) (x : X) : Fin m :=
  boundedIndex hm (Nat.find (exists_nearest_index hm c x))

theorem nearestIndex_minimal {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (x : X) (j : Fin m) :
    edist x (c (nearestIndex hm c x)) ≤ edist x (c j) :=
  (Nat.find_spec (exists_nearest_index hm c x)).2 j

theorem nearestIndex_measurable {m : ℕ} (hm : 0 < m) (c : Fin m → X) :
    Measurable (nearestIndex hm c) := by
  classical
  have hfind : Measurable (fun x => Nat.find (exists_nearest_index hm c x)) := by
    apply measurable_find
    intro n
    change MeasurableSet {x : X | n < m ∧ ∀ j : Fin m,
      edist x (c (boundedIndex hm n)) ≤ edist x (c j)}
    rw [Set.ofPred_and]
    apply MeasurableSet.inter
    · exact (measurable_const : Measurable (fun _ : X => n))
        (measurableSet_Iio (a := m))
    · have hi (j : Fin m) : MeasurableSet {x : X |
          edist x (c (boundedIndex hm n)) ≤ edist x (c j)} :=
        measurableSet_le ((continuous_id.edist continuous_const).measurable)
          ((continuous_id.edist continuous_const).measurable)
      have heq : {x : X | ∀ j : Fin m,
          edist x (c (boundedIndex hm n)) ≤ edist x (c j)} =
          ⋂ j : Fin m, {x : X | edist x (c (boundedIndex hm n)) ≤ edist x (c j)} := by
        ext x
        simp
      rw [heq]
      exact MeasurableSet.iInter hi
  have hbounded : Measurable (boundedIndex hm) := measurable_of_countable _
  exact hbounded.comp hfind

def codebookProjection {m : ℕ} (hm : 0 < m) (c : Fin m → X) (x : X) : X :=
  c (nearestIndex hm c x)

theorem codebookProjection_measurable {m : ℕ} (hm : 0 < m) (c : Fin m → X) :
    Measurable (codebookProjection hm c) :=
  (measurable_of_finite c).comp (nearestIndex_measurable hm c)

theorem codebookProjection_edist_eq {m : ℕ} (hm : 0 < m) (c : Fin m → X) (x : X) :
    edist x (codebookProjection hm c x) = finiteCodebookDistortion hm c x := by
  apply le_antisymm
  · unfold finiteCodebookDistortion
    apply Finset.le_inf'
    intro j _
    exact nearestIndex_minimal hm c x j
  · unfold finiteCodebookDistortion codebookProjection
    exact Finset.inf'_le _ (Finset.mem_univ (nearestIndex hm c x))

theorem finiteCodebookDistortion_measurable {m : ℕ} (hm : 0 < m) (c : Fin m → X) :
    Measurable (finiteCodebookDistortion hm c) := by
  have h := measurable_id.edist (codebookProjection_measurable hm c)
  simpa only [id_eq, codebookProjection_edist_eq] using h

end BrownianSharp.AlignmentPaperQuantizationAtomicBridge

