import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalTail
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalTensorAtoms
open AlignmentFractionalL2 AlignmentFractionalTranslation AlignmentFractionalDensity
  AlignmentFractionalTail AlignmentL2TensorProduct AlignmentFractionalTensorOperator

def cubeTensorAtom {d : ℕ} (s : Fin d → ℕ) (m : ∀ i, Fin (2^(s i))) :
    C(BrownianCubeAnchor d, ℝ) where
  toFun t := ∏ i, smoothAtom ((2:ℝ)^(s i) * t.val i - (m i).val)
  continuous_toFun := by
    apply continuous_finset_prod
    intro i hi
    exact smoothAtom_contDiff.continuous.comp
      ((continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)).sub continuous_const)

/-- Every tensor dyadic atom has a genuine RL source, with exactly the
coordinatewise sharp energy exponents and no extra shape-count loss. -/
theorem cubeTensorAtom_fractional_preimages {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : Fin d → ℕ) (m : ∀ i, Fin (2^(s i))),
      ∃ g : CameronMartin.UnitCubeL2 d,
        fractionalTensorRL a ha g = cubeTensorAtom s m ∧
        ‖g‖^2 ≤ C*(2:ℝ)^(∑ i, (2*a i-1)*(s i:ℝ)) := by
  classical
  choose C hC hpre using fun i => smoothAtom_dyadic_fractional_preimage (ha i)
  refine ⟨∏ i,C i,Finset.prod_pos (fun i hi => hC i),?_⟩
  intro s m
  choose v hv hvnorm using fun i => hpre i (s i) (m i).val (m i).isLt
  refine ⟨productToCube d (productVector v),?_,?_⟩
  · ext t
    rw [fractionalTensorRL_product]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hv i]
    rfl
  · have hn := cube_productVector_norm_le v
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
    calc
      ‖productToCube d (productVector v)‖^2 ≤ (∏ i,‖v i‖)^2 := hsq
      _ = ∏ i,‖v i‖^2 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ i, C i*(2:ℝ)^((2*a i-1)*(s i:ℝ)) := by
        exact Finset.prod_le_prod₀ (fun i hi => sq_nonneg _) (fun i hi => hvnorm i)
      _ = (∏ i,C i)*(2:ℝ)^(∑ i, (2*a i-1)*(s i:ℝ)) := by
        rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]

/-- The isotropic grade-n specialization used by the Gaussian entropy
obstruction. All constants are fixed before the grade and atom are chosen. -/
theorem isotropic_layer_preimages {d : ℕ} {r : ℝ} (hr : 1/2<r) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ s : Fin d → ℕ, (∑ i,s i)=n →
      ∀ m : ∀ i, Fin (2^(s i)), ∃ g : CameronMartin.UnitCubeL2 d,
        fractionalTensorRL (fun _ => r) (fun _ => hr) g = cubeTensorAtom s m ∧
        ‖g‖^2 ≤ C*(2:ℝ)^((2*r-1)*(n:ℝ)) := by
  obtain ⟨C,hC,hpre⟩ := cubeTensorAtom_fractional_preimages (fun _ : Fin d => r) (fun _ => hr)
  refine ⟨C,hC,?_⟩
  intro n s hs m
  obtain ⟨g,hg,hbound⟩ := hpre s m
  refine ⟨g,hg,?_⟩
  convert hbound using 1
  rw [← Finset.mul_sum, ← Nat.cast_sum, hs]

end BrownianSharp.AlignmentFractionalTensorAtoms
