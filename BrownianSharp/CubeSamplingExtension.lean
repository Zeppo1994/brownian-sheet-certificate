import BrownianSharp.CubeDyadicGrid
import BrownianSharp.CameronMartinFeatureModulus
import BrownianSharp.FinitePartitionExtension

/-! Positive sampling extensions on an explicit finite cube grid. This
reduces uniform approximation of the actual integration ball to a finite
matrix problem with a quantitative square-root mesh error. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter CameronMartin

theorem exists_cube_sampling_extension (d N : ℕ) :
    ∃ E : (CubeDyadicGrid d N → ℝ) →ₗ[ℝ] C(BrownianCubeAnchor d,ℝ),
      (∀ a, ‖E a‖ ≤ ‖a‖) ∧
      ∀ g : AmbientL2 d, ‖g‖ ≤ 1 →
        ‖anchoredIntegrationPath g-E (fun j => anchoredIntegrationPath g (cubeDyadicAnchor j))‖ ≤
          Real.sqrt ((d:ℝ)*(2*((2:ℝ)^N)⁻¹)) := by
  let δ : ℝ := 2*((2:ℝ)^N)⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let U : CubeDyadicGrid d N → Set (BrownianCubeAnchor d) :=
    fun j => {x | ∀ i : Fin d, |x.val i-(cubeDyadicAnchor j).val i| < δ}
  have hUopen (j : CubeDyadicGrid d N) : IsOpen (U j) := by
    dsimp [U]
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun x : BrownianCubeAnchor d => x.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact isOpen_lt (continuous_abs.comp (hc.sub continuous_const)) continuous_const
  have hcover : (Set.univ : Set (BrownianCubeAnchor d)) ⊆ ⋃ j,U j := by
    intro x hx
    obtain ⟨j,hj⟩ := exists_cubeDyadicAnchor_near N x
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    intro i
    exact (hj i).trans (by
      dsimp [δ]
      have hpos : (0:ℝ)<((2:ℝ)^N)⁻¹ := by positivity
      linarith)
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUopen hcover
  refine ⟨finitePartitionExtension ρ,finitePartitionExtension_norm_le ρ,?_⟩
  intro g hg
  apply finitePartitionExtension_approx ρ cubeDyadicAnchor (anchoredIntegrationPath g)
    (Real.sqrt_nonneg _)
  intro j x hx
  have hxU : x ∈ U j := hρ j (subset_closure (show x ∈ Function.support (ρ j) from hx))
  exact anchoredIntegrationPath_modulus g hg x (cubeDyadicAnchor j) hδ.le
    (fun i => (hxU i).le)

end BrownianSharp
