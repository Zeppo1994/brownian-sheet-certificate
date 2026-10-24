import BrownianSharp.AlignmentHilbertTraceApproximation
import BrownianSharp.AlignmentApproximationNumberClosure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic

/-! Finite source refinements turn a uniform residual Hilbert--Schmidt budget
into an approximation-number bound. -/

noncomputable section
open scoped InnerProductSpace ENNReal

namespace BrownianSharp.AlignmentHilbertTraceRefinement

universe u

open BrownianSharp.AlignmentHilbertTraceApproximation
open BrownianSharp.AlignmentApproximationNumberClosure
open BrownianSharp.AlignmentFractionalApproximationNumbers

/-- The squared-image trace of a finite-dimensional Hilbert operator is
independent of the orthonormal basis used to compute it. -/
theorem output_norm_sq_sum_eq_of_orthonormal_basis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    (∑ i, ‖T (b i)‖^2) =
      ∑ i : Fin (Module.finrank ℝ E),
        ‖T ((gram_isPositive T).isSymmetric.eigenvectorBasis rfl i)‖^2 := by
  let G := gram T
  let bEig := (gram_isPositive T).isSymmetric.eigenvectorBasis
    (n := Module.finrank ℝ E) rfl
  have htraceB := LinearMap.trace_eq_sum_inner G.toLinearMap b
  have htraceEig := LinearMap.trace_eq_sum_inner G.toLinearMap bEig
  have hsumB : (∑ i, ‖T (b i)‖^2) = LinearMap.trace ℝ E G.toLinearMap := by
    calc
      (∑ i, ‖T (b i)‖^2) = ∑ i, ⟪b i, G (b i)⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ‖T (b i)‖^2 = ⟪T (b i), T (b i)⟫_ℝ := by
            rw [← real_inner_self_eq_norm_sq]
          _ = ⟪b i, T.adjoint (T (b i))⟫_ℝ := by rw [T.adjoint_inner_right]
      _ = LinearMap.trace ℝ E G.toLinearMap := htraceB.symm
  have hsumEig :
      (∑ i : Fin (Module.finrank ℝ E), ‖T (bEig i)‖^2) =
        LinearMap.trace ℝ E G.toLinearMap := by
    calc
      (∑ i : Fin (Module.finrank ℝ E), ‖T (bEig i)‖^2) =
          ∑ i, ⟪bEig i, G (bEig i)⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ‖T (bEig i)‖^2 = ⟪T (bEig i), T (bEig i)⟫_ℝ := by
            rw [← real_inner_self_eq_norm_sq]
          _ = ⟪bEig i, T.adjoint (T (bEig i))⟫_ℝ := by rw [T.adjoint_inner_right]
      _ = LinearMap.trace ℝ E G.toLinearMap := htraceEig.symm
  exact hsumB.trans hsumEig.symm

/-- If finite-dimensional source spaces containing a fixed base space capture
the feature operator uniformly, and the feature residual on each refinement
has squared trace at most `B`, then the strict-rank approximation number is
bounded by the Hilbert--Schmidt tail estimate. -/
theorem approximationNumber_le_of_nested_trace_refinements
    {H F : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : H →L[ℝ] F)
    (D k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hrefine : ∀ δ : ℝ, 0 < δ →
      ∃ (U V : Submodule ℝ H) (_hU : FiniteDimensional ℝ U)
        (_hV : FiniteDimensional ℝ V),
        U ≤ V ∧
        Module.rank ℝ (LinearMap.range
          ((T.comp U.starProjection : H →L[ℝ] F) : H →ₗ[ℝ] F)) ≤ (D : Cardinal) ∧
        ‖T - T.comp V.starProjection‖ ≤ δ ∧
        ∃ b : Fin (Module.finrank ℝ V) → V, Orthonormal ℝ b ∧
          (∑ i, ‖T (((ContinuousLinearMap.id ℝ H - U.starProjection)
              ((V.subtypeₗᵢ : V →ₗᵢ[ℝ] H) (b i))))‖^2) ≤ B) :
    approximationNumber T (D + k + 1) ≤ ENNReal.ofReal (Real.sqrt (B / (k+1:ℝ))) := by
  have htarget_nonneg : 0 ≤ Real.sqrt (B / (k+1:ℝ)) := Real.sqrt_nonneg _
  apply approximationNumber_le_of_arbitrarily_close_approximants
    T (D+k+1) (Real.sqrt (B/(k+1:ℝ))) htarget_nonneg
  intro ε hε
  obtain ⟨U,V,hU,hV,hUV,hbase,htail,htrace⟩ := hrefine ε hε
  letI := hU
  letI := hV
  let J : V →ₗᵢ[ℝ] H := V.subtypeₗᵢ
  let Jc : V →L[ℝ] H := J.toContinuousLinearMap
  let PV : H →L[ℝ] H := Jc.comp Jc.adjoint
  let R : V →L[ℝ] F := T.comp ((ContinuousLinearMap.id ℝ H - U.starProjection).comp Jc)
  have hPV : PV = V.starProjection := by
    dsimp [PV,Jc,J]
    simp [Submodule.starProjection, Submodule.adjoint_subtypeL]
  have hbaseV : U.starProjection.comp PV = U.starProjection := by
    rw [hPV]
    exact Submodule.starProjection_comp_starProjection_of_le hUV
  obtain ⟨b,hb,htraceB⟩ := htrace
  have htraceR :
      (∑ i : Fin (Module.finrank ℝ V),
        ‖R ((gram_isPositive R).isSymmetric.eigenvectorBasis rfl i)‖^2) ≤ B := by
    have hspanrank : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) =
        Module.finrank ℝ V := by
      rw [finrank_span_eq_card hb.linearIndependent]
      simp
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ :=
      Submodule.eq_top_of_finrank_eq hspanrank
    let bBasis : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V :=
      OrthonormalBasis.mk hb (by rw [hspan])
    have heq := output_norm_sq_sum_eq_of_orthonormal_basis R bBasis
    calc
      (∑ i : Fin (Module.finrank ℝ V),
          ‖R ((gram_isPositive R).isSymmetric.eigenvectorBasis rfl i)‖^2) =
        ∑ i : Fin (Module.finrank ℝ V), ‖R (bBasis i)‖^2 := heq.symm
      _ ≤ B := by
        simpa [R, J, Jc, bBasis, OrthonormalBasis.coe_mk] using htraceB
  obtain ⟨A,hArank,hAerr⟩ := exists_rank_k_approximation_of_trace R k
  have hAcard : Module.rank ℝ (LinearMap.range (A : V →ₗ[ℝ] F)) ≤ (k : Cardinal) := by
    letI : Module.Finite ℝ (LinearMap.range (A : V →ₗ[ℝ] F)) :=
      Module.Finite.of_surjective (A.toLinearMap.rangeRestrict)
        (LinearMap.surjective_rangeRestrict _)
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hArank
  have hAcomp : Module.rank ℝ (LinearMap.range
      ((A.comp Jc.adjoint : H →L[ℝ] F) : H →ₗ[ℝ] F)) ≤ (k : Cardinal) := by
    exact (LinearMap.rank_comp_le_left _ _).trans hAcard
  let C : H →L[ℝ] F := T.comp U.starProjection + A.comp Jc.adjoint
  have hCrank : Module.rank ℝ (LinearMap.range (C : H →ₗ[ℝ] F)) < ((D+k+1:ℕ):Cardinal) := by
    have hadd := LinearMap.rank_add_le
      ((T.comp U.starProjection : H →L[ℝ] F) : H →ₗ[ℝ] F)
      ((A.comp Jc.adjoint : H →L[ℝ] F) : H →ₗ[ℝ] F)
    change Module.rank ℝ (LinearMap.range
      (((T.comp U.starProjection : H →L[ℝ] F) : H →ₗ[ℝ] F) +
        ((A.comp Jc.adjoint : H →L[ℝ] F) : H →ₗ[ℝ] F))) < _
    exact lt_of_le_of_lt (hadd.trans (add_le_add hbase hAcomp)) (by
      exact_mod_cast (show D+k < D+k+1 by omega))
  have hJadj : ‖Jc.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact J.norm_toContinuousLinearMap_le
  have hRidentity :
      R.comp Jc.adjoint + T.comp (ContinuousLinearMap.id ℝ H - PV) =
        T.comp (ContinuousLinearMap.id ℝ H - U.starProjection) := by
    ext x
    have hx : U.starProjection (PV x) = U.starProjection x := by
      have h := congrArg (fun L : H →L[ℝ] H => L x) hbaseV
      simpa [ContinuousLinearMap.comp_apply] using h
    change T (PV x - U.starProjection (PV x)) + T (x - PV x) =
      T (x - U.starProjection x)
    rw [map_sub, map_sub, map_sub, hx]
    abel
  have herrid : T - C = (R-A).comp Jc.adjoint + T.comp
      (ContinuousLinearMap.id ℝ H - PV) := by
    calc
      T - C = (T - T.comp U.starProjection) - A.comp Jc.adjoint := by
        dsimp [C]
        ext x
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
        abel
        
      _ = (R.comp Jc.adjoint + T.comp (ContinuousLinearMap.id ℝ H - PV)) -
          A.comp Jc.adjoint := by
        rw [hRidentity]
        simp [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
      _ = (R-A).comp Jc.adjoint + T.comp (ContinuousLinearMap.id ℝ H - PV) := by
        ext x
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply]
        module
  have herr : ‖T-C‖ ≤ Real.sqrt (B/(k+1:ℝ)) + ε := by
    rw [herrid]
    calc
      ‖(R-A).comp Jc.adjoint + T.comp (ContinuousLinearMap.id ℝ H - PV)‖ ≤
          ‖(R-A).comp Jc.adjoint‖ + ‖T.comp (ContinuousLinearMap.id ℝ H - PV)‖ := norm_add_le _ _
      _ ≤ ‖R-A‖ * ‖Jc.adjoint‖ + ‖T.comp (ContinuousLinearMap.id ℝ H - PV)‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.sqrt (B/(k+1:ℝ)) + ε := by
          have hpart : ‖R-A‖ ≤ Real.sqrt (B/(k+1:ℝ)) := by
            calc
              ‖R-A‖ ≤ Real.sqrt ((∑ i : Fin (Module.finrank ℝ V),
                ‖R ((gram_isPositive R).isSymmetric.eigenvectorBasis rfl i)‖^2)/(k+1:ℝ)) := hAerr
              _ ≤ Real.sqrt (B/(k+1:ℝ)) := by
                apply Real.sqrt_le_sqrt
                exact div_le_div_of_nonneg_right htraceR (by positivity)
          have htail' : ‖T.comp (ContinuousLinearMap.id ℝ H - PV)‖ ≤ ε := by
            rw [hPV]
            simpa [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id] using htail
          calc
            ‖R-A‖ * ‖Jc.adjoint‖ + ‖T.comp (ContinuousLinearMap.id ℝ H - PV)‖ ≤
                ‖R-A‖ * 1 + ε := by
              gcongr
            _ = ‖R-A‖ + ε := by ring
            _ ≤ Real.sqrt (B/(k+1:ℝ)) + ε := by linarith
  refine ⟨C, hCrank, ?_⟩
  simpa [add_comm] using herr

end BrownianSharp.AlignmentHilbertTraceRefinement
