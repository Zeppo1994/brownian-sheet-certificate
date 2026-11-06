import BrownianSharp
import Lean.Util.CollectAxioms

open Lean Elab Command
open scoped ENNReal

/-! Check exact public theorem types, then audit the transitive axioms of every project declaration. -/
example : BrownianSharp.AlignmentMainBodyCertified.MainBodyResultsStatement.{0} :=
  BrownianSharp.AlignmentMainBodyCertified.mainBodyResults_certified

example : BrownianSharp.AlignmentPeriodicCutoffCertified.ArbitraryCutoffMainResultsStatement :=
  BrownianSharp.AlignmentPeriodicCutoffCertified.arbitraryCutoffMainResults_certified

example : BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary.FullL1PeriodicEntropyStatement :=
  BrownianSharp.AlignmentPeriodicCutoffCertified.fullL1_periodic_entropy_certified

example : BrownianSharp.AlignmentPeriodicL1CutoffSobolevReconstruction.FullL1PeriodicWidthStatement :=
  BrownianSharp.AlignmentPeriodicCutoffCertified.fullL1_periodic_width_certified

-- Paper lemmas of Section 2 on the proof route of Theorem 2.1.
example := @BrownianSharp.AlignmentPaperSection2Lemmas.lemma_2_3 -- Lemma 2.3
example := @BrownianSharp.AlignmentPaperSection2Lemmas.lemma_2_4 -- Lemma 2.4
example := @BrownianSharp.finiteProductGaussianEhrhard_certified -- Lemma 2.5
example := @BrownianSharp.AlignmentPaperSection2Lemmas.proposition_2_6 -- Proposition 2.6
example := @BrownianSharp.AlignmentPaperGenericSmoothBumpBesov.generic_exists_scaled_box_synthesis_Besov_spatial -- Lemma 3.2

-- Theorem 1.2 on the literal bounded operator image, not only on the image-set name.
example (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)] :
    BrownianSharp.AlignmentPaperPeriodic.twoSidedEntropyRate
      (BrownianSharp.AlignmentPaperAnchoredLpOperator.anchoredIntegrationOperator
        (d := d) p hp '' Metric.closedBall 0 1) 1 ((d:ℝ)-1/2) := by
  rw [BrownianSharp.AlignmentPaperAnchoredLpOperator.anchoredIntegrationOperator_image_eq]
  exact (BrownianSharp.AlignmentMainBodyCertified.anchoredLpTheorem_certified d hd p hp).1

-- These guards check proof-body dependencies, not just theorem names or types.
-- They do not replace the manual mathematical comparison with the paper.
set_option maxHeartbeats 2000000 in
run_cmd do
  let env ← getEnv
  let anchors : Array (Name × Name) := #[
    (`BrownianSharp.AlignmentPeriodicCutoffCertified.arbitraryCutoffMainResults_certified,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalTensor_certified,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperMaternNumbersCertified.maternCMNumbers_certified,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperSheetUniverse.brownianTwoSided_certified,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperSheetUniverse.fractionalSheet_certified,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperSheetUniverse.integratedSheet_certified,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperMaternSmallBallUpper.maternRawSmallBall_certified,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperQuantizationSheetFinal.paperQuantizationResultsStatement,
      `BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades),
    (`BrownianSharp.AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades,
      `BrownianSharp.AlignmentPaperGenericBumpCertified.eventually_bumpSynthesis_confinement),
    (`BrownianSharp.AlignmentPaperGenericBumpCertified.eventually_bumpSynthesis_confinement,
      `BrownianSharp.AlignmentPaperConvexTail.finiteProductGaussian_convex_exp_lower_tail),
    (`BrownianSharp.AlignmentPaperMaternSmallBallUpper.maternRawSmallBall_certified,
      `BrownianSharp.AlignmentPaperMaternSpectralAggregation.scalarFeature_levelTaylor_residual_norm_le),
    (`BrownianSharp.AlignmentPaperMaternSmallBallUpper.maternRawSmallBall_certified,
      `BrownianSharp.AlignmentEndpointCubeGridLimit.cube_grid_mass_lower_to_uniform_mass_lower),
    (`BrownianSharp.AlignmentPaperMaternSmallBallUpper.maternRawSmallBall_certified,
      `BrownianSharp.AlignmentGaussianGradedReverseClosure.uniform_upperLog_of_dyadic_probability_lower),
    (`BrownianSharp.AlignmentPaperGenericSmoothBumpBesov.generic_exists_scaled_box_synthesis_Besov_spatial,
      `BrownianSharp.AlignmentPaperGenericSmoothBumpBesov.genericPeriodicBesov_of_boundedCoefficients),
    (`BrownianSharp.AlignmentPaperGenericSmoothBumpBesov.exists_meanZero_generic_smooth_bump_endpoint,
      `BrownianSharp.AlignmentPaperMeanZeroBump.exists_meanZero_smooth_admissibleBump),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalTensor_certified,
      `BrownianSharp.AlignmentPaperFractionalFourierBridge.fourier_dampedDerivativeConvolution_l2_norm_eq),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalTensor_certified,
      `BrownianSharp.AlignmentPaperFractionalDampingLimit.dampedRLIntegral_tendsto),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalTensor_certified,
      `BrownianSharp.AlignmentPaperFractionalEntropyRoute.scaled_class_mass_of_scalar),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalSheet_certified,
      `BrownianSharp.AlignmentPaperFractionalSheetSameSpaceSlice.exists_sameSpace_minimumMultiplicity_slice),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalSheet_certified,
      `BrownianSharp.AlignmentPaperFractionalSheetSameSpaceSlice.sameSpaceMinimumCoordinateSheet_smallBall_probability_ge),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalSheet_certified,
      `BrownianSharp.AlignmentPaperFractionalEntropyRoute.entropy_lower_of_scalar),
    (`BrownianSharp.AlignmentPaperFractional.paperIntegratedSheet_certified,
      `BrownianSharp.AlignmentPaperFractionalFourierPreimage.smoothAtom_dyadic_fractional_preimage_fourier),
    (`BrownianSharp.AlignmentPaperFractional.paperIntegratedSheet_certified,
      `BrownianSharp.AlignmentGaussianIntegratedSmallBall.integratedSheetLaw_ball_shift_lower),
    (`BrownianSharp.AlignmentPaperFractional.paperFractionalTensor_certified,
      `BrownianSharp.AlignmentPaperFractionalFourierMembership.causalRLProfile_fourier_memLp_two),
    (`BrownianSharp.AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p,
      `BrownianSharp.AlignmentAnchoredLpEnergy.firstMixedDerivative_layer_square_sum_le),
    (`BrownianSharp.AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p,
      `BrownianSharp.AlignmentAnchoredLpEnergy.firstMixedDerivative_cube_expected_rpow_le),
    (`BrownianSharp.AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p,
      `BrownianSharp.AlignmentAnchoredLpEnergy.firstMixedDerivativeDensityLp_image_eq_native),
    (`BrownianSharp.AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p,
      `BrownianSharp.AlignmentAnchoredLpEnergy.firstMixedDerivative_cube_Lp_sublevel_mass),
    (`BrownianSharp.AlignmentPaperSignedKernelLp.circleSignedConvolutionOperator_lintegral_lp_le,
      `BrownianSharp.External.WeakCZ.exists_circle_signed_convolution_weak_one),
    (`BrownianSharp.AlignmentPaperSignedKernelLp.circleSignedConvolutionOperator_lintegral_lp_le,
      `BrownianSharp.AlignmentPaperSignedKernelOperator.circleSignedConvolutionOperator_lintegral_sq_le),
    (`BrownianSharp.AlignmentPaperSignedKernelLp.circleSmoothSquareFunction_vector_lintegral_lp_le,
      `BrownianSharp.AlignmentPaperHilbertRademacherLower.hilbertRow_lower_moment),
    (`BrownianSharp.AlignmentPaperJointStageEntropy.jointFeature_entropy_le_of_stage_counts,
      `BrownianSharp.AlignmentPaperJointStageChain.actual_chain_increment_mem),
    (`BrownianSharp.AlignmentPaperJointStageEntropy.jointFeature_entropy_le_of_stage_counts,
      `BrownianSharp.AlignmentPaperJointStagePieces.exists_stage_increment_piece),
    (`BrownianSharp.AlignmentPaperFractional.paperIntegratedSheet_certified,
      `BrownianSharp.AlignmentPaperIntegratedSemigroup.integrateSheetPath_eq_integrateSheetSemigroupPath),
    (`BrownianSharp.AlignmentPaperJointDyadicSums.jointFeature_dyadic_entropy_budgeted,
      `BrownianSharp.AlignmentPaperJointStageRates.exists_joint_stage_data),
    (`BrownianSharp.AlignmentPaperJointDyadicSums.jointFeature_dyadic_entropy_budgeted,
      `BrownianSharp.AlignmentPaperAdaptiveDyadicCardinality.pairCoverCount_le_binary_cost),
    (`BrownianSharp.AlignmentPaperAnchoredLpParityFourierCube.anchoredFaceSource_fourierCoeff_eq_derivativePath,
      `BrownianSharp.AlignmentPaperAnchoredLpParityFourier.anchoredFaceSource_fourierCoeff_average),
    (`BrownianSharp.AlignmentPaperAnchoredLpParityFourierCube.anchoredFaceSource_fourierCoeff_eq_derivativePath,
      `BrownianSharp.AlignmentPaperAnchoredLpSourceFourier.measurePreserving_foldCoordinates),
    (`BrownianSharp.AlignmentPaperJointSamplingBudget.encodeSmoothGradeSamples_fin_square_budget,
      `BrownianSharp.AlignmentPaperLpDvpSampling.torusFourierPolynomial_shifted_grid_lp_bound),
    (`BrownianSharp.AlignmentPaperJointSamplingBudget.encodeSmoothGradeSamples_fin_square_budget,
      `BrownianSharp.AlignmentPaperFiniteShapeEnergy.sum_energy_le_card_square_budget),
    (`BrownianSharp.AlignmentPaperAnchoredLpCompact.anchoredIntegrationOperator_isCompact,
      `BrownianSharp.AlignmentPaperAnchoredLpCompact.anchoredIntegrationLpImage_equicontinuous),
    (`BrownianSharp.AlignmentPaperProductSquareFunctionLp.productSmoothSquareFunction_lintegral_lp_le,
      `BrownianSharp.AlignmentPaperSignedKernelLp.circleSignedConvolutionOperator_weak_one),
    (`BrownianSharp.AlignmentPaperProductSquareFunctionLp.productSmoothSquareFunction_lintegral_lp_le,
      `BrownianSharp.AlignmentPaperProductSquareFunctionLp.iteratedProductBlock_eq_productSmoothBlockConvolution),
    (`BrownianSharp.AlignmentPaperAnchoredLpGradeReconstruction.smoothGradePolynomial_hasSum,
      `BrownianSharp.AlignmentPaperAnchoredLpGradeReconstruction.gradeMultiplier_hasSum),
    (`BrownianSharp.AlignmentPaperAnchoredLpCubeRestriction.anchoredImage_entropy_le_of_fold_membership,
      `BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension.periodicFoldExtension_halfCube),
    (`BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity.productSmoothSquareFunction_lintegral_lp_le_of_memLp,
      `BrownianSharp.AlignmentPaperFiniteKernelLpDensity.finiteKernel_moment_le_of_continuous),
    (`BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity.productSmoothSquareFunction_lintegral_lp_le_of_memLp,
      `BrownianSharp.AlignmentPaperProductSquareFunctionLp.productSmoothSquareFunction_lintegral_lp_le),
    (`BrownianSharp.AlignmentPaperMultivariateFaceInverse.faceInverse_reconstructs_actual_faceBlock,
      `BrownianSharp.AlignmentPaperInverseDerivativeNeighborIdentity.inverseNeighbor_multiplier_reconstructs_block),
    (`BrownianSharp.AlignmentPaperJointGradeRefinement.exists_decodedGrade_refined_cover,
      `BrownianSharp.AlignmentPaperJointGradeRefinement.decodedGradeRange_finrank_le),
    (`BrownianSharp.AlignmentPaperJointGradeScaleEnvelope.exists_lowGrade_cover_envelope,
      `BrownianSharp.AlignmentPaperJointGradeScaleEnvelope.exists_stageScale_fullRank_envelope),
    (`BrownianSharp.AlignmentPaperJointGradeScaleEnvelope.exists_stageScale_fullRank_envelope,
      `BrownianSharp.AlignmentPaperJointAdaptiveScalarSums.jointSampleDimension_lower_envelope),
    (`BrownianSharp.AlignmentPaperFaceGradeYoung.exists_faceGradeYoung_Lp_bound,
      `BrownianSharp.AlignmentPaperMultivariateFaceInverse.faceInverse_reconstructs_actual_faceBlock),
    (`BrownianSharp.AlignmentPaperFaceGradeYoung.exists_faceGradeYoung_Lp_bound,
      `BrownianSharp.unitAddTorus_complex_convolution_rpow_le),
    (`BrownianSharp.AlignmentPaperAnchoredLpSeriesMembership.integrationPath_mem_GradeSeriesClass_of_grade_cost,
      `BrownianSharp.AlignmentPaperJointSamplingBudget.encodeSmoothGradeSamples_fin_square_budget),
    (`BrownianSharp.AlignmentPaperAnchoredLpSeriesMembership.integrationPath_mem_GradeSeriesClass_of_grade_cost,
      `BrownianSharp.AlignmentPaperAnchoredLpGradeReconstruction.smoothGradePolynomial_hasSum),
    (`BrownianSharp.AlignmentPaperJointGlobalWindow.gradeSeriesClass_entropy_le_of_window_covers,
      `BrownianSharp.AlignmentPaperJointGlobalTail.gradeSeriesClass_window_decomposition),
    (`BrownianSharp.AlignmentMainBodyCertified.meanZeroBesovEntropy_certified,
      `BrownianSharp.AlignmentPaperGenericSmoothBumpBesov.exists_meanZero_generic_smooth_bump_endpoint),
    (`BrownianSharp.AlignmentMainBodyCertified.meanZeroBesovEntropy_certified,
      `BrownianSharp.AlignmentPaperGenericBumpCertified.eventually_bumpSynthesis_confinement),
    (`BrownianSharp.AlignmentPaperProductGradeSquareFunctionLp.productSmoothGrade_mixedLp_le_of_memLp,
      `BrownianSharp.AlignmentPaperFiniteMixedSquareLp.finite_mixed_square_le_integral),
    (`BrownianSharp.AlignmentPaperProductGradeSquareFunctionLp.productSmoothGrade_mixedLp_le_of_memLp,
      `BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity.productSmoothSquareFunction_lintegral_lp_le_of_memLp),
    (`BrownianSharp.AlignmentPaperJointLowGradeRefinedFamily.exists_lowGrade_refined_cover_family,
      `BrownianSharp.AlignmentPaperJointRefinementBinaryBudget.exists_joint_refinement_binary_budget),
    (`BrownianSharp.AlignmentPaperJointLowGradeRefinedFamily.exists_lowGrade_refined_cover_family,
      `BrownianSharp.AlignmentPaperJointGradeRefinement.exists_decodedGrade_refined_cover),
    (`BrownianSharp.AlignmentPaperAnchoredLpSeriesClass.exists_uniform_anchoredGradeSeries_membership,
      `BrownianSharp.AlignmentPaperAnchoredLpActualGradeBudget.exists_actualGradeLpCost_bound),
    (`BrownianSharp.AlignmentPaperAnchoredLpActualGradeBudget.exists_actualGradeLpCost_bound,
      `BrownianSharp.AlignmentPaperProductGradeSquareFunctionLp.productSmoothGrade_mixedLp_le_of_memLp),
    (`BrownianSharp.AlignmentPaperAnchoredLpActualGradeBudget.exists_actualGradeLpCost_bound,
      `BrownianSharp.AlignmentPaperFaceGradeYoung.exists_faceGradeYoung_Lp_bound),
    (`BrownianSharp.AlignmentPaperAnchoredLpSeriesClass.exists_anchoredGradeSeries_entropy_domination,
      `BrownianSharp.AlignmentPaperAnchoredLpCubeRestriction.anchoredImage_entropy_le_of_fold_membership),
    (`BrownianSharp.AlignmentMainBodyCertified.anchoredLpTheorem_certified,
      `BrownianSharp.AlignmentPaperAnchoredLpComplete.anchoredIntegrationLp_entropy_upper_lt_two),
    (`BrownianSharp.AlignmentPaperAnchoredLpComplete.anchoredIntegrationLp_entropy_upper_lt_two,
      `BrownianSharp.AlignmentPaperAnchoredLpSeriesClass.exists_anchoredGradeSeries_entropy_domination),
    (`BrownianSharp.AlignmentPaperAnchoredLpComplete.anchoredIntegrationLp_entropy_upper_lt_two,
      `BrownianSharp.AlignmentPaperJointGlobalEntropy.gradeSeriesClass_entropy_upper),
    (`BrownianSharp.AlignmentPaperJointGlobalEntropy.gradeSeriesClass_entropy_upper,
      `BrownianSharp.AlignmentPaperJointGlobalWindowSplit.gradeSeriesClass_entropy_le_of_split_window),
    (`BrownianSharp.AlignmentPaperJointGlobalEntropy.gradeSeriesClass_entropy_upper,
      `BrownianSharp.AlignmentPaperJointLowGradeRefinedFamily.exists_lowGrade_refined_cover_family),
    (`BrownianSharp.AlignmentPaperJointGlobalEntropy.gradeSeriesClass_entropy_upper,
      `BrownianSharp.AlignmentPaperJointHighGradeCovers.exists_highGrade_cover_family),
    (`BrownianSharp.AlignmentPaperJointGlobalEntropy.gradeSeriesClass_entropy_upper,
      `BrownianSharp.AlignmentPaperJointGlobalTailRadius.exists_windowTail_radius_envelope),
    (`BrownianSharp.AlignmentPaperJointGlobalEntropy.gradeSeriesClass_entropy_upper,
      `BrownianSharp.AlignmentPaperJointGradeEntropyInversion.eventually_entropy_powerlog_of_joint_stage_bounds),
    (`BrownianSharp.AlignmentPaperBrownianEntropyRoute.brownianTwoSided_paperRoute,
      `BrownianSharp.AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p),
    (`BrownianSharp.AlignmentPaperBrownianEntropyRoute.brownianTwoSided_paperRoute,
      `BrownianSharp.AlignmentGaussianIntegratedSmallBall.integratedSheetLaw_ball_shift_lower),
    (`BrownianSharp.AlignmentPaperBrownianEntropyRoute.brownianTwoSided_paperRoute,
      `BrownianSharp.AlignmentGaussianEntropySmallBall.uniform_smallBall_probability_upper_of_entropy_lower),
    (`BrownianSharp.AlignmentPaperDeterministicExceptionalSet.deterministic_exceptional_set_small,
      `BrownianSharp.AlignmentPaperGenericBumpCertified.admissibleBumpIidConfinement_certified),
    (`BrownianSharp.AlignmentPaperAnchoredLpClosed.anchoredIntegrationLpImage_isCompact,
      `BrownianSharp.AlignmentPaperAnchoredLpClosed.anchoredIntegrationLpImage_isClosed),
    (`BrownianSharp.AlignmentPaperAnchoredLpClosed.anchoredIntegrationLpImage_isClosed,
      `MeasureTheory.Lp.surjective_inclusionInDoubleDual)]
  -- Traverse each provider once even when several required steps share it.
  let roots := anchors.foldl (fun acc pair =>
    if acc.contains pair.1 then acc else acc.push pair.1) (#[] : Array Name)
  for root in roots do
    let targets := anchors.filterMap fun pair =>
      if pair.1 == root then some pair.2 else none
    for target in targets do
      unless (env.find? root).isSome && (env.find? target).isSome do
        throwError "Missing proof-route declaration: {root} / {target}"
    let mut pending : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut remaining := targets
    while !pending.isEmpty && !remaining.isEmpty do
      let current := pending.back!
      pending := pending.pop
      remaining := remaining.filter (· != current)
      if !seen.contains current then
        seen := seen.insert current
        let inspect := match env.getModuleIdxFor? current with
          | none => true
          | some idx => match env.allImportedModuleNames[idx.toNat]? with
            | some moduleName => Name.isPrefixOf `BrownianSharp moduleName
            | none => false
        if inspect then
          let body? := match env.find? current with
            | some (.defnInfo v) => some v.value
            | some (.thmInfo v) => some v.value
            | some (.opaqueInfo v) => some v.value
            | _ => none
          if let some body := body? then
            for dependency in body.getUsedConstants do
              if !seen.contains dependency then
                pending := pending.push dependency
    for target in remaining do
      throwError "Proof-route dependency missing: {root} must use {target}"
  logInfo m!"PASS: {anchors.size} proof-route dependency anchors checked."

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let auditThis ← match env.getModuleIdxFor? name with
      | none => pure true
      | some idx => do
        let some moduleName := env.allImportedModuleNames[idx.toNat]? |
          throwError "Invalid defining-module index for {name}"
        pure (Name.isPrefixOf `BrownianSharp moduleName ||
          Name.isPrefixOf `Isoperimetric moduleName ||
          Name.isPrefixOf `TauCeti moduleName)
    if auditThis then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  unless checked > 0 do
    throwError "No component declarations were audited"
  logInfo m!"PASS: {checked} component declarations use only foundational axioms. Exact public statement types checked above."
