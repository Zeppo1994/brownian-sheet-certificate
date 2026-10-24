import BrownianSharp
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Check exact public theorem types, then audit the transitive axioms of every project declaration. -/
example : BrownianSharp.AlignmentMainBodyCertified.MainBodyResultsStatement :=
  BrownianSharp.AlignmentMainBodyCertified.mainBodyResults_certified

example : BrownianSharp.AlignmentPeriodicCutoffCertified.ArbitraryCutoffMainResultsStatement :=
  BrownianSharp.AlignmentPeriodicCutoffCertified.arbitraryCutoffMainResults_certified

example : BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary.FullL1PeriodicEntropyStatement :=
  BrownianSharp.AlignmentPeriodicCutoffCertified.fullL1_periodic_entropy_certified

example : BrownianSharp.AlignmentPeriodicL1CutoffSobolevReconstruction.FullL1PeriodicWidthStatement :=
  BrownianSharp.AlignmentPeriodicCutoffCertified.fullL1_periodic_width_certified

example : BrownianSharp.AlignmentFractionalApproximationCertified.FullFractionalApproximationStatement :=
  BrownianSharp.AlignmentFractionalApproximationCertified.fractionalApproximation_certified

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
          Name.isPrefixOf `Isoperimetric moduleName)
    if auditThis then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  unless checked > 0 do
    throwError "No component declarations were audited"
  logInfo m!"PASS: {checked} component declarations use only foundational axioms. Exact public statement types checked above."
