import BrownianSharp.AlignmentPeriodicCutoffYoung
import BrownianSharp.AlignmentPeriodicCutoffAssembly
import BrownianSharp.AlignmentPeriodicL1CutoffSobolevReconstruction

/-! Unconditional arbitrary-cutoff periodic conclusions. Every analytic
transfer input and full-L¹ reconstruction is discharged; none remains as a
caller premise. -/
namespace BrownianSharp.AlignmentPeriodicCutoffCertified

theorem periodicMain_certified :
    AlignmentPeriodicCutoffAssembly.PeriodicMainStatement :=
  AlignmentPeriodicCutoffAssembly.periodicMain_of_transfer
    AlignmentPeriodicCutoffYoung.cutoffBesovScaleTransfer_certified

def ArbitraryCutoffMainResultsStatement : Prop :=
  AlignmentPeriodicCutoffAssembly.PeriodicMainStatement ∧
  AlignmentPeriodicL1CutoffSobolevReconstruction.FullL1PeriodicWidthStatement

theorem arbitraryCutoffMainResults_certified : ArbitraryCutoffMainResultsStatement :=
  ⟨periodicMain_certified,
    AlignmentPeriodicL1CutoffSobolevReconstruction.fullL1_periodic_width_of_cutoff_statement
      periodicMain_certified.2.1⟩

theorem periodic_mixed_entropy_certified :
    AlignmentPeriodicCutoffTransferStatement.PeriodicMixedEntropyStatement :=
  periodicMain_certified.1

theorem periodic_width_certified :
    AlignmentPeriodicCutoffTransferStatement.PeriodicWidthStatement :=
  periodicMain_certified.2.1

theorem fullL1_periodic_entropy_certified :
    AlignmentPeriodicL1AdmissibleEntropyBoundary.FullL1PeriodicEntropyStatement :=
  periodicMain_certified.2.2

theorem fullL1_periodic_width_certified :
    AlignmentPeriodicL1CutoffSobolevReconstruction.FullL1PeriodicWidthStatement :=
  arbitraryCutoffMainResults_certified.2

end BrownianSharp.AlignmentPeriodicCutoffCertified
