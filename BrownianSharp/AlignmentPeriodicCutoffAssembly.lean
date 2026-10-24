import BrownianSharp.AlignmentPeriodicCutoffMixedEntropy
import BrownianSharp.AlignmentPeriodicCutoffSobolevWidth
import BrownianSharp.AlignmentPeriodicCutoffNikolskyWidth
import BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary

/-! Assemble actual periodic main conclusions from the single explicit
cutoff Besov transfer statement. A final certified caller must discharge
that transfer statement with the actual kernel/overlap proof. -/
namespace BrownianSharp.AlignmentPeriodicCutoffAssembly

open BrownianSharp.AlignmentPeriodicCutoffTransferStatement

theorem periodic_width_of_transfer (htransfer : BesovScaleTransferStatement) :
    AlignmentPeriodicCutoffTransferStatement.PeriodicWidthStatement := by
  have hEntropy := AlignmentPeriodicCutoffMixedEntropy.periodic_mixed_entropy_of_transfer htransfer
  intro φ d hd p hp r hr
  constructor
  · intro hptop
    exact AlignmentPeriodicCutoffSobolevWidth.periodic_cutoff_sobolev_width_of_transfer_and_entropy
      htransfer hEntropy hd hp hptop hr
  · exact AlignmentPeriodicCutoffNikolskyWidth.nikolsky_twoSided_width_of_cutoff_transfer_and_entropy
      htransfer hEntropy φ hd p hp r hr

def PeriodicMainStatement : Prop :=
  AlignmentPeriodicCutoffTransferStatement.PeriodicMixedEntropyStatement ∧
  AlignmentPeriodicCutoffTransferStatement.PeriodicWidthStatement ∧
  AlignmentPeriodicL1AdmissibleEntropyBoundary.FullL1PeriodicEntropyStatement

theorem periodicMain_of_transfer (htransfer : BesovScaleTransferStatement) :
    PeriodicMainStatement := by
  have hEntropy := AlignmentPeriodicCutoffMixedEntropy.periodic_mixed_entropy_of_transfer htransfer
  exact ⟨hEntropy, periodic_width_of_transfer htransfer,
    AlignmentPeriodicL1AdmissibleEntropyBoundary.fullL1_periodic_entropy_of_cutoff_statement hEntropy⟩

end BrownianSharp.AlignmentPeriodicCutoffAssembly
