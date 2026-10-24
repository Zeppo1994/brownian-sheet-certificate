import BrownianSharp.AlignmentPeriodicCutoffCertified
import BrownianSharp.AlignmentOperatorCameronMartin
import BrownianSharp.AlignmentOperatorFractional
import BrownianSharp.AlignmentFractionalApproximationCertified
import BrownianSharp.AlignmentGaussianBrownianReverse
import BrownianSharp.AlignmentFractionalSheetStatement
import BrownianSharp.AlignmentGaussianIntegratedReverse

/-! One main-body statement. The arbitrary-cutoff periodic clause already
includes the full-L1 entropy and width conclusions; concrete-cutoff
specializations and older headline bundles are not repeated. -/
namespace BrownianSharp.AlignmentMainBodyCertified

def MainBodyResultsStatement : Prop :=
  AlignmentOperatorStatements.CameronMartinEntropyWidthStatement ∧
  AlignmentPeriodicCutoffCertified.ArbitraryCutoffMainResultsStatement ∧
  AlignmentOperatorStatements.FractionalEntropyWidthStatement ∧
  AlignmentFractionalApproximationCertified.FullFractionalApproximationStatement ∧
  Latest.BrownianTwoSidedStatement ∧
  Latest.FractionalSheetStatement ∧
  Latest.IntegratedSheetStatement

theorem mainBodyResults_certified : MainBodyResultsStatement :=
  ⟨AlignmentOperatorCameronMartin.cameronMartinEntropyWidth_certified,
    AlignmentPeriodicCutoffCertified.arbitraryCutoffMainResults_certified,
    AlignmentOperatorFractional.fractionalEntropyWidth_certified,
    AlignmentFractionalApproximationCertified.fractionalApproximation_certified,
    AlignmentGaussianBrownianReverse.latest_brownian_twoSided_certified,
    AlignmentFractionalSheetStatement.latest_fractionalSheet_certified,
    AlignmentGaussianIntegratedReverse.latest_integratedSheet_certified⟩

end BrownianSharp.AlignmentMainBodyCertified
