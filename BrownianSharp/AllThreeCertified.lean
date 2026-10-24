import BrownianSharp.UniformSharpCertified
import BrownianSharp.NativeCameronMartinCoverRate
import BrownianSharp.PeriodicMixedFinal

/-! The three manuscript results, with no external analytic hypotheses.
The first conjunct uses dimension-uniform constants, the second is the
actual restricted-cube integration ball, and the third uses the literal
smooth Fourier resolution including the infinite-theta endpoint. -/
namespace BrownianSharp

theorem allThreeResults_certified : AllThreeResultsStatement :=
  ⟨uniformSharpLog_certified, cameronMartinEntropyWidth_certified,
    periodicMixedEntropy_certified⟩

end BrownianSharp
