import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.CameronMartinNativeConfinement

/-! Unconditional consequences of the checked Gaussian heat proof. These
certify the first manuscript result and the entropy lower half of the second;
the full second and third results retain their separate completion gate. -/
namespace BrownianSharp

theorem sharpLog_certified : SharpLogStatement :=
  sharpLog_of_productGaussianEhrhard productGaussianEhrhard_certified

theorem sharpProbability_certified : SharpProbabilityStatement :=
  sharpProbability_of_productGaussianEhrhard productGaussianEhrhard_certified

theorem cameronMartinEntropyLower_certified {d : ℕ} (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) :=
  cameronMartinEntropyLower_of_productGaussianEhrhard productGaussianEhrhard_certified hd

end BrownianSharp
