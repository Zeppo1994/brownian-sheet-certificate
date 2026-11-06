# Paper-to-Lean map

Reference: D. Bilyk, S. Neumayer, T. Ullrich, *The small ball problem for the
Brownian sheet: sharp bounds via entropy numbers in $`L_\infty`$*, manuscript of
6 November 2026 (22 pages, SHA-256
`27f92ce8adf167d8d32509cc40b04a317b58bdebcb39ebe2e88231e255b3851f`).
Theorem, lemma and equation numbers refer to this version. Full Lean names
begin with `BrownianSharp.`.

The public theorem is
[`AlignmentMainBodyCertified.mainBodyResults_certified`](BrownianSharp/AlignmentMainBodyCertified.lean).
Its statement `MainBodyResultsStatement` is a conjunction with one or more
fields per result, listed below in the order of the paper.

## Conventions

- **Entropy numbers.** $`e_k`$ uses $`2^{k-1}`$ closed balls with centers in the
  ambient space, as in (3.2) (`HaarQuarter.TheoremD.entropyNumber`; this name is outside `BrownianSharp`).
- **Kolmogorov numbers.** $`d_k`$ uses subspaces of dimension $`\lt k`$, as in
  (3.1)–(3.2) (`AlignmentOperatorNumbers.operatorKolmogorovNumber`).
- **Rates.** $`k^{-r}(\log k)^{\beta}`$ is `logarithmicIndexRate r β k`. The paper's
  $`\log(k+1)`$ in Lemma 3.1 agrees with $`\log k`$ up to constants for $`k\ge2`$.
  Small-deviation rates are `Latest.smallBallRate`.
- **Asymptotics.** Every $`\asymp`$ is stated with explicit constants $`c,C\gt 0`$
  and an index $`k_0`$, or a radius $`\varepsilon_0\lt e^{-1}`$, chosen before $`k`$
  or $`\varepsilon`$. For Gaussian fields the constants are chosen before the
  probability space and the realization, and the probability space may lie in
  any universe.
- **Classes.**
  - Anchored classes: the literal images of the $`L_p`$ unit ball under (1.4) in
    $`C([0,1]^d)`$.
  - Periodic classes: Littlewood–Paley classes (3.14)–(3.15) for every
    admissible cutoff $`\varphi_0`$. They are stated both for continuous functions
    and for the full $`L_1`$ classes, and they consist of real-valued functions.
  - Torus: it carries its probability Haar measure, with
    $`\widehat f(k)=\int f e^{-2\pi i\langle k,x\rangle}`$.
- **Matérn covariance.** In Corollary 5.3,
  $`k_i(\tau)=c_i\int\cos(2\pi\xi\tau)(\kappa_i^2+\xi^2)^{-h-1/2}\,d\xi`$.
  "Proportional to" in the paper is the constant $`c_i\gt 0`$. Another Fourier
  convention only rescales $`\kappa_i`$ and $`c_i`$, which are arbitrary.

## Main results

| Paper | Lean statement | Scope |
|---|---|---|
| Theorem 1.1 | `AlignmentPaperSheetUniverse.BrownianTwoSidedStatementU` | (1.3) for every $`d\ge2`$ and every continuous realization of the Brownian sheet. |
| Theorem 1.2 | `AlignmentMainBodyCertified.AnchoredLpTheoremStatement` | (1.6) for $`e_k(T_{d,p})`$, every $`1\lt p\lt\infty`$; $`d_k(T_{d,p})`$ for $`2\le p\lt\infty`$; compactness of $`T_{d,p}(B_{L_p})`$. Closedness by reflexivity of $`L_p`$ (uniform convexity and Milman–Pettis, from the ported TauCeti sources). |
| Theorem 1.3, lower bounds | `AlignmentPeriodicCutoffCertified.ArbitraryCutoffMainResultsStatement` | $`e_k`$ lower bounds for $`\mathbf W_p^r`$ ($`1\lt p\lt\infty`$), $`\mathbf B_{p,\theta}^r`$ and $`\mathbf H_p^r`$ ($`1\lt p\le\infty`$, $`1\le\theta\le\infty`$), $`r\gt 1/p`$. Also contains the Sobolev and Nikol'skii Kolmogorov numbers. Continuous and full $`L_1`$ classes. |
| Theorem 1.3 (i), (ii) | `AlignmentMainBodyCertified.PeriodicEndpointEntropyStatement`, `PeriodicBesovUpperRangeStatement`, `FullL1PeriodicBesovUpperRangeStatement`, `AlignmentPaperFullL1PeriodicEntropy.FullL1PeriodicEndpointEntropyStatement` | (1.7) and (1.8): two-sided $`e_k`$ and $`d_k`$ for $`r\gt 1/2`$, $`p\ge2`$, $`\theta\ge2`$ (Sobolev $`p\lt\infty`$, Nikol'skii $`\theta=\infty`$). |
| Theorem 2.1 | `AlignmentPaperGenericBumpCertified.AdmissibleBumpIidConfinementStatement` | (2.5) for every nonzero continuous bump supported in $`(0,1)`$ with $`\lvert\psi\rvert\le1`$, hence for every bump of the paper. Coefficients are iid $`N(0,1)`$ on any probability space. |
| Remark 2.2 | `AlignmentMainBodyCertified.ExceptionalSetStatement` | (2.7): inequality (2.6) fails only on an event of probability at most $`e^{-c''\lvert\mathcal D_n\rvert}`$. |
| Remark 2.7 | `AlignmentMainBodyCertified.ConvexTailSharpnessStatement` | $`\mathbb E e^{f_s}=1`$, $`\operatorname{Var}e^{f_s}=e^{s^2}-1`$, and both equivalences (2.35). |
| Remark 2.9 | `AlignmentMainBodyCertified.OneDimensionalFailureStatement` | (2.40), including $`(1-e^{-a^2n/2})^{2^n}=e^{-o(\lvert\mathcal D_n\rvert)}`$, and the failure of Theorem 2.1 for $`d=1`$. |
| Lemma 3.1 | `AlignmentMainBodyCertified.CarlLemmaStatement` | Every $`\alpha\gt 0`$ and $`\beta\in\mathbb R`$, for any bounded set $`K`$ in a Banach space (the image ball $`T(B_X)`$). Hypotheses and conclusion use the widths `kolmogorovWidth K n` over subspaces of dimension $`\le n`$; for these rates the shift to $`\lt k`$ only changes constants. |
| Remark 3.3 | `AlignmentMainBodyCertified.MeanZeroBesovEntropyStatement` | The Besov ball intersected with the coordinatewise mean-zero functions, for every cutoff, $`r\gt 1/2`$, $`p\ge2`$, $`2\le\theta\lt\infty`$. |
| Theorem 5.1 | `AlignmentPaperFractional.PaperFractionalTensorStatement` | (5.4) for every $`r\gt 1/2`$. |
| Theorem 5.2 | `AlignmentPaperSheetUniverse.FractionalSheetStatementU`, `IntegratedSheetStatementU` | (5.11) for $`\mathbf H\in(0,1)^d`$ with $`\nu\ge2`$; (5.12) for every $`m\in\mathbb N_0`$. |
| Corollary 5.3 | `AlignmentPaperMaternNumbersCertified.MaternCMNumbersStatement`, `AlignmentPaperMaternSmallBallUpper.MaternRawSmallBallStatement` | (5.13) and (5.14), with spectral densities $`c_i(\kappa_i^2+\xi^2)^{-h-1/2}`$. |
| Corollary 5.4 | `AlignmentPaperQuantizationSheetFinal.PaperQuantizationResultsStatement` | (5.18) for $`q_{m,1}`$, $`q_{m,2}`$ and $`\mathbb E W_2(\mu,\mu_m)`$, for all three sheet laws. |
| Section 5.3, last sentence | `AlignmentMainBodyCertified.PaperDeterministicIntegrationStatement`, `AlignmentPaperDeterministicIntegrationRates.DeterministicIntegrationRatesStatement` | With at most $`m`$ adaptive exact evaluations, the minimax error equals $`q_{m,1}`$ and hence has the rates (5.18). |

### Lemmas of Section 2 and Lemma 3.2

These are separate theorems, checked by the audit, on the proof route of Theorem 2.1:

| Paper | Lean |
|---|---|
| Lemma 2.3 | `AlignmentPaperSection2Lemmas.lemma_2_3`: (2.13) summed over depth profiles; $`\rho=0`$ for hulls of volume $`\gt 2^{-n}`$; (2.14) for every pair of good points. |
| Lemma 2.4 | `AlignmentPaperSection2Lemmas.lemma_2_4`: $`\mathbb E U_\tau=1`$, convexity of $`\log U_\tau`$, all moments, and (2.18) with $`\kappa,C`$ depending only on $`d,\psi`$. |
| Lemma 2.5 | `finiteProductGaussianEhrhard_certified`: (2.29) for all convex sets and $`0\lt\lambda\lt 1`$. |
| Proposition 2.6 | `AlignmentPaperSection2Lemmas.proposition_2_6`: both inequalities of (2.30), $`q=\Phi^{-1}(3/4)`$. It assumes $`e^{f(G)}\in L_2`$ explicitly, since Lean's `variance` is $`0`$ outside $`L_2`$. |
| Lemma 3.2 | `AlignmentPaperGenericSmoothBumpBesov.generic_exists_scaled_box_synthesis_Besov_spatial`: (3.16) in the form used for (3.19), for coefficients bounded by a fixed $`M`$, every $`r\gt 0`$, $`1\le p\le\infty`$, $`1\le\theta\le\infty`$. It is stated for the reference cutoff and transferred to the others. |

## Lower bounds: proof routes

All lower bounds follow the paper. The only probabilistic input is
Theorem 2.1, as proved in Section 2.

| Step | Paper | Lean |
|---|---|---|
| Good region, soft maximum, variance, convex tail | (2.8)–(2.38) | `AlignmentPaperContinuumGenericBump`, `AlignmentPaperSpatialExponential`, `AlignmentPaperGenericContinuumVariance`, `AlignmentPaperConvexTail`, `AlignmentPaperGenericBumpCertified.eventually_bumpSynthesis_confinement` |
| Theorem 2.1 for the fixed smooth atom, all grades | Theorem 2.1 | `AlignmentPaperConfinementBridge.smoothAtom_confinement_all_grades` |
| Translated balls | (3.9) | `AlignmentPaperConfinementBridge.linearSynthesis_ball_mass_le`. This uses finite-dimensional Anderson with radius $`2\rho`$ instead of the independent copy; only constants change. |
| Covering argument | (3.10)–(3.11) | `AlignmentPaperConfinementBridge.scaled_externalCover_gt` |
| Theorem 1.2 | (3.12)–(3.13) | `AlignmentAnchoredLpEnergy`, `AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p` |
| Theorem 1.3 | (3.18)–(3.20) and the Sobolev embeddings | `PeriodicNativeEntropy`, `AlignmentPeriodicCutoffCertified.arbitraryCutoffMainResults_certified` |
| Theorem 5.1 | (5.5)–(5.8) | `AlignmentPaperFractionalFourierBridge`, `AlignmentPaperFractionalFourierPreimage`, `AlignmentPaperFractionalEntropyRoute` |
| Theorem 1.1 | Section 4 | `AlignmentPaperBrownianEntropyRoute.brownian_lowerLog_paperRoute`: Theorem 1.2 at $`p=2`$ on $`K_d`$, the Cameron–Martin shift, and the lower half of (4.1) (`AlignmentGaussianEntropySmallBall.uniform_smallBall_probability_upper_of_entropy_lower`) |
| Theorem 5.2 | Proof of Theorem 5.2 | Unit-ball inclusion and the lower half of (4.1). For unequal Hurst indices, restriction to the coordinates with $`H_i=H_*`$ (`AlignmentPaperFractionalSheetSameSpaceSlice`). Integrated sheets via $`R_m^{\otimes d}T_d=T_d^{(m+1)}`$. |
| Corollary 5.3 | (5.15) and (4.1) | (5.15) by restricting the periodic Sobolev ball to the cube after multiplication with a fixed positive window (`AlignmentMaternComplexWindow.matern_periodic_sobolev_source_embedding`); the small-deviation lower bound by the lower half of (4.1) |
| Corollary 5.4 | (5.19) | Independent-copy bound and the small-deviation lower bounds |

Section 4 enters through the Cameron–Martin shift inequality on
$`K_d=T_d(B_{L_2})`$, which is proved directly for the sheet law. The description
(1.5) of $`K_d`$ by weak derivatives is not needed.

`CertificateAudit.lean` checks that the proofs of Theorems 1.1, 1.2, 1.3, 5.1,
5.2 and Corollaries 5.3, 5.4 use `smoothAtom_confinement_all_grades`, and that
it uses the Section 2 proof.

## Upper bounds: proof routes

The paper imports the upper bounds from the literature. The certificate proves
them, partly along other routes:

- **Theorems 1.1 and 5.2.** Finite-dimensional Gaussian approximations of the
  sheets, grid probabilities and inversion of the scale, instead of [20],
  [29, Cor. 7.5] and the upper half of (4.1).
- **Theorem 1.2.**
  - For $`p\ge2`$: the width bound for $`K_d`$ and $`L_p\subset L_2`$.
  - For $`1\lt p\lt 2`$: a direct proof on the $`L_p`$ source, instead of Belinsky's estimate [5] (`AlignmentPaperAnchoredLpComplete`). It uses reflection, Fourier grades, product square functions and adaptive hyperbolic-cross covers.
- **Theorem 1.3.** Internal proofs of the Sobolev and Nikol'skii widths of [46], and an explicit high/low block decomposition in place of the interpolation (3.21).
- **Theorem 5.1.** An internal width bound instead of [29, Thm. 5.7] and [37].
- **Corollary 5.3.**
  - Entropy and Kolmogorov numbers (5.16): inclusion of the Cameron–Martin ball in a
    periodic Sobolev class of period 8, by weighted Fourier-kernel estimates, then Theorem 1.3.
  - Small-deviation upper bound: spectral approximation and grids.
- **Corollary 5.4.** Finite codebooks, Gaussian path enlargement and empirical coupling, instead of [11, Thm. 1.4].

## Not formalized

- **Remark 2.8:** Theorem 2.1 for arbitrary measurable atoms with
  $`\sum\|a_R\|_2^2\ge c_0S_n`$.
- **Remark 3.3, last part:** the $`e_k`$ order of Theorem 1.3(i) for
  $`1\lt p\lt 2`$, which relies on Belinsky's upper bound [5, Thm. 1.1].
- **Remark 3.4:** the approximation numbers of [15].
- **The upper half of the Kuelbs–Li–Linde correspondence (4.1) as a general
  theorem.** The upper bounds above are proved without it.
