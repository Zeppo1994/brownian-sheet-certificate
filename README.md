# Entropy, Kolmogorov widths, and Brownian-sheet small deviations

Lean certificate for D. Bilyk, S. Neumayer and T. Ullrich,
*The small ball problem for the Brownian sheet: sharp bounds via entropy
numbers in $`L_\infty`$* (6 November 2026). Results are numbered as in the paper.

Throughout, $`d\ge2`$, $`\mathbb N=\{1,2,\ldots\}`$, and
$`\mathbb N_0=\{0,1,2,\ldots\}`$.
The spaces $`L_p`$ on the cube $`[0,1]^d`$ use the Lebesgue measure, and
$`C([0,1]^d)`$ carries the supremum norm
$`\|f\|_\infty=\sup_{\mathbf t\in[0,1]^d}|f(\mathbf t)|`$.
All logarithms are natural. We write $`u_k\lesssim v_k`$ if $`u_k\le C v_k`$ for a fixed $`C\gt 0`$, and $`u_k\asymp v_k`$ when both
$`u_k\lesssim v_k`$ and $`v_k\lesssim u_k`$ hold with positive constants for all
sufficiently large $`k`$; the analogous convention applies as a radius tends
to zero. Constants may depend on the fixed dimension and the displayed
smoothness and integrability parameters, but not on $`k`$ or the radius.

## 1. Brownian-sheet small deviations (Theorem 1.1)

Let $`(\Omega,\mathcal F,\mathbb P)`$ be a probability space. All Gaussian
fields below have continuous paths and are measurable as maps from
$`\Omega`$ into $`C([0,1]^d)`$. Every finite collection of evaluations is
jointly Gaussian with mean zero.

The Brownian sheet $`B`$ is the centered Gaussian field with covariance

```math
\mathbb E[B(\mathbf s)B(\mathbf t)]
=\prod_{i=1}^d\min(s_i,t_i).
```

Then, it holds

```math
-\log\mathbb P\{\|B\|_\infty\le\varepsilon\}
\asymp\varepsilon^{-2}
 \bigl(\log(1/\varepsilon)\bigr)^{2d-1},
\qquad \varepsilon\downarrow0.
```

There are positive constants $`c_d,C_d,\varepsilon_d`$, with
$`\varepsilon_d\lt e^{-1}`$, giving both inequalities for every
$`0\lt \varepsilon\le\varepsilon_d`$. The constants depend only on $`d`$ and
are uniform over the probability space and realization.

This resolves the Brownian-sheet small-deviation conjecture stated as
[Conjecture 2.12 by Bilyk–Lacey–Vagharshakyan](https://arxiv.org/pdf/0705.4619v3#page=6)
in dimensions $`d\ge3`$, determining the exact logarithmic exponent in the
uniform norm. The case $`d=2`$ was proved by
[Talagrand](https://doi.org/10.1214/aop/1176988605).

## Notation: entropy numbers and Kolmogorov widths

For Banach spaces $`X,Y`$, write $`B_X=\{x\in X:\|x\|_X\le1\}`$.
For $`K\subset Y`$ and $`t\gt 0`$, let $`N(K,t;Y)`$ be the least number of closed
radius-$`t`$ balls, with centers in $`Y`$, needed to cover $`K`$, possibly infinite.
For a bounded linear operator $`T:X\to Y`$ and $`k\in\mathbb N`$, define the dyadic entropy numbers by

```math
e_k(T)=\inf\{t\gt 0:N(T(B_X),t;Y)\le2^{k-1}\}.
```

For Kolmogorov widths, the infimum runs over linear subspaces $`V\subset Y`$ with $`\dim V\lt k`$:

```math
d_k(T)=\inf_{\dim V\lt k}\sup_{x\in B_X}\inf_{v\in V}\|Tx-v\|_Y.
```

For a set $`K\subset Y`$, we use $`e_k(K;Y)`$ and $`d_k(K;Y)`$ for the
corresponding entropy numbers and Kolmogorov widths.
In particular, $`e_k(T)=e_k(T(B_X);Y)`$ and $`d_k(T)=d_k(T(B_X);Y)`$.

## 2. Anchored integration operators (Theorem 1.2)

For $`1\lt p\lt\infty`$, consider the non-periodic integration operator

```math
\begin{aligned}
T_{d,p} &:L_p([0,1]^d)\longrightarrow C([0,1]^d),\\
(T_{d,p}g)(\mathbf t)&=\int_{[0,\mathbf t]}g(\mathbf u)\,d\mathbf u,
\qquad [0,\mathbf t]=\prod_{i=1}^d[0,t_i],
\end{aligned}
```

and write $`T_d=T_{d,2}`$. The image $`K_d=T_d(B_{L_2([0,1]^d)})`$ is the
non-periodic anchored mixed Sobolev unit ball and the Cameron–Martin unit ball
of the Brownian sheet. Its elements vanish whenever one coordinate is zero and
have mixed weak derivative satisfying
$`\|\partial_1\cdots\partial_d f\|_{L_2}\le1`$.
In the uniform norm on $`C([0,1]^d)`$, it holds

```math
e_k(T_{d,p})\asymp k^{-1}(\log k)^{d-1/2},
\qquad k\to\infty,
```

for every $`1\lt p\lt\infty`$, and the same order holds for $`d_k(T_{d,p})`$
when $`2\le p\lt\infty`$. The image ball $`T_{d,p}(B_{L_p})`$ is compact.

The entropy estimate resolves
[Bilyk–Lacey–Vagharshakyan's Conjecture 2.9](https://arxiv.org/pdf/0705.4619v3#page=5)
for $`1\lt p\lt\infty`$.
The matching upper entropy estimate for $`p\ge2`$ was known from
[Dunker–Linde–Kühn–Lifshits](https://doi.org/10.1006/jath.1999.3354).

## 3. Periodic classes with mixed smoothness (Theorem 1.3)

Let $`\mathbb T^d=(\mathbb R/\mathbb Z)^d`$ carry normalized Lebesgue measure.
Choose a real even $`\varphi_0\in C_c^\infty(\mathbb R)`$ equal to one on
$`[-1,1]`$ and zero outside $`[-2,2]`$, and put

```math
\varphi_j(\xi)=\varphi_0(2^{-j}\xi)-\varphi_0(2^{1-j}\xi),
\qquad j\ge1.
```

For $`\mathbf s\in\mathbb N_0^d`$, let $`|\mathbf s|=\sum_i s_i`$. For
$`f\in L_1(\mathbb T^d)`$ and $`\mathbf k\in\mathbb Z^d`$, define the Fourier coefficient and tensor dyadic block by

```math
\begin{aligned}
\widehat f(\mathbf k)
&=\int_{\mathbb T^d} f(\mathbf x)
       e^{-2\pi i\langle\mathbf k,\mathbf x\rangle}\,d\mathbf x,\\
\Delta_{\mathbf s}f(\mathbf x)
&=\sum_{\mathbf k\in\mathbb Z^d}
 \left(\prod_{i=1}^d\varphi_{s_i}(k_i)\right)
 \widehat f(\mathbf k)e^{2\pi i\langle\mathbf k,\mathbf x\rangle}.
\end{aligned}
```

The periodic mixed Sobolev and Besov norms are

```math
\begin{aligned}
\|f\|_{\mathbf W_p^r}
&=\left\|\left(\sum_{\mathbf s\in\mathbb N_0^d}
  2^{2r|\mathbf s|}|\Delta_{\mathbf s}f|^2\right)^{1/2}\right\|_{L_p},\\
\|f\|_{\mathbf B_{p,\theta}^r}
&=\left\|\left(2^{r|\mathbf s|}
       \|\Delta_{\mathbf s}f\|_{L_p}\right)_{\mathbf s\in\mathbb N_0^d}
  \right\|_{\ell_\theta},
\qquad
\mathbf H_p^r=\mathbf B_{p,\infty}^r.
\end{aligned}
```

Here, $`\mathbf W_p^r`$ is the periodic mixed Bessel-potential space for
$`1\lt p\lt \infty`$, $`\mathbf B_{p,\theta}^r`$ is the mixed Besov space, and
$`\mathbf H_p^r`$ is the Nikol'skii space. We identify real $`L_1`$ functions
that agree almost everywhere and require the displayed norm to be finite.
For $`\theta\lt \infty`$, $`\|(a_{\mathbf s})\|_{\ell_\theta} =(\sum_{\mathbf s}|a_{\mathbf s}|^\theta)^{1/\theta}`$;
for $`\theta=\infty`$, it is $`\sup_{\mathbf s}|a_{\mathbf s}|`$.
The $`L_p`$ norm is the usual integral norm, with essential supremum when
$`p=\infty`$. In the parameter ranges below, write $`I:f\mapsto f`$ for the canonical embedding into
$`L_\infty(\mathbb T^d)`$, and use $`1/\infty=0`$.
The output norm is the essential supremum, equal to the supremum norm
on continuous representatives.

Let $`d\ge2`$. As $`k\to\infty`$, the following hold.

(i) For $`2\le p\lt\infty`$ and $`r\gt 1/2`$,

```math
e_k(I:\mathbf W_p^r\to L_\infty)\asymp d_k(I:\mathbf W_p^r\to L_\infty)
\asymp k^{-r}(\log k)^{r(d-1)+1/2}.
```

For $`1\lt p\lt\infty`$ and $`r\gt 1/p`$, the lower bound for $`e_k`$ remains valid.

(ii) For $`2\le p\le\infty`$, $`2\le\theta\le\infty`$ and $`r\gt 1/2`$,

```math
e_k(I:\mathbf B_{p,\theta}^r\to L_\infty)\asymp d_k(I:\mathbf B_{p,\theta}^r\to L_\infty)
\asymp k^{-r}(\log k)^{(r+1/2-1/\theta)(d-1)+1/2}.
```

The Nikol'skii spaces $`\mathbf H_p^r=\mathbf B_{p,\infty}^r`$ correspond to
$`\theta=\infty`$. For $`1\lt p\le\infty`$, $`1\le\theta\le\infty`$ and
$`r\gt 1/p`$, the lower bound for $`e_k`$ remains valid.

The estimates hold for every cutoff specified above, both for the classes of
continuous functions and for the full $`L_1`$ classes; the constants may also
depend on that cutoff. The entropy order in (ii) also holds for the
coordinatewise mean-zero Besov classes (Remark 3.3) when $`\theta\lt\infty`$.

For $`d\ge3`$, the Sobolev width estimate resolves the finite-$`p`$ part of
[Conjecture 4.21](https://arxiv.org/pdf/1601.03978v3#page=50) in
Dũng–Temlyakov–Ullrich's *Hyperbolic Cross Approximation*, and the Nikol'skii
estimate resolves [Conjecture 4.27](https://arxiv.org/pdf/1601.03978v3#page=51)
throughout its stated range. These determine the optimal subspace-approximation
rates, including their logarithmic exponents, in the corresponding ranges
of [Outstanding Open Problem 1.3](https://arxiv.org/pdf/1601.03978v3#page=12).

The Sobolev entropy estimate supplies the conjectured lower bound in
[Temlyakov's (1.8)](https://arxiv.org/pdf/1602.08712v1#page=5) and
[Conjecture 6.16](https://arxiv.org/pdf/1601.03978v3#page=87) of the book.
Together with the Besov and Nikol'skii lower bounds, it addresses the
entropy question in [Outstanding Open Problem 1.6](https://arxiv.org/pdf/1601.03978v3#page=12)
in the displayed ranges.

## 4. Probabilistic small ball inequality (Theorem 2.1)

Fix a nonzero real $`\psi\in C_c^\infty(0,1)`$ with $`\|\psi\|_\infty\le1`$.
For a dyadic rectangle $`R=\prod_i[m_i2^{-s_i},(m_i+1)2^{-s_i})`$ put
$`a_R(\mathbf x)=\prod_i\psi(2^{s_i}x_i-m_i)`$, let $`\mathcal D_n`$ be the
rectangles of volume $`2^{-n}`$, $`S_n=\binom{n+d-1}{d-1}`$, and let
$`(G_R)`$ be independent standard Gaussian variables. Then there are
$`a,b\gt 0`$, depending only on $`d`$ and $`\psi`$, such that for all
sufficiently large $`n`$

```math
\mathbb P\Bigl\{\Bigl\|\sum_{R\in\mathcal D_n}G_Ra_R\Bigr\|_\infty
\le a\sqrt{nS_n}\Bigr\}\le\exp(-b|\mathcal D_n|).
```

The certificate proves this for every nonzero continuous $`\psi`$ supported in
$`(0,1)`$ with $`|\psi|\le1`$, together with Lemmas 2.3–2.5,
Proposition 2.6 and Remarks 2.2, 2.7 and 2.9.

## 5. Fractional integration (Theorem 5.1)

For $`r\gt 1/2`$, let $`R_r:L_2(0,1)\to C([0,1])`$ be the Riemann–Liouville operator

```math
(R_r g)(t)=\frac1{\Gamma(r)}
 \int_0^t(t-u)^{r-1}g(u)\,du,
```

and $`T_d^{(r)}=R_r^{\otimes d}:L_2([0,1]^d)\to C([0,1]^d)`$. Then

```math
e_k(T_d^{(r)})\asymp d_k(T_d^{(r)})
\asymp k^{-r}(\log k)^{r(d-1)+1/2}.
```

In particular, $`T_d^{(1)}=T_d`$.

## 6. Fractional and integrated Brownian sheets (Theorem 5.2)

For $`\mathbf H=(H_1,\ldots,H_d)\in(0,1)^d`$, let $`B^{\mathbf H}`$ be the
continuous centered Gaussian sheet with covariance

```math
\mathbb E[B^{\mathbf H}(\mathbf s)B^{\mathbf H}(\mathbf t)]
=\prod_{i=1}^d
 \frac{s_i^{2H_i}+t_i^{2H_i}-|s_i-t_i|^{2H_i}}2.
```

Let $`H_*=\min_iH_i`$ occur in exactly $`\nu\ge2`$ coordinates, and let
$`m\in\mathbb N_0`$. Then

```math
\begin{aligned}
-\log\mathbb P\{\|B^{\mathbf H}\|_\infty\le\varepsilon\}
&\asymp \varepsilon^{-1/H_*}
 \bigl(\log(1/\varepsilon)\bigr)^{\nu-1+\nu/(2H_*)},\\
-\log\mathbb P\{\|R_m^{\otimes d}B\|_\infty\le\varepsilon\}
&\asymp \varepsilon^{-2/(2m+1)}
 \bigl(\log(1/\varepsilon)\bigr)^{d-1+d/(2m+1)}.
\end{aligned}
```

The constants and thresholds depend only on $`d`$ and the regularity
parameters. They are uniform over the probability space and realization.

The exact fractional rate is posed as an open problem in the
[remark after Kühn–Linde's Corollary 7.5](https://users.fmi.uni-jena.de/~hicke/inst_stoch/Linde/SERREP5.pdf#page=27).
The estimate above attains their upper order and closes this gap in the
stated repeated-minimum range. The equal-index two-dimensional case was
established by [Belinsky–Linde](https://doi.org/10.1023/A:1016263614257).

## 7. Tensor-product Matérn fields (Corollary 5.3)

Let $`X`$ be a centered continuous Gaussian field on $`[0,1]^d`$ with covariance
$`\mathbb E[X(\mathbf s)X(\mathbf t)]=\prod_{i=1}^dk_i(s_i-t_i)`$, where the
spectral density of $`k_i`$ is proportional to $`(\kappa_i^2+\xi^2)^{-h-1/2}`$
for a common $`h\gt 0`$. Its Cameron–Martin embedding
$`I_X:H_X\to C([0,1]^d)`$ satisfies

```math
e_k(I_X)\asymp d_k(I_X)\asymp k^{-h-1/2}(\log k)^{(h+1/2)(d-1)+1/2},
\qquad
-\log\mathbb P\{\|X\|_\infty\le\varepsilon\}
\asymp\varepsilon^{-1/h}\bigl(\log(1/\varepsilon)\bigr)^{d-1+d/(2h)}.
```

## 8. Quantization and deterministic integration (Corollary 5.4)

For a continuous Gaussian field $`X`$ with law $`\mu`$ on $`C([0,1]^d)`$, let
$`q_{m,p}(\mu)=\inf_{f_1,\ldots,f_m}(\mathbb E\min_j\|X-f_j\|_\infty^p)^{1/p}`$,
$`p=1,2`$, and let $`\mu_m`$ be the empirical measure of $`m`$ independent copies.
For $`X=B`$, $`B^{\mathbf H}`$ (with $`\nu\ge2`$) and $`R_q^{\otimes d}B`$,

```math
q_{m,1}(\mu)\asymp q_{m,2}(\mu)\asymp\mathbb E[W_2(\mu,\mu_m)]\asymp
\begin{cases}
(\log\log m)^{d-1/2}(\log m)^{-1/2}, & X=B,\\
(\log\log m)^{H_*(\nu-1)+\nu/2}(\log m)^{-H_*}, & X=B^{\mathbf H},\\
(\log\log m)^{(q+1)(d-1)+1/2}(\log m)^{-q-1/2}, & X=R_q^{\otimes d}B.
\end{cases}
```

The minimax error of deterministic integration of 1-Lipschitz functionals,
using at most $`m`$ adaptive exact evaluations, equals $`q_{m,1}(\mu)`$ and
therefore has the same rates.

## Scope of the formalization

Every lower bound follows the proof of the paper: Theorem 2.1, the covering
argument (3.9)–(3.11) and, for Gaussian fields, the lower half of the
Kuelbs–Li–Linde correspondence (4.1). The upper bounds, which the paper
imports from the literature, are proved internally, partly by other routes.

Not formalized are Remarks 2.8 and 3.4, the last part of Remark 3.3, and the upper half of
(4.1) as a general theorem. The last part of Remark 3.3 extends Theorem 1.3(i) to
$`1\lt p\lt 2`$ and relies on Belinsky's upper bound.

[PAPER_TO_LEAN.md](PAPER_TO_LEAN.md) maps each numbered result, lemma and
proof step of the paper to its Lean declaration and records the conventions.

## Statement-to-certificate map

The combined endpoint is
[mainBodyResults_certified](BrownianSharp/AlignmentMainBodyCertified.lean#L226),
of type `BrownianSharp.AlignmentMainBodyCertified.MainBodyResultsStatement`.
Each row below is a field of that conjunction; full names begin with `BrownianSharp.`.

| Certified result | Lean statement |
|---|---|
| Theorem 1.1: Brownian-sheet two-sided small deviations | [AlignmentPaperSheetUniverse.BrownianTwoSidedStatementU](BrownianSharp/AlignmentPaperSheetUniverse.lean#L23) |
| Theorem 1.2: entropy and Kolmogorov numbers of $`T_{d,p}`$, compactness | [AlignmentMainBodyCertified.AnchoredLpTheoremStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L44) |
| Theorem 1.3: entropy lower bounds and Kolmogorov widths, every admissible cutoff, continuous and full $`L_1`$ classes | [AlignmentPeriodicCutoffCertified.ArbitraryCutoffMainResultsStatement](BrownianSharp/AlignmentPeriodicCutoffCertified.lean#L15) |
| Theorem 1.3: two-sided Sobolev and Nikol'skii entropy | [AlignmentMainBodyCertified.PeriodicEndpointEntropyStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L60) |
| Theorem 1.3: two-sided Besov entropy and Kolmogorov numbers | [AlignmentMainBodyCertified.PeriodicBesovUpperRangeStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L78) |
| Theorem 1.3: two-sided Besov rates, full $`L_1`$ classes | [AlignmentMainBodyCertified.FullL1PeriodicBesovUpperRangeStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L94) |
| Theorem 1.3: two-sided Sobolev and Nikol'skii entropy, full $`L_1`$ classes | [AlignmentPaperFullL1PeriodicEntropy.FullL1PeriodicEndpointEntropyStatement](BrownianSharp/AlignmentPaperFullL1PeriodicEntropy.lean#L20) |
| Theorem 2.1: probabilistic small ball inequality | [AlignmentPaperGenericBumpCertified.AdmissibleBumpIidConfinementStatement](BrownianSharp/AlignmentPaperGenericBumpCertified.lean#L119) |
| Remark 2.2: exceptional set (2.7) | [AlignmentMainBodyCertified.ExceptionalSetStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L138) |
| Remark 2.7: sharpness of Proposition 2.6 | [AlignmentMainBodyCertified.ConvexTailSharpnessStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L172) |
| Remark 2.9: failure for $`d=1`$ | [AlignmentMainBodyCertified.OneDimensionalFailureStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L150) |
| Lemma 3.1: Carl's inequality for widths and entropy | [AlignmentMainBodyCertified.CarlLemmaStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L126) |
| Remark 3.3: coordinatewise mean-zero Besov classes | [AlignmentMainBodyCertified.MeanZeroBesovEntropyStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L111) |
| Theorem 5.1: fractional integration | [AlignmentPaperFractional.PaperFractionalTensorStatement](BrownianSharp/AlignmentPaperFractional.lean#L36) |
| Theorem 5.2: fractional Brownian sheets | [AlignmentPaperSheetUniverse.FractionalSheetStatementU](BrownianSharp/AlignmentPaperSheetUniverse.lean#L32) |
| Theorem 5.2: integrated Brownian sheets | [AlignmentPaperSheetUniverse.IntegratedSheetStatementU](BrownianSharp/AlignmentPaperSheetUniverse.lean#L45) |
| Corollary 5.3: Matérn entropy and Kolmogorov numbers | [AlignmentPaperMaternNumbersCertified.MaternCMNumbersStatement](BrownianSharp/AlignmentPaperMaternNumbersCertified.lean#L12) |
| Corollary 5.3: Matérn small deviations | [AlignmentPaperMaternSmallBallUpper.MaternRawSmallBallStatement](BrownianSharp/AlignmentPaperMaternSmallBallUpper.lean#L72) |
| Corollary 5.4: quantization and empirical Wasserstein rates | [AlignmentPaperQuantizationSheetFinal.PaperQuantizationResultsStatement](BrownianSharp/AlignmentPaperQuantizationSheetFinal.lean#L391) |
| Section 5.3: minimax deterministic integration equals $`q_{m,1}`$ | [AlignmentMainBodyCertified.PaperDeterministicIntegrationStatement](BrownianSharp/AlignmentMainBodyCertified.lean#L187) |
| Section 5.3: deterministic integration rates | [AlignmentPaperDeterministicIntegrationRates.DeterministicIntegrationRatesStatement](BrownianSharp/AlignmentPaperDeterministicIntegrationRates.lean#L23) |

Lemmas 2.3, 2.4 and Proposition 2.6 are stated in
[AlignmentPaperSection2Lemmas.lean](BrownianSharp/AlignmentPaperSection2Lemmas.lean).
Lemma 2.5, Lemma 3.2 and the proof routes are listed in
[PAPER_TO_LEAN.md](PAPER_TO_LEAN.md).

## Install and verify

Install **Git** and **elan**, Lean's version manager, using the
[official Lean installation instructions](https://lean-lang.org/install/manual/).
Lake is included with Lean. Open a terminal in this folder, containing lakefile.toml and CertificateAudit.lean,
and run these commands one at a time:

```sh
lean --version
lake exe cache get
lake build
lake env lean CertificateAudit.lean
```

The first command should report **Lean 4.34.1**; elan may download it on first use.
The cache command fetches the pinned dependencies and Mathlib's compiled cache.
The certificate's own proofs are built from the bundled sources.

Success requires both a successful build and an audit ending in:

```text
PASS: 11338 component declarations use only foundational axioms. Exact public statement types checked above.
```

[CertificateAudit.lean](CertificateAudit.lean) checks the exact exported theorem
types and the transitive axiom dependencies of every imported local
declaration, including private and generated helpers. It accepts only
`propext`, `Classical.choice`, and `Quot.sound`. Unfinished proofs using `sorry`
and additional mathematical axioms fail the audit. The declaration count
includes helpers; it is not a count of headline theorems.

The files [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and
[lake-manifest.json](lake-manifest.json) pin Lean **4.34.1** and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, together with transitive dependency
revisions. Keep them unchanged when reproducing the check. The commands create
the excluded `.lake/` dependency and build cache locally.

## Read the formal statements

Start with [AlignmentMainBodyCertified.lean](BrownianSharp/AlignmentMainBodyCertified.lean)
and follow its statement fields; [PAPER_TO_LEAN.md](PAPER_TO_LEAN.md) gives the
scope of each field. Gaussian-sheet targets are in
[AlignmentLatestStatements.lean](BrownianSharp/AlignmentLatestStatements.lean);
operator targets are in
[AlignmentOperatorStatements.lean](BrownianSharp/AlignmentOperatorStatements.lean).
The Brownian realization interface is
[BrownianSheetOnCube.lean](BrownianSharp/BrownianSheetOnCube.lean).

For terminal inspection, create a local file named `Inspect.lean` with:

```lean
import BrownianSharp

#check BrownianSharp.AlignmentMainBodyCertified.mainBodyResults_certified
#print BrownianSharp.AlignmentMainBodyCertified.MainBodyResultsStatement
#print BrownianSharp.AlignmentPaperSheetUniverse.BrownianTwoSidedStatementU
#print axioms BrownianSharp.AlignmentMainBodyCertified.mainBodyResults_certified
```

Then run `lake env lean Inspect.lean` after the build. Use `#print` on the
referenced definitions to inspect their hypotheses, ambient spaces, norms
and index conventions. The Gaussian results quantify over continuous
realizations with the stated covariance. The small-ball estimates are proved
from these hypotheses.

Lean checks the formal proof terms; the correspondence between the displayed
mathematics and the formal definitions requires mathematical review.
The formalization was developed with AI assistance.

## References and conjecture sources

Conjecture numbers refer to the linked author versions.

- Dinh Dũng, Vladimir Temlyakov, and Tino Ullrich,
  [Hyperbolic Cross Approximation](https://doi.org/10.1007/978-3-319-92240-9),
  Birkhäuser (2018).
  [Open author version](https://arxiv.org/pdf/1601.03978v3):
  Outstanding Open Problems 1.3 and 1.6; Conjectures 4.21, 4.27 and 6.16;
  Sections 6.4–6.5.
- Dmitriy Bilyk, Michael T. Lacey, and Armen Vagharshakyan,
  [On the Small Ball Inequality in All Dimensions](https://arxiv.org/pdf/0705.4619v3),
  J. Funct. Anal. 254 (2008), 2470–2502.
  Conjecture 2.9 states the covering-entropy rate; Conjecture 2.12 states
  the Brownian-sheet small-ball rate.
- Vladimir Temlyakov,
  [On the Entropy Numbers of the Mixed Smoothness Function Classes](https://arxiv.org/pdf/1602.08712v1),
  J. Approx. Theory 217 (2017), 26–56, equation (1.8), for the Sobolev entropy conjecture.
- Michel Talagrand,
  [The Small Ball Problem for the Brownian Sheet](https://doi.org/10.1214/aop/1176988605),
  Ann. Probab. 22 (1994), 1331–1354, for dimension two.
- T. Dunker, W. Linde, T. Kühn, and M. A. Lifshits,
  [Metric Entropy of Integration Operators and Small Ball Probabilities for the Brownian Sheet](https://doi.org/10.1006/jath.1999.3354),
  J. Approx. Theory 101 (1999), 63–77, for the probability lower bound
  in all dimensions.
- Eduard Belinsky and Werner Linde,
  [Small Ball Probabilities of Fractional Brownian Sheets via Fractional Integration Operators](https://doi.org/10.1023/A:1016263614257),
  J. Theoret. Probab. 15 (2002), 589–612, for the sharp two-dimensional
  fractional-sheet estimate.
- Thomas Kühn and Werner Linde,
  [Optimal Series Representation of Fractional Brownian Sheets](https://projecteuclid.org/euclid.bj/1078435223),
  Bernoulli 8 (2002), 669–696.
  [Open author version](https://users.fmi.uni-jena.de/~hicke/inst_stoch/Linde/SERREP5.pdf):
  Theorem 5.7, Proposition 5.8, Corollary 7.5 and the following remark.
- Wenbo V. Li and Werner Linde,
  [Approximation, Metric Entropy and Small Ball Estimates for Gaussian Measures](https://doi.org/10.1214/aop/1022677459),
  Ann. Probab. 27 (1999), 1556–1578, and
  James Kuelbs and Wenbo V. Li,
  [Metric Entropy and the Small Ball Problem for Gaussian Measures](https://doi.org/10.1006/jfan.1993.1107),
  J. Funct. Anal. 116 (1993), 133–157, for the entropy–small-deviation correspondence (4.1).

## License

MIT for project-owned material, with the retained Apache-2.0 exception for
the ported Isoperimetric and TauCeti sources.
See [LICENSE](LICENSE) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
