# Entropy, Kolmogorov widths, and Brownian-sheet small deviations

Throughout, $d\ge2$, $\mathbb N=\{1,2,\ldots\}$, and
$\mathbb N_0=\{0,1,2,\ldots\}$. The spaces and operators are over the real
scalars; Fourier expansions use complex notation, with $i^2=-1$.
The spaces $L_p$ on the cube use Lebesgue measure, and
$C([0,1]^d)$ carries the supremum norm
$\|f\|_\infty=\sup_{\mathbf t\in[0,1]^d}|f(\mathbf t)|$.
All logarithms are natural. We write $u_k\lesssim v_k$ if $u_k\le C v_k$ for a fixed $C>0$, and $u_k\asymp v_k$ when both
$u_k\lesssim v_k$ and $v_k\lesssim u_k$ hold with positive constants for all
sufficiently large $k$; the analogous convention applies as a radius tends
to zero. Constants may depend on the fixed dimension and the displayed
smoothness and integrability parameters, but not on $k$ or the radius.

## 1. Brownian-sheet small deviations

Let $(\Omega,\mathcal F,\mathbb P)$ be any probability space.
A centered Gaussian field means that every finite collection of evaluations
is jointly Gaussian and has mean zero. All fields below are measurable as
maps from $\Omega$ into $C([0,1]^d)$; their sample paths are continuous.

The Brownian sheet $B$ is the centered Gaussian field with covariance

$$
\mathbb E[B(\mathbf s)B(\mathbf t)]
=\prod_{i=1}^d\min(s_i,t_i).
$$

For any such random field $X$, set
$\|X\|_\infty=\sup_{\mathbf t\in[0,1]^d}|X(\mathbf t)|$.
Then

$$
-\log\mathbb P\{\|B\|_\infty\le\varepsilon\}
\asymp\varepsilon^{-2}
 \bigl(\log(1/\varepsilon)\bigr)^{2d-1},
\qquad \varepsilon\downarrow0.
$$

There are positive constants $c_d,C_d,\varepsilon_d$, with
$\varepsilon_d<e^{-1}$, giving both inequalities for every
$0<\varepsilon\le\varepsilon_d$. They depend only on $d$ and are chosen
before the probability space and realization.

## Notation: entropy, widths, and approximation numbers

For Banach spaces $X,Y$, write $B_X=\{x\in X:\|x\|_X\le1\}$.
For $K\subset Y$ and $t>0$, let $N(K,t;Y)$ be the least number of closed
radius-$t$ balls, with centers in $Y$, needed to cover $K$, possibly infinite.
For a bounded linear operator $T:X\to Y$ and $k\in\mathbb N$, set

$$
\begin{aligned}
e_k(T)
&=\inf\{t>0:N(T(B_X),t;Y)\le2^{k-1}\},\\
d_k(T)
&=\inf_{\substack{V\subset Y\ \mathrm{linear}\\\dim V<k}}
  \sup_{x\in B_X}\inf_{v\in V}\|Tx-v\|_Y,\\
a_k(T)
&=\inf_{\substack{A:X\to Y\ \mathrm{bounded\ linear}\\
                 \mathrm{rank}A<k}}\|T-A\|_{X\to Y}.
\end{aligned}
$$

Thus $e_k$ are dyadic entropy numbers, $d_k$ are Kolmogorov widths, and
$a_k$ are approximation numbers. For a set $K\subset Y$, write $e_k(K;Y)$
and $d_k(K;Y)$ for the corresponding covering and subspace quantities.
In particular, $e_k(T)=e_k(T(B_X);Y)$ and $d_k(T)=d_k(T(B_X);Y)$.
Here $\mathrm{rank}A=\dim A(X)$, and
$\|T-A\|_{X\to Y}=\sup_{x\in B_X}\|(T-A)x\|_Y$.
All dimension and rank bounds are **strictly less than $k$**.

## 2. Anchored mixed Sobolev ball: entropy and Kolmogorov widths

Consider the non-periodic integration operator

$$
\begin{aligned}
T_d &:L_2([0,1]^d)\longrightarrow C([0,1]^d),\\
(T_dg)(\mathbf t)&=\int_{[0,\mathbf t]}g(\mathbf u)\,d\mathbf u,
\qquad [0,\mathbf t]=\prod_{i=1}^d[0,t_i].
\end{aligned}
$$

Its image $K_d=T_d(B_{L_2([0,1]^d)})$ is the anchored mixed Sobolev
unit ball, with the supremum norm on $C([0,1]^d)$. The anchoring is the
zero boundary condition whenever any coordinate is zero. Then

$$
e_k(T_d)\asymp d_k(T_d)
\asymp k^{-1}(\log k)^{d-1/2},
\qquad k\to\infty.
$$

Equivalently, its covering entropy satisfies

$$
\log N(K_d,t;C([0,1]^d))
\asymp t^{-1}\bigl(\log(1/t)\bigr)^{d-1/2},
\qquad t\downarrow0.
$$

## 3. Periodic mixed smoothness: entropy lower bounds and sharp widths

Let $\mathbb T^d=(\mathbb R/\mathbb Z)^d$ carry normalized Lebesgue measure.
Choose a real even $\varphi_0\in C_c^\infty(\mathbb R)$ equal to one on
$[-1,1]$ and zero outside $[-2,2]$, and put

$$
\varphi_j(\xi)=\varphi_0(2^{-j}\xi)-\varphi_0(2^{1-j}\xi),
\qquad j\ge1.
$$

For $\mathbf s\in\mathbb N_0^d$, let $|\mathbf s|=\sum_i s_i$. For
$f\in L_1(\mathbb T^d)$ and $\mathbf k\in\mathbb Z^d$, define the Fourier coefficient and tensor dyadic block by

$$
\begin{aligned}
\widehat f(\mathbf k)
&=\int_{\mathbb T^d} f(\mathbf x)
       e^{-2\pi i\langle\mathbf k,\mathbf x\rangle}\,d\mathbf x,\\
\Delta_{\mathbf s}f(\mathbf x)
&=\sum_{\mathbf k\in\mathbb Z^d}
 \left(\prod_{i=1}^d\varphi_{s_i}(k_i)\right)
 \widehat f(\mathbf k)e^{2\pi i\langle\mathbf k,\mathbf x\rangle}.
\end{aligned}
$$

The periodic mixed Sobolev and Besov norms are

$$
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
$$

Here $\mathbf W_p^r$ is the mixed Bessel-potential space for $1<p<\infty$,
$\mathbf B_{p,\theta}^r$ is the mixed Besov space, and $\mathbf H_p^r$ is
the Nikol'skii space. Each space consists of the real $L_1$ functions
with finite displayed norm, modulo equality almost everywhere.
For $\theta<\infty$, $\|(a_{\mathbf s})\|_{\ell_\theta} =(\sum_{\mathbf s}|a_{\mathbf s}|^\theta)^{1/\theta}$;
for $\theta=\infty$, it is $\sup_{\mathbf s}|a_{\mathbf s}|$.
The $L_p$ norm is the usual integral norm, with essential supremum when
$p=\infty$. In the parameter ranges below, write $I:f\mapsto f$ for the canonical embedding into
$L_\infty(\mathbb T^d)$, and use $1/\infty=0$.
The output norm is the essential supremum, equal to the supremum norm
on continuous representatives.

For $1<p\le\infty$, $r>1/p$, and $1\le\theta\le\infty$, the certified
**entropy lower bounds** are

$$
\begin{aligned}
e_k(I:\mathbf W_p^r\to L_\infty)
&\gtrsim k^{-r}(\log k)^{r(d-1)+1/2}
&& (p<\infty),\\
e_k(I:\mathbf B_{p,\theta}^r\to L_\infty)
&\gtrsim k^{-r}(\log k)^{(r+1/2-1/\theta)(d-1)+1/2},\\
e_k(I:\mathbf H_p^r\to L_\infty)
&\gtrsim k^{-r}(\log k)^{(r+1/2)(d-1)+1/2}.
\end{aligned}
$$

For $r>1/2$, the certified **two-sided Kolmogorov width estimates** are

$$
\begin{aligned}
d_k(I:\mathbf W_p^r\to L_\infty)
&\asymp k^{-r}(\log k)^{r(d-1)+1/2}
&& (2\le p<\infty),\\
d_k(I:\mathbf H_p^r\to L_\infty)
&\asymp k^{-r}(\log k)^{(r+1/2)(d-1)+1/2}
&& (2\le p\le\infty).
\end{aligned}
$$

These statements hold for every cutoff specified above; constants may
also depend on that fixed cutoff. The source classes and ambient
$L_\infty$ norm are specified by the displayed definitions.

## 4. Tensor fractional integration: entropy and Kolmogorov widths

For $\alpha>1/2$, let $R_\alpha:L_2(0,1)\to C([0,1])$ be the Riemann–Liouville operator

$$
(R_\alpha g)(t)=\frac1{\Gamma(\alpha)}
 \int_0^t(t-u)^{\alpha-1}g(u)\,du.
$$

Here $\Gamma$ is Euler's Gamma function. For
$\boldsymbol\alpha=(\alpha_1,\ldots,\alpha_d)$ with all $\alpha_i>1/2$, set

$$
T_{\boldsymbol\alpha}
=R_{\alpha_1}\otimes\cdots\otimes R_{\alpha_d}
:L_2([0,1]^d)\longrightarrow C([0,1]^d).
$$

Let $r=\min_i\alpha_i$, and let
$\nu=\#\{i:\alpha_i=r\}$ be its multiplicity. If $\nu\ge2$, then

$$
e_k(T_{\boldsymbol\alpha})\asymp d_k(T_{\boldsymbol\alpha})
\asymp k^{-r}(\log k)^{r(\nu-1)+1/2}.
$$

Explicitly, the tensor notation means

$$
(T_{\boldsymbol\alpha}g)(\mathbf t)
=\int_{\prod_{i=1}^d[0,t_i)}
 \left(\prod_{i=1}^d\frac{(t_i-u_i)^{\alpha_i-1}}{\Gamma(\alpha_i)}\right)
 g(\mathbf u)\,d\mathbf u.
$$

Thus the kernel is causal and Gamma-normalized. In particular,
$T_{\mathbf1}=T_d$ for $\mathbf1=(1,\ldots,1)$.

## 5. Fractional Brownian-sheet small deviations

For $\mathbf H=(H_1,\ldots,H_d)\in(0,1)^d$, let $B^{\mathbf H}$ be the
continuous centered Gaussian sheet with measurable path map and covariance

$$
\mathbb E[B^{\mathbf H}(\mathbf s)B^{\mathbf H}(\mathbf t)]
=\prod_{i=1}^d
 \frac{s_i^{2H_i}+t_i^{2H_i}-|s_i-t_i|^{2H_i}}2.
$$

Let $H_*=\min_iH_i$ occur in exactly $\nu\ge2$ coordinates. Then

$$
-\log\mathbb P\{\|B^{\mathbf H}\|_\infty\le\varepsilon\}
\asymp \varepsilon^{-1/H_*}
 \bigl(\log(1/\varepsilon)\bigr)^{\nu-1+\nu/(2H_*)}.
$$

## 6. Integrated Brownian-sheet small deviations

For $\mathbf m=(m_1,\ldots,m_d)\in\mathbb N_0^d$, define

$$
X_{\mathbf m}=(R_{m_1}\otimes\cdots\otimes R_{m_d})B,
\qquad R_0=\mathrm{Id}.
$$

Thus $X_{\mathbf m}$ integrates the Brownian sheet $m_i$ times from zero
in coordinate $i$. If $m_*=\min_i m_i$ occurs in exactly $\nu\ge2$
coordinates, then

$$
-\log\mathbb P\{\|X_{\mathbf m}\|_\infty\le\varepsilon\}
\asymp \varepsilon^{-2/(2m_*+1)}
 \bigl(\log(1/\varepsilon)\bigr)^{\nu-1+\nu/(2m_*+1)}.
$$

In both the fractional and integrated estimates, the norm is the full
continuous-path supremum norm. Positive constants and a positive radius
threshold depend only on $d$ and the regularity vector, and are chosen
before the probability space and process realization.

The fractional rate with $H_i=1/2$ for every $i$, and the integrated rate
with $m_i=0$ for every $i$, both reduce to the Brownian-sheet rate in Result 1.

## 7. Approximation numbers and the approximation-to-width quotient

For the tensor fractional-integration operator $T_{\boldsymbol\alpha}$
defined above, let $r=\min_i\alpha_i$ and
$\nu=\#\{i:\alpha_i=r\}\ge2$, with all $\alpha_i>1/2$. Then

$$
a_k(T_{\boldsymbol\alpha})
\asymp k^{-r+1/2}(\log k)^{r(\nu-1)},
\qquad
\frac{a_k(T_{\boldsymbol\alpha})}{d_k(T_{\boldsymbol\alpha})}
\asymp\sqrt{\frac{k}{\log k}}.
$$

The width in the denominator is positive and finite for all sufficiently
large $k$.

## Statement-to-certificate map

The combined endpoint is
[mainBodyResults_certified](BrownianSharp/AlignmentMainBodyCertified.lean#L23),
of type `BrownianSharp.AlignmentMainBodyCertified.MainBodyResultsStatement`.
Each row below is a field of that conjunction; full names begin with `BrownianSharp.`.

| Certified result | Lean provider |
|---|---|
| Brownian-sheet two-sided small deviations | [AlignmentGaussianBrownianReverse.latest_brownian_twoSided_certified](BrownianSharp/AlignmentGaussianBrownianReverse.lean#L138) |
| Cameron–Martin covering entropy, entropy numbers, and Kolmogorov widths | [AlignmentOperatorCameronMartin.cameronMartinEntropyWidth_certified](BrownianSharp/AlignmentOperatorCameronMartin.lean#L59) |
| Periodic mixed-smoothness entropy lower bounds and Kolmogorov widths, for arbitrary admissible cutoffs | [AlignmentPeriodicCutoffCertified.arbitraryCutoffMainResults_certified](BrownianSharp/AlignmentPeriodicCutoffCertified.lean#L19) |
| Tensor fractional-integration entropy numbers and Kolmogorov widths | [AlignmentOperatorFractional.fractionalEntropyWidth_certified](BrownianSharp/AlignmentOperatorFractional.lean#L17) |
| Fractional Brownian-sheet two-sided small deviations | [AlignmentFractionalSheetStatement.latest_fractionalSheet_certified](BrownianSharp/AlignmentFractionalSheetStatement.lean#L21) |
| Integrated Brownian-sheet two-sided small deviations | [AlignmentGaussianIntegratedReverse.latest_integratedSheet_certified](BrownianSharp/AlignmentGaussianIntegratedReverse.lean#L219) |
| Fractional-integration approximation numbers and approximation-to-width quotient | [AlignmentFractionalApproximationCertified.fractionalApproximation_certified](BrownianSharp/AlignmentFractionalApproximationCertified.lean#L12) |

Explicit full-$L^1$ periodic conclusions are
[fullL1_periodic_entropy_certified](BrownianSharp/AlignmentPeriodicCutoffCertified.lean#L32)
and [fullL1_periodic_width_certified](BrownianSharp/AlignmentPeriodicCutoffCertified.lean#L36).

The full-$L^1$ entropy lower bounds use inclusion of the corresponding
continuous images. The width conclusions use the certified
continuous-representative/image identifications for Sobolev and Nikol'skii
classes in the stated width range; no full-$L^1$ Besov representative
equality is asserted.

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
PASS: 10636 component declarations use only foundational axioms. Exact public statement types checked above.
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
and follow its seven statement fields. Gaussian-sheet targets are in
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
#print BrownianSharp.Latest.BrownianTwoSidedStatement
#print axioms BrownianSharp.AlignmentMainBodyCertified.mainBodyResults_certified
```

Then run `lake env lean Inspect.lean` after the build. Use `#print` on the
referenced definitions to inspect their hypotheses, ambient spaces, norms,
and index conventions. The Brownian-sheet small-ball rate is a conclusion,
not a field of the realization interface. The headline theorem quantifies
over the specified continuous Gaussian realizations; it does not itself
construct a canonical probability space.

Lean checks the formal proof terms. Comparing the mathematical statements
above with their formal definitions remains a mathematical review task;
a successful build does not automatically check the translation from prose.
The formalization was developed with AI assistance.

## References and conjecture sources

- Dinh Dũng, Vladimir Temlyakov, and Tino Ullrich,
  [Hyperbolic Cross Approximation](https://link.springer.com/book/10.1007/978-3-319-92240-9),
  Birkhäuser (2018).
  [Open author version](https://arxiv.org/pdf/1601.03978v3):
  Outstanding Open Problem 1.3; Conjectures 4.21 and 4.27; Sections 6.4–6.5.
- Dmitriy Bilyk, Michael T. Lacey, and Armen Vagharshakyan,
  [On the Small Ball Inequality in All Dimensions](https://arxiv.org/pdf/0705.4619v3),
  J. Funct. Anal. 254 (2008), 2470–2502.
  Conjecture 2.9 states the covering-entropy rate; Conjecture 2.12 states
  the Brownian-sheet small-ball rate.
- Vladimir Temlyakov,
  [On the Entropy Numbers of the Mixed Smoothness Function Classes](https://arxiv.org/pdf/1602.08712v1),
  J. Approx. Theory (2017), equation (1.8), for the Sobolev entropy conjecture.
- Michel Talagrand,
  [The Small Ball Problem for the Brownian Sheet](https://doi.org/10.1214/aop/1176988605),
  Ann. Probab. 22 (1994), 1331–1354, for dimension two.
- T. Dunker, W. Linde, T. Kühn, and M. A. Lifshits,
  [Metric Entropy of Integration Operators and Small Ball Probabilities for the Brownian Sheet](https://www.sciencedirect.com/science/article/pii/S0021904599933543),
  J. Approx. Theory 101 (1999), 63–77, for the probability lower bound
  in all dimensions.

Conjecture numbers refer to the linked author versions. The certified ranges
are specified above; for instance, the Sobolev width clause covers finite $p$,
and the periodic entropy clauses are lower bounds.

## License

MIT for project-owned material, with the retained Apache-2.0 exception for
the ported Isoperimetric sources.
See [LICENSE](LICENSE) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
