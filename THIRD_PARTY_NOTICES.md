# Source attribution and licensing

The root MIT license covers project-owned Lean sources and documentation,
including the 54 former HaarQuarter modules now in BrownianSharp/. They were
reused from the project-owned
haar-gain-certificate at commit 1a1c830b1b5e37e7e26bb0624df36f1666371e6e.
Four defining formulas in BrownianSharp/TorusFoundations.lean were adapted from
HaarQuarter/TheoremDMixedSmoothness.lean at that commit, in an independent
namespace with minimal imports. The incorporated HaarQuarter modules now
use the BrownianSharp module prefix in imports; their declaration namespaces
and mathematical content are retained.

The two Lean files in Isoperimetric are ported from
[hojonathanho/isoperimetric](https://github.com/hojonathanho/isoperimetric),
commit 29768f8beeaf17295cdf3853d37da35d7e2b0a5f. They retain Apache-2.0;
the complete license is at [Isoperimetric/LICENSE](Isoperimetric/LICENSE).
The root MIT grant does not replace that license.

Compatibility edits in PrekopaLeindler.lean supply explicit ae_restrict_mem
and measurable-equivalence inverse arguments, update tactic case names, and
replace the removed Measurable.comp′ with explicit marginal composition.
Basic.lean is an unchanged copy of the upstream file.

Lean, Mathlib, and the transitive dependencies fetched by Lake retain their
own licenses. Their revisions are pinned; they are not bundled in the ZIP.
