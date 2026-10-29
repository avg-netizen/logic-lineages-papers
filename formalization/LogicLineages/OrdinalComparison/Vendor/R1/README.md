# Selected calculator source in Lean module mode

This directory adapts three complete files from the included pure-R1 calculator:
`Ordinal.lean`, `ArithmeticBounds.lean` and `Norm.lean`. They are the complete local
import closure needed for the expanded hereditary tree norm; their remaining
dependencies are pinned Lean/Mathlib modules.

The original sources are in `04-pure-r1-calculator/lean/R1Calculator/` at the
public repository root. [PROVENANCE.json](PROVENANCE.json) records original and
adapted SHA-256 hashes and the mechanical transformation. Reversing the module
header, public-import/export section, namespace and local import names reproduces
each original source byte-for-byte. No mathematical proof body was changed.

The namespace is `LogicLineages.OrdinalComparison.Vendor.R1`. The original
calculator is unchanged and remains independently buildable. Source reuse here
does not import the old 3.1.3 aggregate or a conditional semantic package.

The adaptation is necessary for Lean's modern `module` system. Importing legacy
modules into modern modules is not supported; the selected complete source is
therefore included under this new namespace, with ordinary public Mathlib imports.
Compilation and axiom audits are still required before a reused result is accepted
by the new formalization. Provenance alone is not a compile certificate.

The additive tree-weight definition matches the Wilken–Weiermann paper norm.
The calculator's `ONote` addition remains **ordinary ordinal addition**. It is
not the natural sum used by the canonical assignment papers; no natural-sum
additivity or natural-product result is inferred from an ordinary-addition lemma.
