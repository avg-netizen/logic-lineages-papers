# Paper 16: actual repeated-cap image and independent lexicographic arithmetic

This is the modular follow-up to the exact original repeated cap witnesses in
`LogicLineages/PersistentMarking/NativeOrdinalRepeatedCapBlockTargets.lean`,
the strict lex construction, and already checked two-way reflection
(receipt `1795449387846238355-83`). It supports the lower-witness side of the
printed height question in `sections/ordinals.tex`, not its rank, cofinality,
or upper-bound interpretation. No printed statement is discharged.

* **Native-side root:** `NativeOrdinalRepeatedCapImageRelIsoProof` has
  `exact_ActualBlockImageRelIso` for the literal range of the original
  `blockImage` with the relation given by actual `NativeBelow` of subtype
  terms. It exposes the literal forward map, uses checked injectivity and
  two-way actual reflection, and `exact_ActualBlockImageWellOrder` transports
  the well-order along the inverse embedding. Both quantify over the original
  payload (hence include original zero). There are no ordinal-library imports.
* **Arithmetic-side root:** `NatPairLexOrdinalTypeProof` contains
  `exact_NatPairLexOrdinalType` for the same literal `Prod.Lex` relation on
  natural pairs and `exact_OrdinalTypeOfNatPairLexIso` transporting it to any
  supplied well-order via a genuine Mathlib `RelIso`. It is independent of
  every native or local Lean declaration. Its only direct import is pinned
  `Mathlib.SetTheory.Ordinal.Arithmetic`; it uses `Ordinal.type_prod_lex`,
  `Ordinal.type_nat_lt`, and `RelIso.ordinalType_congr`. It does not import
  `Exponential` or `Rank`.
* Both lex domains unfold to the same literal `Prod.Lex` natural strict order.
  The leaves are intentionally **not** combined in a new Lean specialization.
  The original combined concrete native ordinal-type root
  `NativeOrdinalRepeatedCapImageOrderTypeProof` remains unchanged and
  unverified: exact receipt `1795449389814501987-93` stopped at the 1536 MiB
  RSS check (exit 77, no proof diagnostic). Moving the generic result behind
  an import would still load the full Arithmetic and native closures.
  This recut does not invoke a new combined root or assert that it passed.

The static cache counts include multi-modifier imports (e.g. public meta),
exclude comments, and count Mathlib artifacts separately from Lean/core and
other pinned packages. They are a static availability check, not native
checks of these new modules.
