# Paper 16: exact finite cover of the actual primary class (supporting)

Scope: the source `ordinals.tex` “One finite arithmetic universe” and its
paragraph “Quotient by the congruence” (lines 13–28 and 69–76). This packet
proves an executable finite *cover* of each actual class, not that the
cover contains only class members. It does not decide membership, compute a
least representative, prove arithmetic of certificates, or assert ID1
accessibility. No previously accepted source or proof is changed.

- **Actual syntax and alphabet.** The exact existing `NTerm` and `NArgs`
  from the numerical rules are used, not a generic auxiliary syntax:
  globally typed free pairs use their actual type and Nat index, bound
  variables use actual de Bruijn indices, lambda uses its actual binder type,
  bottom keeps its type, ordinary/native/ranked/typed-application heads
  use their original literal declaration, numbered heads keep the original
  head, current type, finite label, actual base and ordered extra lists,
  and auxiliary applications remain a separate constructor with both
  actual annotations. `admittedHeads S K` is packet442's exact executable
  head enumeration for this signature and complete original declarations
  in this same K. No ambient context changes K or introduces an artificial
  bound on free indices for the universe as a whole.
- **Original congruence and bounds.** `PrimaryBounds` is over actual
  `Primary` and mutually defined `OrderedPrimary`, not a new relation.
  Names/indices/labels are the actual numerals in the syntax and distinct
  from ranked-head identifiers. The literal structural measure counts
  each term constructor and nonempty argument cell. The two root
  exchanges only replace admitted equivalent heads and permute the same
  literal typed base items, maintaining size and maximum numeric atom.
  Numbered exchange retains label/current type/extras. The two application
  positions, lambda, ordered args and base/extra congruence lift equality
  of the same bounds. Reflexivity/symmetry/transitivity retain it.
- **Finite constructor grammar.** For each finite fixed head list and K,
  an explicit finite natural recursion takes the preceding term/args lists
  as its only recursive inputs. Its numerical alphabet is exactly
  `List.range (m + 1)`; the local bound m comes from the individual source
  and does not restrict the global carrier. Every actual term with its
  literal typed window guard and both measured bounds is covered. The
  corresponding argument case requires actual per-argument type-support
  and head validity, not a weaker invented type of arguments. The
  constructor grammar can contain irrelevant candidates and duplicates.
- **Complete cover, not exact membership.** `FinitePrimaryClassCover`
  needs only the manuscript's fixed subtype-closed K, the initial
  actual typed/admitted term, and the true actual equivalence proof in
  that K. Same C and type on both vertices, with no target admission or
  bound hypothesis. Actual primary locality already established in
  packets431/439 will propagate target admission; exact equality of both
  measures places it in the source-generated finite list. Distinguished
  from characterization of the exact class, that may later restrict the
  list by an independently proved executable relation.

Source correspondences: `foundations.tex` 3–18, 26–54, 57–90;
`ordinals.tex` 13–28 (window and all-context carrier), 69–76 (primary
congruence/effectivity). Existing Lean inputs are frozen below with both
new definition/comparator files and the provenance of packet442's head
admission proof. Original ordered/canonical sources remain unchanged.
