# Actual free-variable containment through comparison

Source paper06 `lem:fv`, lines368–380, for every original weak comparison, with simultaneous strictness through marking. The final targets quantify arbitrary marked packed endpoints at any scope, not only ordinary source/target inputs. They conclude membership containment of literal free-variable traversals, not containment of typeSupport or an artificial comparison label. No stronger occurrence-multiplicity injection is asserted.

`markedOccurrences` traverses variables, removes exactly the current binder with existing `dropBound`, concatenates every ordinary base argument, and concatenates every marked base and extra argument. It preserves order and duplicates in its representation. The target ordinary calibration is exact equality with the existing actual `SourceFreeOccurrences.freeOccurrences` on ordinary embedding.

`Supported` is the independent structural predicate that each actual variable is allowed: lambda extends allowance by the bound variable, every functional base/extra is checked. Its target calibration proves equivalence to universal membership in the literal occurrence traversal. No comparison relation is defined from this predicate and no conclusion is packaged as a premise.

The original Apply provenance target is an actual syntactic substitution/argument supplier. It retains the original-spine `applyOriginalWith`, a successful actual result and the literal source/environment/argument support premises. In Select these premises must be discharged from the selected source argument and the whole-source self copies. FAbs must weaken existing inputs with the original fresh bound variable allowed, then remove exactly that binder from the target. All actual mutual relations, including occurrence-based strict multiset matching, remain unchanged.

Full source adoption requires all five targets and full helper dependency closure. No well-foundedness, substitution stability of comparisons, finite-lattice adequacy or other numbered statement follows from this lemma alone.
