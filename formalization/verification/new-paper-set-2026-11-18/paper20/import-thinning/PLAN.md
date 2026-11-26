# Proposed import thinning: not applied

The original files are copied byte-for-byte here. IMPACT-INVENTORY.json records the original digit-definition hash and repository HEAD provenance; PROPOSED-NOT-APPLIED.patch is a three-file import-only candidate, not an executed patch.

## Identifier accounting

PolynomialDigitDefinitions declares just `actualBinaryPolynomialDigit`: Field, Polynomial, Finset.range/sum, Polynomial.monomial/coeff/natDegree, Nat.bit. It never references PowerSeries, actualBinarySeriesDigit, actualBinarySeriesWord or actualPolynomialSeriesQuotient. The proposed Degree.Operations import supplies the polynomial algebra vocabulary and finite sums; Nat.bit is core. This is source accounting, not yet an elaboration check.

There are exactly three direct local importers. CartierPolynomialDefinitions needs only the polynomial digit and PerfectRing/Frobenius. PolynomialDigitTargets explicitly mentions PowerSeries and actualBinarySeriesDigit. BinaryQuotientTargets explicitly mentions these and actualPolynomialSeriesQuotient. Thus the latter two must gain direct SeriesContinuationDefinitions imports when the definition leaf loses that dependency. Removing only the first import is NOT an acceptable patch.

## Impact and limitation

The import graph has 333 transitive local descendants of the definition module, listed in IMPACT-INVENTORY.json. LEGACY-REGISTER-REFERENCES.json lists the exact legacy register module references in that set, including unrelated major accepted comparison/decision gates. Every affected checked input key is stale after the refactor even though declaration bodies are identical. Historical acceptance remains historical; current-source validity requires recompiling/reconciling affected accepted closures. Existing new-paper accepted closures must also be tested against the full reverse set before claiming unaffectedness.

Crucially this three-file patch ONLY thins the definition branch. CartierPolynomialProof imports PolynomialDigitProof, which imports PolynomialDigitTargets and therefore still pulls the series branch. The patch may get LocalTargets under the cap but is NOT evidence that the L0 proof closure fits. A complete proof-path thinning would need a separate pure coefficient supplier (or moving the existing actualBinaryPolynomialDigitCoefficient theorem to a pure module and importing it from legacy PolynomialDigitProof), and changing CartierPolynomialProof's dependency accordingly. That is a larger independently reviewed refactor, not hidden in this proposal. No cap increase or same-input retry is justified by the current information.

## Legacy-preserving alternative

A new current-paper thin stack with DISTINCT declaration names is mathematically possible: literal polynomial selector, sqrt polynomial selector, canonical rational digits/C, and new proofs independent of series. A bridge could compare the new definitions to actualBinaryPolynomialDigit/actualRationalSquareRootDigit/actualDifferentialCartier by definitional/extensional equality. The bridge must import old CartierRationalDefinitions (which did pass), but need not import old CartierLocalTargets or old proofs. Actual RatFunc.X/C still require AsPolynomial. Its memory behavior is untested. Any bridge to the existing frozen actual targets must still be compiled; an independent thin theorem without this bridge is not the requested actual-control result. Duplicating definitions under the same names is forbidden. Frozen target import changes need explicit superseding pins/review even when proposition text is unchanged.

This alternative avoids invalidating 333 legacy descendants, but entails rebuilding substantial rational square-decomposition/uniqueness/local suppliers and duplicating maintenance. It is not a cheap alias or a guaranteed cap remedy. A still smaller first experiment could replace the NEW L0Targets import of CartierLocalTargets by exact necessary legacy definitions plus AsPolynomial, with a reviewed superseding freeze; however its proof import of CartierLocalProof still restores the broad dependency, so this alone cannot finish the candidate.

## Recommendation

Do not apply the legacy three-file patch merely to advance one blocked packet. First obtain independent review of this impact accounting and select explicitly either (a) a controlled legacy proof/definition import refactor plus accepted-closure revalidation, or (b) an isolated new thin stack with actual-definition bridge and revised reviewed target imports. Preserve current resource stop and mark L0 unaccepted while choosing. This packet performs no source edits or compiler runs.
