# Literal dependency frontier, exact5
Mathlib/Computability/Primrec/List.lean nat_omega_rec' bindList, lines 312–313:
depth zero is [seed]; successor is previous.flatMap dependencies. Flatten uses the
actual append AST in a right fold, so original list order and duplicate entries
are retained. The bindList AST is ordinary primitive recursion on depth.

NativeFlatten/NativeBindList explicitly require D's calibration. OriginalRankExhaustion
uses the ORIGINAL Code-pair dependencies and source codeNumber rank (not pair rank):
every depth-k node has source rank + k <= original source rank, hence the frontier
at source rank+1 is empty. This native original rank theorem is not reflected into
arithmetic for the selected opaque D.
InternalFlattenCons and InternalBindSuccessor are actual arithmetic graph laws
for these ASTs. The latter is a two-way successor equation conditional on the actual
previous graph, not a semantic soundness shortcut.

The following stages still remain: original rank subtraction m(seed)-i, graph recursion
using each literal frontier and the same prior association graph, coverage and
coherence connecting lookup answers to recursive calls, actual dependency and
headMove/layer supplier installation. This packet does not change the current full
tuple, claim installed recursive E, or replace nat_omega_rec with dense row memoization.
