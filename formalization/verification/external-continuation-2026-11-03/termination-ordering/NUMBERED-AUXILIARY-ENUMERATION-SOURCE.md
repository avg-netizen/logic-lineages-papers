# Executable finite auxiliary-code enumeration and actual class coverage

The ordinary executable enumerator lists all literal structural codes whose
fields lie in the displayed finite lists, whose finite labels and extra-type
list lengths satisfy the displayed bounds, and whose constructor depth fits
the fuel. Variable indices use the actual ambient-context length; only the
lambda branch increments it. Type lists retain duplicates and order. Exact
membership in this structural overapproximation is proved, not assumed.

Actual typed syntax coverage additionally derives every field restriction
from InUniverse, the actual finite-label bound and subtype closure. The proof
must derive a depth bound of twice the original auxiliary node size and bound
extra-list lengths by that same size; these are not source restrictions.
The actual fixed-window primary class is then covered by the source-dependent
finite list classCodes using genuine type, size, label and universe invariants.

The list may include ill-typed or inequivalent codes. It is not an exact class
enumeration or a decision procedure for Primary. Exact class filtering,
numeric least-code representatives and the quotient relation remain pending.
No source comparison semantics or checked obstruction is changed.
