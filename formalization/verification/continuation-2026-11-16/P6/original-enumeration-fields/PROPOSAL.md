# Independent original Fields AST and comparator

Proposed only; review/freeze and native preflight are pending. No candidate
proof has been authored. The namespace is Continuation20261116.OriginalEnumerationFields.

## Executable semantics

The public argument order is [raw code, variable bound, types, original encoded
heads, label bound, tuple bound]. The fresh selected recursion key is pair(raw,
variableBound); rank is the raw coordinate. Dependency retains source child
order and increments the bound only on a lambda first child. Constant parameters
pack the four actual remaining inputs. This graph, layer and values are new:
no depth/bounds/enumeration cache is reused.

The layer follows the eight original Fields cases. The checked original Code
validity guard rejects malformed metadata/head codes/nil payloads. Child answers
are booleans, with their original order preserved. Type membership uses actual
list contains. Heads are converted from their original Encodable entries before
raw-head membership; duplicates remain and invalid original head encodings
retain the existing conversion-to-zero behavior on arbitrary raw lists.
Numbered nodes use literal label, head, type and type-list selectors. Their
checks include source label<=bound, real list length<=tupleBound and a list
fold checking every type entry. The fresh layer adds one successor for Some.

## Exact target coverage

The thirteen targets are native original Fields equivalence on every typed
source input; universal raw boolean range; raw Code-decode-failure rejection;
internal boolean range; internal malformed rejection; and eight internal
constructor equations. No internal equation assumes native truth or externally
supplied child values. Child acceptance occurs as the recursively meaningful
object-language formula, not an extra premise. All raw internal constructor
clauses retain explicit actual-Code validity, preventing malformed data from
masquerading as typed source syntax.

Lambda acceptance uses variableBound+1; other recursive cases preserve it.
Original encoded-head membership/conversion and original type-list length and
all-members conditions are explicit bounded/universal formulas, not opaque
membership in an invented candidate list. Original source Fields is never
defined to mean enumeration membership.

## Remaining work after review

First prove fresh keyed raw descent and native source recursion. Then prove
original internal parameter/frame and own-key cache coherence for the new rank
and dependency, followed by the literal internal Fields equations. The eventual
original enumeration membership iff Fields and depth<=fuel needs its own
internal induction and is not part of this supplier packet.
