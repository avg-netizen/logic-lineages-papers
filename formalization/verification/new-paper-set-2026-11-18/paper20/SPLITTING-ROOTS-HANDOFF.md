# SplittingRoots7 native/evidence handoff

The seven exact supporting aliases passed unchanged standard native limits in
receipt `1794983650362513411-2.json`. The native process is reaped and queue
released. Recursive evidence reconciles nine local modules, all four frozen
pins and all seven standard-only alias audits. Maximum closure RSS was
1,334,080 KiB. Independent final review has been requested; acceptance awaits it.

The first attempt failed because the opaque `Root` definition did not expose
its finite-subtype instance to inference. Failed source/receipt are preserved
under `splitting-roots-failures/01`. Proof-only repair unfolds Root when proving
its finiteness and installs that proved instance locally for the permutation.
No target, definition, import pin, checker or resource cap was changed.

Actual results: the literal source polynomial's actual splitting field is
finite, its complete mapped polynomial splits, its complete distinct root set
has exact membership and no zero root, Frobenius fixes the polynomial and
permutes that entire root set, and the fixed field consists exactly and uniquely
of embedded F2 elements. This is mathematical existence, not an executable field
construction/root enumeration/conversion or a complete profile theorem.
