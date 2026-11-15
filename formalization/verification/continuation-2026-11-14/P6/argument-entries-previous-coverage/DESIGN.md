# Dependency coverage in an actual previous table: exact1

The original stage reads all dependency answers from the previous association
graph. Paid stage domain alone is not enough: a current node's dependencies
must belong to that previous graph's frontier. This theorem pays the link.

Actual current frontier at depth d, actual node membership, actual D output,
and actual child membership imply child membership at depth d+1 using the
checked original bindList successor. Its frontier output is internally bound,
not an added public premise. The original graph table at index+1 uses that
same frontier when actual subtract(index,seed)=d+1. Apply actual table domain.

The exact subtraction graph is retained explicitly: its input order is
[index,seed], output seed-index. No unproved identity between arbitrary
indices/depths is assumed. Source rank, fixed seed/parameter, duplicates and
first-match order stay unchanged. Inner None cached as zero is present outer
Some0, not missing lookup0.

This proves presence, NOT correct cached value or equality to independently
computed child extraction. Those global coherence obligations remain open.
Frozen for review/preflight; no proof/compiler launched.
