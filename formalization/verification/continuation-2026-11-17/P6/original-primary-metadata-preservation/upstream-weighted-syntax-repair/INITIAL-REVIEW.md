# Independent WeightedAgreement generic syntax review

Approved at REVIEWED-PINS.json hashes. All eight original headers/attributes and five unchanged full declarations match the original snapshot exactly. Only fieldsSubst, atRawSubst and matrixWitness proof bodies now delegate to generic syntax lemmas. Original WeightedAgreementDefinitions is byte-identical to HEAD.

The generic program parameter denotes the entire fold program, not the element-weight program. Every old wrapper correctly instantiates it with Fold.weighted weight. The generic fields retain the original universal count agreement conjunct and the two graph1 observations, in the same order. The generic Fin 3 matrix retains [right,ls,rs], the lifted left source, and equality ls=rs; allSchema uses the identical allBlock. Instantiation therefore exactly recovers the original fields/matrix/AtRaw, with no weakened hypothesis or changed result.

The three generic lemmas prove only capture-free substitution and witness identities, using agreementSubst plus the existing program/tuple/binder substitution laws. They do not claim arbitrary program outputs agree from count agreement. No axiom, preservation oracle, native reflection or semantic assumption is added. Original public declaration names and namespace are retained through the public generic import.

No source edits or compiler runs were performed by the reviewer. Native and recursive evidence at the unchanged resource limits remain required. This proof organization is not a substantive contribution.
