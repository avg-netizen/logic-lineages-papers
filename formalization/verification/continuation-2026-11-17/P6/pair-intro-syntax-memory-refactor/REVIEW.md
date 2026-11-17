# Independent source review

Approved exact proposed pins for native checking only. Verified hashes of preserved original and both new sources. Compared full source diff: only new helper import and two implementation bodies (atRawSubst, matrixWitness) change. All six theorem headers and the four other proof blocks are byte-identical. Original definitions remain untouched.

The generic five-slot matrix expands the actual original fields/result in the same conjunction order: roots(out,raw,param), member(1,raw,targetChild), pair(node,param,targetChild), implying member(1,out,node). Slots param/out/node/sourceChild/targetChild remain 0/1/2/3/4, including unused sourceChild. Substitution and witness use original graph2 substitution, allBlock substitution and lifted/witness embeddings; no semantic result is assumed. Caller supplies exactly pairRoots, original contains and InternalPairing.pairing.

This is a proof-only abstraction boundary, not a new target or weakened theorem. No native job was run in review, and no memory benefit, endpoint acceptance or substantive contribution is claimed.
