# Genuine ordinal endpoint programs: plan

Pinned Mathlib SetTheory/Ordinal/Notation.lean supplies actual ONote.addAux/add/sub, add/sub NF preservation and repr_add/repr_sub, with NONote operations. These are genuine ordinary ordinal operations, not formula syntax. Executability alone does not prove the required Computable/Primrec statements.

Propose explicit raw-code tables over paired input index n=Nat.pair a b. At step n, decode only immediate numeric constructor fields of a,b. For addition, recurse through the first notation's tail at index pair(tail(a),b), then implement addAux from the recursive result's immediate fields and checked rawComparisonCode on exponent fields. For subtraction, compare original exponents/coefficients; only equal coefficients recurse at pair(tail(a),tail(b)). Those indices are strictly smaller by raw-child decrease and Nat.pair_lt_pair_left/right. Table length and all previous-entry correctness establish literal output=rawNoteEncode(rawNoteDecode a + or - rawNoteDecode b), including malformed/non-normal inputs, not just semantic equivalence.

Freeze all-input joint Primrec for the actual programs, literal syntactic agreement with installed Mathlib operations, and normal-input output normality plus actual repr ordinary addition/subtraction. The latter follows only after the program equality and Mathlib NF/repr theorems are checked in the closure.

Use these to compute deltaQ=lambdaQ-muQ, kappa=muP+deltaQ, and partner codes H/Qtilde. No normal representative choice or supplied output code is the algorithm. Primitive recursion on finite tables is total on all raw codes. Full inverse threshold still requires complete case/translation/output-offset assembly afterward.
