# Supporting literal arbitrary-policy abstraction

Current18's arbitrary computable admissible policy is retained. The concrete
semantic comparator is actual `AdmissibleAssignment.abstraction p h`; no default
or all-left policy substitution, source normalization or value-only equality.

PartialsCalibration requires exact ordered Option collection of every m+1
source coordinate using the same p. FactorCalibration is literal source-size
calibration for 2^(level+1) times the sum of ordinalPartialSize, not a bound or
normalized expression size. LiteralCalibration includes every failure and every
successful coordinate of the max(level+1,m)-level result.

Coordinate0 uses actual policy scalarRepeat with the exact factor, including
count-zero behavior on raw inputs. Positive low coordinates expand the actual
positiveAbstraction shape at index m, hence arity m+1, in original partial-vector
order. High delta coordinates retain the literal original headClosure; every
coordinate below m+1 then adds its original headClosure as a separate plain add.
No retained copy, operand or zero-valued subtree is removed or reassociated.
On actual typed vectors all high-index accesses must be proved in range, not
justified by the numeric getD-zero fallback.

Programs explicitly demands joint all-input computation of partial collection,
coordinate expansion, result traversal and full abstraction with ONLY a
Computable policy selector. The source-size factor itself remains genuinely PR.
Malformed raw lists/codes have defined total Option behavior, but no false typed
success promise is made for them. The checked PolicyPartial and finite Computable
fold suppliers may be reused only with actual literal correspondence.

This pays abstraction only. Full original-term assignment recursion and its
arbitrary-policy equality/domain frontend remain separate. No numbered source
corollary is claimed by this supporting compiler packet.
