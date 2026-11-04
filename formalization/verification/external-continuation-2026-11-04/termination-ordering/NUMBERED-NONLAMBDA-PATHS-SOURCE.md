# Exact first edge and residual path

Draft for exact review. Verification only; no export.

Paper 06, lines 583–589: non-lambda application reasoning. This component states the precise positive-path consequence of the already accepted one-H-edge decomposition, not a full-path application endpoint classification.

ActualPositiveFirstEdge uses the literal PositivePath constructors with H(source, successor). It is an iff for arbitrary Nat relations with a nonempty first H edge and either equality at that endpoint or a remaining positive path.

ActualNonLambdaApplicationPath uses actual QuotientEdge, confined f and a, explicit SubtypeClosed, and isLambda f=false. Its first application edge is bottom or app g a, with g confined at the exact original arrow type and H(rep f,rep g). The argument is restored by actual primary congruence, not by a positive argument step. If the first endpoint is bottom, accepted actualBottomPositiveTerminal excludes any residual path; tau membership is derived from confined application and subtype closure. Otherwise the endpoint may be app g a or any positive descendant thereof. In particular g can be a lambda and later beta reduction need not leave an application.

No neutral expansion, accessibility, computability, original-order transitivity, ID1, or global well-foundedness claim. All prior accepted bytes remain unchanged.
