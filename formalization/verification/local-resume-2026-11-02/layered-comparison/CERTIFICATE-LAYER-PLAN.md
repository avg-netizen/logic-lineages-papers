# Next exact source08 certificate layer

This is an implementation plan, not an accepted theorem or a substitute for
the outstanding complete numeric row-code gate.

Use the original A_r grammar from paper08 lines831–908. A_0 has numeral,
positive raw variable, addition and the ACTUAL Phi function. At a positive
level an expression is one nonnegative constant plus a finite list of
positive multiples of calls to the SAME fixed head for that level. Empty
lists and zero constants remain valid. A finite head list supplies the whole
level certificate; no open remainder is admitted at positive common-head
levels. Different levels may use arbitrary different fixed nonzero limits.

For E,F at positive level, form the actual signed row by concatenating left
positive and right negative coefficients and taking the signed constant
difference. The input for each occurrence is N(head)+B_i evaluated using
ONE original raw valuation. The exact row compiler applies to this shared
input function, including equal/dependent subexpressions.

Translate the emitted guards as follows:

- Equality/order of N+B_i and N+B_j is equality/order of the preceding-level
  expressions B_i,B_j.
- A lower bound c<=N+B_i is constant true when c<=N, and otherwise the
  complement of the preceding-level comparison B_i<c-N.
- Closed equality guards are thereby translated with their complete whole
  argument, never by folding an open raw value.
- Every atomic comparison becomes a recursive child at STRICTLY lower
  certificate level, using the SAME original raw variables. Constant
  comparison expressions are legal in every preceding A_r (empty head sum).
  No new independent parameter is introduced for a subexpression value.

The finite Boolean guard code can be traversed to list all atomic child
comparisons. Its assembler preserves negation/conjunction/disjunction while
substituting the actual returned BASE-language formula codes. The checked
row code support bounds make every original occurrence lookup legal on valid
certificates; invalid numeric code inputs can use total defaults without
claiming source correctness on them.

Use the actual finite-graph computability theorem with outer natural measure
the certificate level. Boolean assembly is finite syntax processing, not a
same-level recursive source call. Inner small-exception recursion has already
used occurrence-count fuel. Thus the source lexicographic termination is
implemented by two genuine bounded-depth finite graphs, without needing an
unproved lexicographic recursion oracle.

The final translation must have literal BASE syntax for0,1,+,<,Phi, exact
truth at EVERY positive original valuation and no fresh raw index; all-code
computability must concern actual input/output syntax codes. Snyatkov's
quantified arithmetic decision theorem remains separate and pending. A full
compiler alone does not promote the ENTIRE original thm:common.
