# Paper 17: actual typed row availability, proper-shape rejection, and literal signed/mixed clauses

Printed source: `arithmetic.tex`, `thm:arithmetic`, the real source matrix
feeding high order/residue normalization after proper source checks.

- The actual `valueAt` witness and the actual `ReadState` preserve one read
  per literal weighted occurrence and exact original signed sum/constant,
  in the same order including duplicate and zero-weight occurrences.
- An admitted live original row entails all its actual operand shapes and
  test admission (in particular positive modulus). A clause with a
  malformed interval or unadmitted test has no successful original
  snapshot under either polarity. The finite filter removes that whole
  impossible clause without manufacturing test=false or a numeric value.
- Compile signed comparisons from the same original constant/tape through
  the checked proper short-count cleanup only. Even if signed cancellation
  or cleanup erases occurrence syntax later, original reads remain owed;
  exact pre-cleanup `PaidReadCeiling` and actual selected-control proper
  source prove those reads. A modular row keeps its exact original tape,
  modulus and polarity. No original positive graph row changes sign.
- Clause mapping uses these exact individual equivalences at the same
  actual raw assignment. It does not yet compute or prove the whole
  literal branch high-side ceiling, rank replay, projected residual
  recursion, raw effectivity, or full arithmetic theorem.
