# Direct homogeneous-prefix source decision

The actual source syntax is parsed without altering its original names. One
parser strips leading existsNat constructors; the other strips the literal
negative/existsNat/negative universal-binder encoding. Exact reconstruction
requires folding the extracted names back to reproduce the original AST.

The quantifier-free body test selects these two homogeneous-prefix fragments,
including arbitrary nested Phi terms and Boolean matrix polarity. Actual source
parameter decisions handle the extracted blocks. The six targets require precise
rejection, full original-formula truth, literal numeric parser calibration,
primitive recursion and correctness on every raw source code through the codec.
Mixed alternating prefixes, internal quantified bodies, QE and full BASE remain
outside the claimed fragment.
