# Paper 17 signed residues across the used raw ranks

Every occurrence at the same original raw input uses one residue modulo `2m`. The all-large calculation pays a common cutoff for the current operands. This packet covers an arbitrary list of signed coordinate, ordinary-value, and count operands whose original ranks can differ. [Arithmetic, lines 231–247 and 255–263](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex#L231)

The numeric program finds the distinct used ranks by processing the operand list from the right. Its association-list evaluator reads the same residue for every occurrence at a given rank. It preserves all original signed coefficients and reads the operand list in order. The exact code theorem compares with the original operand types on canonical encodings. [Frozen comparator](../../LogicLineages/PermittedControl/MixedRankResidueTargets.lean) · [Code proof](../../LogicLineages/PermittedControl/MixedRankResidueCodeProof.lean) · [Support proof](../../LogicLineages/PermittedControl/MixedRankResidueSupportProof.lean)

The actual theorem uses the single original raw valuation at all ranks. For each term it pays the individual original tail from the common encoded maximum at that rank. The checked same-rank theorem supplies the actual term read and its signed contribution. These give the whole signed congruence and one ordered read for every original occurrence. [Actual proof](../../LogicLineages/PermittedControl/MixedRankResidueSemanticProof.lean) · [Author pins](PAPER17-MIXED-RANK-RESIDUE-AUTHOR-MANIFEST.json)

The next source step emits the full Presburger disjunction for this single row. Optional halves and the original full matrix normalization and projection remain open.
