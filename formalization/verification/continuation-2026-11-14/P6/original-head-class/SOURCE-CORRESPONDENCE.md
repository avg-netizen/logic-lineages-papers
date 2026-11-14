# Concrete original head-equivalence guard (exact3)

NumberedExchangeCode.headMove contains headEquivalent of the decoded source and target heads. NumberedExchangeGuardsPrimrecProof.headClassNumber uses 0 for zero/succ/cases/recursor, 1 for application, and 2+symbol.val for ranked. Its headClassNumberCalibration establishes exact agreement with RecursiveComparison.headEquivalent. This packet implements that exact raw-head classifier with original headNumber tags/payloads, then actual equalityTest.

NativeClassAndEquivalence covers all six actual heads and all pairs, including unequal ranked symbols and parameter-varying builtins. InternalTagFactor handles actual raw pairing evidence for every supported tag, independent of semantic validity. InternalEquivalence is actual program-graph iff internal class equality with actual class-output graph premises, not native reflection. Raw malformed inputs have deterministic AST outputs but no claimed semantic head interpretation.

This pays one genuine headMove component, not headMove as a whole. Original HeadInWindow, target sourceHeads enumeration membership, argumentEntries malformed-spine handling and argument permutation remain unpaid internally. No full selected E/recursive coherence/source-stability claim or tuple mutation.
