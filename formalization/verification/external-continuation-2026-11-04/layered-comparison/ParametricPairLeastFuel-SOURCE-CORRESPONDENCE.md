# Total computable least-success worklist fuel

This supporting bound clarifies, but does not certify the stronger fixed-iteration wording in paper09 hardness.tex lines 316–319. Fuel counts iterations of the existing explicit worklist transition, not iterations of G and not machine runtime cost.

leastFuel is the least fuel whose actual indexedEvaluate result is some value. A syntactic fallback zero is included for the no-success branch, but ExactLeastFuel proves that branch is unreachable for every H and pair by accepted eventual success. It gives the actual pair-collapse value at the bound, None at every earlier fuel and minimality among all successful fuels.

UniformComputable assumes jointly Computable H on (index,input), not computability of isolated sections. It uses effective least search with the proved total-success premise. FixedGammaFuel applies this to each fixed b and the accepted actual gamma control, calibrating back to the original worklist evaluator.

This is a total computable, input-dependent effective bound. It is not a primitive-recursive bound, closed-form majorant, input-independent iteration count, bounded-cost implementation, full source-evaluator fuel bound or proof of the manuscript's stronger fixed finite iteration reading. No manuscript/register/export changes.
