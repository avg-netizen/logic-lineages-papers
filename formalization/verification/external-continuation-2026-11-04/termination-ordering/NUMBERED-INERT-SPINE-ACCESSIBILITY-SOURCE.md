# Conditional actual quotient accessibility for inert spines

Draft requested 2026-11-04 12:22 UTC; exact review, comparator and prospective freeze required before proof. Verification-only/no export.

Paper06 lines583–589 discusses variable and bottom computability. The two targets here establish only actual trace/rank and conditional quotient accessibility prerequisites. They use the already proved literal InertSpine and inertRank, allowing variable→bottom and arbitrary application arguments.

The trace target quantifies arbitrary Symbol, arity, symbols, S, above, Gamma, actual count and packed endpoints. An actual WindowTrace of that exact count from an inert source preserves inertness and gives rank(target)+count≤rank(source). Primary links have count0 and preserve rank unconditionally. Raw steps have count1 and strictly decrease rank. Concatenation retains the exact sum. No endpoint confinement or subtype closure is needed for this syntax theorem.

The quotient target fixes Fin n/arity/symbols/S and explicitly assumes SubtypeClosed S, InUniverse q and InertSpine q. It concludes Acc of the successor-first relation (successor,source)↦PositivePath(QuotientEdge ...) source successor at the actual canonical representative of q. Precedence above is arbitrary.

For every numeric successor, accepted actualTypedSuccessorWitness supplies a confined term of the same type, its exact representative equality, and a positive counted typed trace. Accepted typedPresentation converts that trace to the packed trace. The first target gives strict rank decrease, enabling strong induction on the rank of the actual source representative witness. There is no assumed injectivity of canonical representatives and no assumed global rank on arbitrary numeric codes. The same argument covers both variable-headed and bottom-headed spines.

No global well-foundedness, arbitrary term accessibility, precedence assumption, original-order transitivity, encoded scalar calibration, semantic least-set membership, computability, ID1 or register promotion is asserted.
