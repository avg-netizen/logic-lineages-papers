# Actual blank-table bounded simulation (three exact targets)

Paper09 `hardness.tex` lines233–235 asks for a primitive-recursive bounded halting test for an effective enumeration of blank-input programs. This component chooses the existing numerical finite-alphabet TM0 table enumeration explicitly. A natural index decodes a finite transition table (including its initial state and alphabet width); invalid numerical encodings use the existing default table. Every Table has its encoded index. The blank input is the empty list, hence a blank tape.

1. EffectiveEnumeration proves primitive recursion of decoding and the test, and exact decoding on every encoded table.
2. ExactTransitionClock identifies H(e,t) with a finite raw run of at most t transitions ending at a state with no transition. The accepted exactSingleStep transports each raw transition to the actual TM0 machine. Existing bounded simulation counts a terminal halt observation, so the literal test uses fuel t+1. At t=0 an already halted initial machine is detected. No evaln stage is identified with a tape step.
3. MonotoneHalting proves monotonicity and equivalence between eventual success and the domain of the actual blank-tape TM0 evaluation. All terminal outputs count, including nonbinary output.

Reuse: PredictionFiniteAlphabetProof effectiveDecoding, effectiveBoundedSimulation, exactBoundedSimulation, exactSingleStep and exactInitialTape; PredictionFiniteAlphabetEvaluation boundedEvaluation. No accepted source is changed.

This supplies only an explicit operational choice of bounded H. The manuscript does not select a particular machine syntax. Undecidability/computational completeness of this precise enumeration remains a separate obligation, as do the gamma parity theorem for this H and the full source hardness reduction. The earlier Code/evaln-stage parity result is not transported by claiming equality of clocks or controls.
