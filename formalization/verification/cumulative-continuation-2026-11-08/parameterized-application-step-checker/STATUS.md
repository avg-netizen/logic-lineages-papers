# Accepted parameterized original application-step checker

Four exact supporting targets passed on the unchanged frozen specifications:

- Raw-list front-cons commutation for an arbitrary binary transition at one symbolic parameter.
- Exact peeling of the original application-lifted raw state to its original state.
- Full-output internal equivalence of the same concrete checker on original and application-lifted triples.
- All-input calibration of that checker to the original `NumberedNumericStep.numericStepTest` at every calibrated parameter slice.

The program keeps the original raw edge state, application/step-lift constructors, path code and list parser. The parameter stays separate throughout the actual `listRec` at two parameters. Internal proofs admit arbitrary arithmetic bodies, assumption lists, symbolic inputs, outputs and parameters. The only local assumptions are the explicitly frozen constructor, outer-tag and endpoint graph premises. External calibration includes malformed and rejected raw triples.

## Accepted gate

`InternalParameterizedApplicationStepCheckerStatementChecks` passed with four exact aliases: `front_cons_exact`, `transition_exact`, `checker_exact`, and `calibration_exact`. Their actual axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`.

Final receipt: `build-reports/1794179832957649719-2.json`.
Earlier successful source-matched helper modules are recorded in receipts `1794179748126652173-2`, `1794179794982891368-2`, and `1794179814840011292-2`. These records together cover all 13 proof/check modules of this packet. Definitions and Targets passed their earlier preflight in `1794178997661209954-2`.

The serialized profile remained 2,048 MiB heap, 1,536 MiB process-tree RSS, 2,048 MiB minimum free memory and one thread. Peak successful observed process-tree RSS across this packet's accepted helper and final modules was 1,209,944 KiB. Frozen Definitions, Targets and all named supplier hashes still match exactly. The focused gate verifies this supporting packet; the numbered register is unchanged.

## Remaining consumer

The checked local step equation and all-input calibration now supply the concrete parameterized step core. Uniform leaf selection, outer source/type guards, quotient-edge representative compatibility and the original object/context path wrapper are separate consumers. The unqualified original `CertifiedApplicationLift` still requires those consumers.
