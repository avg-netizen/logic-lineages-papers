# Accepted — original raw neutral step inversion

**Ten exact supporting targets pass in 22 new Lean modules.** The continuation
extends `2f690cdf8ffc2788b3711e3a788a412df3761cfb` on
`formalization/cumulative-continuation-2026-11-09`. The inherited original
guard/checker inversion is reused unchanged.

The final result is internal inversion of an accepted original raw neutral
step: under its original active-window, neutral-tag and outer-type graph
premises, the target is either literal same-type bottom or a recovered
application whose function child is accepted by the SAME full step checker.
The original certificate, raw argument, endpoint and separate parameter remain.
The zero-guard leaf branch is now discharged by a proved concrete leaf law.

| Exact target | Checked result |
| --- | --- |
| `ActualTypedNeutralCertificateInversion` | An accepted supplied typed certificate at a non-lambda application is a bottom case or the literal lift of an accepted child certificate. |
| `ActualNumericNeutralCertificateInversion` | The same inversion retains the actual original numeric certificate, including its path suffix, replacement and root selector. |
| `ActualValidatorApplicationInversion` | Acceptance of the actual application validity fold implies acceptance of its codomain node and both original child folds. |
| `ActualSourceApplicationInversion` | The same selected source validator accepts both application children, with the original child type tags retained. |
| `ActualSelectedStepElimination` | Original selected-step inversion yields the unchanged zero-guard leaf or an actual full accepted child step, including target child source-validity. |
| `ActualOriginalNeutralLeafRefinementEquality` | The concrete neutral leaf refinement preserves the entire original numeric output on every raw input. |
| `ActualOriginalNeutralLeafInternalCases` | The refined AST internally retains the old leaf as a factor and forces literal same-type bottom in the active neutral zero-guard case. |
| `ActualOriginalNeutralLeafGlobalSelection` | One calibrated original input tuple precedes all windows and supplies the complete original Package together with the neutral leaf law. |
| `ActualOriginalNeutralVariableGlobalSelection` | One final tuple retains the neutral law, complete Package, original variable certificate-bottom law and variable-I at every finite type. |
| `ActualOriginalNeutralStepElimination` | The final tuple's actual raw neutral step has only the literal-bottom or recovered accepted-child alternatives. |

The shared final tuple is exactly

```lean
let q := OriginalNeutralLeaf.refineInputs p
let r := OriginalVariableRepresentative.refineInputs q
```

The endpoint is unchanged by these refinements as a literal Program AST.
The variable refinement is applied once. Source, computability and lift all
come from the same `r`, chosen before every source window and ambient Gamma.

## Source boundary

This pays the raw-step part of the non-lambda application argument in paper06
`lem:id1`, around lines582–590. It does not yet transport that inversion through
the original canonical quotient representatives. Application-component and
lambda-shape reflection through the same final fold remain unpaid. Neutral
arrow computability, all-type variable C, lambda/substitution, multisets,
constructors and closed context-uniform accessibility remain pending.

The numbered register remains **171 checked, 2 inherited, 16 pending / 189**.
No numbered source statement is promoted.

## Verification

The final exact gate is
`SourceComputabilityCompletion.OriginalNeutralInversionStatementChecks`.
Its ten independent aliases and 41 defining-module proof declarations passed
actual axiom audits, using only `propext`, `Classical.choice` and `Quot.sound`.
The gate's 1,827 local import-source hashes match successful native rows;
including both preflight modules gives 1,829 matched modules. Cached accepted
supplier evidence was reused; this is not a fresh full-root or remote-CI build.

Final receipt: `build-reports/1794282369965059480-5.json`. The unchanged checker
used one worker, 2,048 MiB heap, 1,536 MiB RSS, a 2,048 MiB admission floor,
and 90 CPU/180 wall seconds per module. The peak successful new-module RSS
was 1,307,028 KiB. All 10,233 inherited mathematical Lean source files,
frozen specifications, toolchain, dependencies and checker are unchanged.
The root aggregate gains one import of the checked gate.

Failed attempts are preserved in `ATTEMPTS.json` and `failed-attempts/`.
Two preflight fixes changed only namespace-opening syntax before successful
target elaboration. Proof repairs fixed elaboration and simplification.
Two combined-helper attempts reached the unchanged RSS limit; splitting the
helpers and unfolding only relevant endpoint field definitions resolved the
problem without changing a target or resource cap. The failed helper sources
are preserved. The final gate passes every exact original contract.

`ACCEPTANCE.json`, `AXIOMS.json`, `FROZEN-PRESERVATION.json` and
`exact-checks.log` record acceptance. Source pins, complete successful native
rows and the final receipt are losslessly compressed; coverage is divided
into four files. `EVIDENCE-ENCODINGS.json` records both stored and uncompressed
hashes. Every compiler process for this checkpoint has completed.

See `SOURCE-CORRESPONDENCE.md` and `NEXT-STEPS.md` for the mathematical boundary.
