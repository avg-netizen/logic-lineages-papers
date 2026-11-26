# Sparse application uniqueness and reinstallation: source-only route

Independent source-only review of the next possible gate after accepted
support records 717/719 (output core) and the frozen application frontend
target. The following is a proof plan, not a proved or native-checked
uniqueness, installation, or downstream endpoint. References use
module-and-declaration notation; a module stem ending in Definitions
need not be the declaration namespace.

## Existing tuple shape

`NumberedWindowInternalSparseApplicationFrontendDefinitions.applicationGuard i least`
is literally `guard i (applicationCore least)`. The existing
`NumberedWindowInternalSparseTupleDefinitions.InstalledTupleAt`
therefore fits with `p₀ := applicationCore least`. Its structural field
`v.applicationGuard = guard i p₀` would be discharged by reflexivity
on the updated Inputs, not by relating the new program to the old p₀.

## Route to actual UniqueResult from the frozen report

1. Use the forward half of
   `NumberedWindowInternalSparseApplicationFrontendTargets.ExactOpenGuardedApplication`
   on the two input acceptances at the same whole addresses `f,u`.
   `NumberedWindowComputabilityFormulaTargets.accepts` is the unit
   `programGraph` here. Eliminate the two six-field blocks using
   `InternalFiniteBlocksProof.actualFiniteExistentialElimination`,
   following
   `NumberedWindowInternalSparseAddressPositiveOpenBindingProof.reportsCases`.
   Use `InternalGraphCompositionFunctionalityProof.renameInto` to
   move the unpeeled report and previously obtained derivations through
   the actual enlarged contexts. The exact outer block order is
   `[ctx,result,dom,cod,fn,arg]`. The actual least witness is a
   separate inner existential. Use
   `NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof.reportUnfold`
   and `Derivation.existentialElimination` for that binder;
   `reportRename` and `auxiliaryRename` in the same module transport
   the report through the other binders.
2. Use `InternalControlGraphSupportProof.valueUnique` on
   `rawContext`, `rawDomain`, `rawCodomain`, `rawLeast` on the same
   unchanged `f`, and on `rawLeast` on the same unchanged `u`.
   These are the actual same-program unary graphs from the two reports.
   This aligns the five coordinates entering the output core.
   Comparing the extra source `result` coordinate is unnecessary;
   neither sparse packing inversion nor canonical semantics is needed.
3. Identify the literal tag-six seeds by congruence. To avoid new
   constructor-substitution lemmas, use
   `NumberedWindowInternalSparseApplicationOutputCoreEmitterProof.seedGraph`
   on both six-tapes with the same dummy last coordinate `z`, then
   `InternalGraphCompositionEqualityProof.graphInputTransport` and
   `valueUnique`. Use `graphInputTransport` to move one actual
   `least` graph to the other input triple; `valueUnique` gives
   `S k = S k′`. Apply `InternalTagArithmeticSupportProof.cancelSuc`
   to obtain `k = k′`.
4. Use
   `NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof.addressGraph`
   with input transport and functionality to identify the two literal
   output addresses. Compose with the two report equations using
   `InternalTagArithmeticSupportProof.trans` and `symm`. Carry
   `eqn y y′` through the cuts, then use
   `InternalControlGraphSupportProof.equalEqn` for
   `NumberedWindowFunctionalGraphTargets.UniqueResult`'s
   `equal y y′`. This route does not use numerical functionality
   as an internal derivation.

## Route to fresh InstalledTupleAt

- Keep the same `i,j,cv,tv,d,raw,least` and the same positive
  `r := addressPositive cv tv raw least`. Preserve the existing
  `Evaluates`, `Interprets`, `Rules`, `CallbacksAt`, and
  `InstalledReportAt` on these literally unchanged programs and body.
- In `NumberedWindowInternalFreshProbeParsedTypedDefinitions.Inputs`,
  update only `applicationGuard`; retain `priorTyped`,
  `optionApplication`, `scalarProg`, and `freshBound`. In
  `CalibratedInputs` retain the first three conjuncts; derive the
  fourth using `ExactAllInputGuardedApplication`, exact scalar
  calibration from the first conjunct of
  `Evaluates (checks entries s) i j r d`, and the same
  `ActualLeastCalibration` from `CallbacksAt`. The installed
  scalar `i` is not an identification with the separate probe
  `scalarProg`.
- Supply new `UniqueResult` via the preceding proposed proof and
  fresh `InputGuards` via
  `(NumberedWindowGuardedGraphChecks.exact_GuardRules i j r d (applicationCore least)).1`.
  No old-p value equality or transfer of an arbitrary old-p
  derivation is required.
- Follow the tail of
  `NumberedWindowInternalSparseTupleTypedProof.selectTyped` to rebuild
  `NumberedWindowInternalAtomicRefinementReinstallTargets.TupleAt`:
  `NumberedWindowInternalFreshProbeParsedTypedNumericChecks.exact_ParsedTypedCalibration`,
  `NumberedWindowInternalFreshProbeParsedTypedObjectChecks.exact_SameParsedTypedProbeTotal`,
  `NumberedWindowInternalFreshProbeParsedTypedObjectChecks.exact_OpenLiteralParsedFresh`,
  and `NumberedWindowInternalFreshProbeAlignmentChecks.exact_GivenFreshAlignmentAndCarriers`
  on the updated Inputs. `chosenA` is definitionally unchanged;
  `chosenLeaves` includes the application guard, so `chosenH`,
  its calibration, and the dependent derivations are newly supplied.
  `ValidWindow` remains an explicit tuple premise, not a premise of
  object uniqueness. Close the existing `InstalledTupleAt` using the
  new `TupleAt`, reflexive guard equation, unchanged callbacks and
  unchanged installed positive report.

## Boundary

The input guard and available aligned-carriers interface give the two
input carriers. Neither the successful least graph nor
`NumberedWindowInternalFreshProbeAlignmentTargets.AlignedCarriersAt`
supplies an output carrier. The separate
`NumberedWindowInternalMatchReductionTargets.RawMatching` requires
both the earlier application result and its transformed positive
certificate at the exact supplied endpoint. Neither is inferred by
this plan. No Lean source or freeze pins changed; no compiler ran.
