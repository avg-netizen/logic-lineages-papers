# Syntax-leaf front test for free-variable nodes — source map

Fable B2, 27 November 2026. Module
`LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2.lean`
(definitions only; sha256 in `LEDGER.md`).

**Serves.** Paper 16 `lem:arithmetic-accessibility` → K1 `FreshAddressCarrier`, step 1 of the repair
in `root/K1-VARIABLE-NODE-FINDING.md`, for the **syntax leaf only** (root's order of 15:00).

**Programs.** `isVariableNode := header 0 2` (the existing explicit header test, tag 0, two
fields); `variableCheck TV := applyUnary TV (field 0)`;
`variableFrontSyntax TV V := branch isVariableNode V (variableCheck TV)` (`branch c a b` is `a` on
`c = 0`, else `b`; so `V` off variable nodes, the check on them).

**Statements.**
- `VariableSyntaxBit` — for `TypeSyntaxCalibrated TV`: on every `raw` with
  `run isVariableNode raw = 1`, `run (variableCheck TV) raw = (syntaxBits raw).1.toNat`.
  A fact about functions (`termParts 0 [t,_] = typeBit t`), no opaque program involved.
- `VariableFrontSyntaxCalibrated` — `TypeSyntaxCalibrated TV → TermSyntaxCalibrated V →
  TermSyntaxCalibrated (variableFrontSyntax TV V)`.
- `OpenVariableFrontSyntax` — for arbitrary `TV`, `V`, body, context, open `ty i out`:
  `unary TV out ty ⊢ unary (variableFrontSyntax TV V) out (namedTerm 0 ty i)`. This is step 4 of the
  finding for the syntax leaf; it is included because the header and field reports at a named leaf
  already exist (`exact_OpenCoverNamedLeafIntrinsicShape`).

**Assumed.** Only the two calibrations in the numeric statements; nothing in the open law.

**Not claimed.** Re-installation of the packet/window at `variableFrontSyntax TV V` (step 3);
front tests for the measure and window leaves; K1. Bound names (tag 1) are not intercepted.
`namedTerm 0 ty i` is `rawCons (numeral 0) (rawCons ty (rawCons i z))`; its identification with
the payload `consTerm z (consTerm dom (consTerm name z))` of `packedFreeTerm` is not proved here.

**Existing material this should be combined with (found this session, not used yet).**
- measure leaf: `namedMeasureBase M` with `exact_CoverNamedLeafMeasureBase`
  (`TermMeasureCalibrated` preserved) and the open law `exact_OpenCoverNamedLeafSharedMeasure`
  (`NumberedWindowInternalCoverNamedLeafMeasure{Targets,NumericProof}`,
  `…NamedLeafSharedMeasureProof`) — the measure front test already exists, for the measure
  `namedSharedMeasure M`, which is not the installed `chosenMeasure baseM`;
- generator: `exact_OpenCoverNamedLeafMeasuredScratch` /
  `ExactOpenSelectedGrammarNamedLeafScratch` — a named leaf accepted by the syntax program, with
  type in `typesTerm s`, occurs in its own selected scratch;
- window leaf: `namedGrammarBase s B` (`…NamedLeafIntrinsicTargets`) only adds a rejection guard
  and still returns the opaque base on acceptance, so the positive window fact at a variable node
  is **not** available from it;
- self-least: once coverage holds, the self-least of an atomic seed does not need the exchange
  leaf: `atomObserver` is one of `childGuardObservers`, so the selected least of an atomic seed
  carries the seed's own stamp (`exact_OpenAtomStampPositive`, observer preservation).
