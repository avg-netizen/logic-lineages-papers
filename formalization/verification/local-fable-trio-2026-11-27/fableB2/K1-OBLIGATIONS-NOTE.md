# K1 `FreshAddressCarrier` — what is left after this session (reading note)

Fable B2, 27 November 2026, 15:20. Complements `root/K1-VARIABLE-NODE-FINDING.md`. Everything
under "exists" was read this session as a statement in the named file; none of it was re-run
except where a receipt is given. Files are under `LogicLineages/PersistentMarking/`.

K1 asks for `carrier A.presentation false c u` at `u = packedFreeTerm ctx dom name
= addressTerm ctx dom payload`, `payload = consTerm z (consTerm dom (consTerm name z))`, which is
the term `namedTerm 0 dom name` of the legacy named-leaf line (`consTerm = rawCons` by unfolding,
`numeral 0` vs `z` expected to be `rfl`; **not compiled**).

By `exact_MakeLiteralFiniteScalar` + `exact_OpenLiteralScalarFromSelfLeast` the carrier needs six
facts. Status of each on the installed window:

| # | Fact | Status |
| --- | --- | --- |
| 1 | `unary cv (suc z) ctx` | from the carrier of `q` (`reported`), as in `windowOfScalar` of `…FreshSeedLeastProofV2` |
| 2 | `literalMembership (finiteCodes W) dom` | **missing lemma, small.** `ChildClosed` and `exact_OpenLiteralFiniteCodomain` give the *codomain* only. `sourceWindow K` is also domain-closed (`NumberedWindowApplicationDomainProof.arrowLeft`); needs the numeric `headOfCodes` and the open law with `cellHead`, mirror of `…LiteralFiniteCodomainProof` |
| 3 | `unary tv (suc z) dom` | from 2 by `OpenRankTypeGuards` (now exported: `exact_LiteralWindowWithSeedLeast`) |
| 4 | joined window at `(ctx, dom, payload)` | **open.** Strict half: `strictAuxWindow base Tg` calls the opaque leaf `base` on a variable node. The legacy `namedGrammarBase s B` only adds a rejection guard (`grammarGuard`) and returns `B` on acceptance, so it does not give the positive fact. Covered half: `coveredMemoWindow` needs 5a and the syntax bit |
| 5a | coverage of `payload` (`coverageReport C s ctx payload`) | reducible to: syntax acceptance of the leaf, its measure, and "generator lists a named leaf". The last **exists** for any syntax and measure program: `ExactOpenSelectedGrammarNamedLeafScratch` / `exact_OpenCoverNamedLeafMeasuredScratch`. Syntax acceptance: **gated this session** for the front-tested leaf (`exact_OpenVariableFrontSyntax`, receipt `1795814305566409834-1093361`); for the installed program it still has to pass through `unitAuxSyntax = normalize (auxSyntax V tv)` at a non-auxiliary row (`unaryAfter V currentKey` branch; visible, not written). Measure: the front test **exists** (`namedMeasureBase`, `exact_CoverNamedLeafMeasureBase`, `exact_OpenCoverNamedLeafSharedMeasure`) but for `namedSharedMeasure M`, not for the installed `chosenMeasure baseM` |
| 5b | self-least `programGraph L (suc payload) ![ctx, dom, payload]` | from 5a a least `k` exists (`exact_OpenLeastOnFromCoverage`, `MemoSelectedReports`); `k = payload` should follow without the exchange leaf, because `atomObserver` is in `childGuardObservers` and `guardedLeast` keeps an atomic seed's report only when it equals the seed (`…AtomOnEdgeProof`, `…AtomGuardOnProof`, `…AtomicLeastOpenProof`). **Read, not derived**; needs `atomicTest` at the open payload (`exact_OpenAtomicRecognition` is the likely supplier) |

So the opaque leaves that K1 actually touches are three: `V` (syntax, front test now gated),
`baseM` (measure, front test exists in the legacy tree) and `base` (strict window, no positive
front test anywhere). The exchange leaf `baseX` is not on the path.

Order I would take: (i) fact 2; (ii) the `base` front test with its calibration
(`IntrinsicWindowCalibrated` preserved) and positive open law — the only piece with no
precedent; (iii) one packet restatement at `variableFrontSyntax tv V`, `namedMeasureBase baseM`
(or a `chosenMeasure` over it) and the new `base`, exporting what
`exact_LiteralWindowWithSeedLeast` exports; (iv) K1 on that window from 1–5.
Step (iii) re-runs the coordinator's packet proof text with three leaf substitutions; the
consumers take calibrations as hypotheses, so it is restatement, but it is the largest gate.

## Status after the continuation (15:46, appended)

All six facts are now derived and K1 is a theorem on the window at the front-tested leaves:
`exact_FreshCarrierOnFrontWindow` (receipt `1795815925311427086-1102198`), composed as
`exact_FrontLiteralWindowTyping`. Corrections to the table above: fact 4's strict half had an
existing supplier, `exact_OpenCoverInstallNonAuxWindow`, once the leaf reports positively
(`exact_OpenVariableFrontWindow`); fact 5a's measure is the installed `chosenMeasure` over
`namedMeasureBase baseM₀`; fact 5b is `exact_FreeSeedSelfLeast` (compiled, no longer a reading).
See `LEDGER.md`, "State and next (after the continuation)".
