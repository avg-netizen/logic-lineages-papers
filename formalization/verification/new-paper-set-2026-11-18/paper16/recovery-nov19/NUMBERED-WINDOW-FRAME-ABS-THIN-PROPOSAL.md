# Material new-only Abs recovery elaboration redesign

The first typed-transport split worked: FRAME-THIN-0922 compiled
TypedThinCore (477524 KiB), typed admissibility (477920 KiB), full
primary and typed trace, shifted syntax, numeric realization and
freshness, and scope support. It then stopped at a separate leaf:
original ClosingAbsProof 1e6eecc7, exit77 at 525948 KiB, 43/44,
native receipt `1795080087227938028-6`. All its exact bytes and the
full candidate, receipt, and logs remain preserved; no unchanged retry
and no resource/enforcement changes.

New-only `NumberedWindowClosingAbsThinBuilders` keeps the same lexical
`ScopeAt`, bound interval/equality case, actual single substitution,
and real typed-name freshness from the stopped proof. The original
well-founded recursive package is removed from the candidate closure.
Eleven separately elaborated opaque constructor handlers check the actual
round-trip equations (the two nil handlers share the one identical
`bNil`). Numeric `Typed.rec` combines them as a small existing proof
eliminator, using the same explicit positional inference adapters that
now passed in the first typed split. Source shape, actual argument typing,
freshness, and context are unchanged; no terms are normalized.

`NumberedWindowClosingAbsThinCore` does not load the realization typing
supplier. The separate exact `...AbsThinProof.absBody` uses the unchanged
realization typing/freshness and ordinary empty context plus the actual
one-slot push to discharge all internal structural requirements. Its
external type is the *same* frozen ClosingRecoversAbsBody; no new alias
premise. `NumberedWindowFrameAbsThinChecks` is an append-only exact clone
of all thirteen existing alias types and audits, redirecting only the
one Abs proof and the new module namespace. Both earlier hard-stopped
sources/roots are statically excluded and byte-preserved.

This is an independently reviewable proposed redesign only, no native
proof verified by it yet. Recheck the existing 21 frozen inputs and all
newly reviewed files before any unchanged-cap exact ticket.

Closure estimates: `NumberedWindowClosingAbsProof` 30, `NumberedWindowClosingAbsThinBuilders` 28, `NumberedWindowClosingAbsThinCore` 29, `NumberedWindowClosingAbsThinProof` 32, `NumberedWindowFrameThinChecks` 47, `NumberedWindowFrameAbsThinChecks` 49.

## New exact proposed source hashes

```text
dbcfe6b1b04476595c3016dbffdadb62e74b186357a93a63fb26646747c2b910  LogicLineages/PersistentMarking/NumberedWindowClosingAbsThinBuilders.lean
324a15b884b622e700d436e0e13e807ed7abdcb76affdad36ccfcc597bd0c4c8  LogicLineages/PersistentMarking/NumberedWindowClosingAbsThinCore.lean
1961a3884c00e82f7ac40032a5f84c9ef13b3023d5a3dfe1cace671d16783a0e  LogicLineages/PersistentMarking/NumberedWindowClosingAbsThinProof.lean
765f144e9633d44ffae14129dec8cf134cf70a5a5a76e6605135635031b17f00  LogicLineages/PersistentMarking/NumberedWindowFrameAbsThinChecks.lean
```
