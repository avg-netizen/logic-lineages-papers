# Paper 17: the raw per-row level program, calibrated to the level-order supplier

Key: `STAGE-CALLBACK-RAW-LEVEL`. Targets module
`LogicLineages.PermittedControl.StageCallbackRawLevelTargets`.

Printed source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
`thm:arithmetic`: "The proof is constructive … the entire symbolic normalization tree can be
generated before numerical tails are chosen. It contains finitely many interval, certificate, peeling
and transfer labels." This key is the code-level generation of one row's tree, as a literal list
equation with the typed list of `STAGE-CALLBACK-LEVEL-ORDER`. It is one link of `Emits`.

## What is stated

Raw definitions on encoded data only (`Nat`, `Int`, `Bool`, lists, products):

- `EntryCode = List PreparedPacketCode × RawSyntax`, `encodeEntry`.
- `nodeOut s tape = groupedCode (s.1, groupRaw s.2, tape)` — the accepted raw node (#1355).
- `childrenCode R top e`: **if** `tapeHighestCode top (groupRaw e.2.2)` (the accepted raw activity
  test at `top`, which the accepted `stepCode`/`prefixes` do not apply) then one child per candidate
  tape with zero coefficient and a successor, carrying one more guard code; else none.
- `leavesCode R top order positive e`: the rendered packet codes of the stopped candidates —
  the linear exit joined below the entry's guards if inactive; one joined signed leaf per nonzero
  tape if active.
- `levelCode`, `signedCode`: the same `flatMap` iteration and level-by-level collection as the typed
  `level`/`levelRoutes`.
- `rowCode R r top row`: header tag 3 → the congruence packet code; otherwise `signedCode` on
  `cleanupCode` of the row's syntax at `syntaxBudgetCode`.

All of it is parametric in a record `Rendering` of four programs (`append`, `guard`, `linear`,
`modular`), with `Rendering.Exact` asking one calibration equation of each on encoder outputs
(through `RawPacketAlgebra.encodePacket`, Opus B's frozen name for `preparedPacketCode`).

Targets:

- `ExactRawActivity` — `tapeHighestCode top (groupRaw (ts.map encodeWeighted)) = true ↔
  CanonicalActive top ts`.
- `ExactRawLevelEntries` — `levelCode R top (encodeSyntax s) n = (level top s n).map encodeEntry`.
- `ExactRawSignedPackets` — `signedCode … (encodeSyntax s)` is the encoded rendered `levelRoutes`.
- `ExactRawRowPackets` — for every exact rendering and every literal bit row,
  `rowCode R r top (encodeBitRow row) = (levelOrder r top row).map encodePacket`.

## What is assumed

`R.Exact` — four calibration equations. They are *not* the conclusion: none of them mentions levels,
tapes, successors, activity, cleanup or budgets; they say only that each rendering program computes
the code of the corresponding typed packet (`append`, the comparison guard on a label list, the
canonical linear exit, the congruence packet). No hypothesis on `f` or `B`; this key is syntax only.

## What is not claimed

- No rendering program is constructed here: `guard`, `linear` and `modular` are still owed (R1–R3 in
  the ledger); `append` is Opus B's `appendCode` (`ExactAppendCode`), which this key does not import
  or assume by name.
- No effectivity statement. `rowCode R` is built only from accepted primitive recursive pieces and
  the four programs of `R`, but `Primrec`/`Computable` of `rowCode R` is a separate target, not
  frozen yet.
- Calibration only on encoder outputs (`encodeBitRow row`, `encodeSyntax s`). On other raw input the
  program returns some list with no claim.
- No semantic statement; the semantics are #1394/#1395 and `STAGE-CALLBACK-LEVEL-ORDER`.
