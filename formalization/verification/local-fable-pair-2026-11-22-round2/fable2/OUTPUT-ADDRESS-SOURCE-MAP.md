# Paper 16: accepted original output address of an installed application

Serves the boundary in `verification/github-continuation-2026-11-22/HANDOFF.md`: "An accepted
application output address still needs the original output carrier/fixed-point reconstruction."
Extends `ExactInstalledCarrierApplicationExists` at the same `install … ` route. Supporting result;
no numbered statement is closed and no register item is promoted.

## Claimed

`ExactInstalledApplicationOutputAddress` (theorem `exact_InstalledApplicationOutputAddress`).
For the installed route `Q := install s V TV M M0 B T base cv tv root other`, any ID1 body, context
and terms: given the two original type guards, the two operand address reports at one context
`ctx` and installed-scalar acceptance of both operand addresses, every goal follows that follows —
under the object continuation over `(β) (j) (Δ) (m)` — from all three of

- `leastGraph Q.source.cover Q.exchange Q.window s ctx cod (auxiliaryTerm dom cod fn arg) m`
  (`m` is the measured packed least of the actual auxiliary term),
- `addressReport (addressTerm ctx cod m) ctx cod m` (the literal original tag-3 address on that
  same witness carries its original physical report), and
- `unary Q.scalar (suc z) (addressTerm ctx cod m)` (the same installed scalar accepts it).

The address is the one the original frontend emits: `outputReport least ctx cod aux y` is
`∃k. least(ctx,cod,aux)=k ∧ y = addressTerm ctx cod k`. Its class field is the least `m`, not the
auxiliary term; an address storing `aux` is not what the frontend outputs and is not in general a
fixed point.

`ExactInstalledSyntaxGuardedApplicationOutputAddress`: the same at `tv := TV`, where only the two
original type guards remain as type premises.

What is derived rather than assumed at the output: the context check (from the function address's
coordinates), the window at the least (wrapped auxiliary formation, then the selected-window law),
the fixed point `leastGraph … m m` (covered-least idempotence #835-family, which applies because
`thinPairedExchange` / `thinMatchingWindow` are literal recuts of `pairedExchange` /
`coveredWindow`; the kernel accepted this by unfolding, no equality lemma was added), and the
report itself (`literalAddress`).

## Assumed (explicit premises)

- `unary TV (suc z) dom ⊓ unary TV (suc z) cod` and the `refitGuard s T` pair — the two original
  type guards, unchanged from the integration statement.
- General statement only: `unary tv (suc z) cod`, the scalar's own type check at the result type.
  This is not derivable (`tv` is an arbitrary program; the operands give only `tv (rawCons dom cod)`
  and `tv dom`) and it is necessary: `exact_InstalledCarrierCoordinates` applied to the conclusion
  returns it. It is one of the four acceptance coordinates; the other three are proved.
- Both operand reports and both operand scalar acceptances, as in the integration statement.

## Not claimed

- Acceptance by the application program itself,
  `programGraph Q.application (suc z) ![qf,qa,addressTerm ctx cod m]`. That needs the
  `applicationReport` block: `arrowGood qf`, `arrowReports qf dom cod`, the shell equations
  `qf = addressTerm ctx (rawCons dom cod) fn`, `qa = addressTerm ctx dom arg`, and the six-witness
  block introduction. None is assumed or used here.
- Discharge of the two type guards, callback/base calibration, `InstalledTupleAt` source semantics.
- That `tv` and `TV` coincide in the source; the second statement is the instance, not a
  calibration.
- Any closed existential formula for the output; the witness stays under the continuation.

## Evidence

Targets sha256 `7164f6998e96658f10e0a5e55b9cfbb821de9655aef7262e0254b521afaf8eca`, frozen before the
proof module existed. Receipt `build-reports/1795397242217822492-3231382.json`. Axioms: `propext`,
`Classical.choice`, `Quot.sound` for both theorems. See `OUTPUT-ADDRESS-EVIDENCE.json`.
