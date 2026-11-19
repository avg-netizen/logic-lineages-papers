# Supporting typed application and numbered-owner append

Proof-free packet, not a claim of the whole numbered tuple lemma. The
frozen prior numeric rule/carrier semantics are unchanged. The candidate
source is `NumberedWindowApplicationTargets.lean`, with 15 source pins
in `NUMBERED-WINDOW-APPLICATION-FROZEN.json`.

| Contract | Printed source / exact purpose |
| --- | --- |
| `RealizedCallArgs` | Read the actual domain list of the original typed argument spine (same argument order and length), then obtain each numeric argument's same-window typing/support from its original realization; no extra gate on symbolic argument terms. |
| `AppInWindow`, `ApplicationsInWindow` | Build the actual distinct auxiliary app nodes at the annotated domain and codomain; subtype closure of the original fully typed function arrow supplies each suffix, with unchanged window/outer context. A same-window actual application spine is a conclusion, not a new hypothesis on the final tuple lemma. |
| `LiftAuxFunction`, `LiftApplications` | Lift actual finite paths using function-side closure only, keeping the same concrete arguments, declarations, types and all intermediate windows. Both auxiliary whole application equations remain explicit. No raw argument-side contexts, currying on symbolic syntax, or equivalence-only strict paths. |
| `OpenNumberedInWindow`, `AppendArgumentInWindow` | The original one-decrement abstraction rule introduces its actual binder, shifts the old base/extras and appends bound zero; its beta then appends the same supplied typed numerical value. Original head declaration and present arrow's domain/suffix remain in the same window throughout. |
| `WholeNumberedAppend` | For the already-numbered functional branch only, build the literal full auxiliary application spine and then one abstraction/beta pair per supplied argument. Exactly the original old extras followed by the whole new ordered tuple survive, and label starts at k+length and ends at k. This is a supporting fixed-window path over the actual new raw relation, not the protected original lambda-prefix or ordinary-head cases of the public theorem. |

Likely small proof leaves: annotation/type support; original-args
realization and raw function contexts; window-aware shift and constructor
typing; exact numeric-append induction using the separately frozen
literal numerical beta helper. The final public tuple claim still needs
the original protected prefix and all successful original head/lambda/zero
and impossible-overapplication branches at the explicit n+length+1
uniform threshold.
