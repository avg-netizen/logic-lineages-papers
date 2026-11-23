# Paper 16: fixed numeric application output and a new physical output guard

These are staged supporting sources, not a numbered (T) result. See
`16-persistent-marking-termination-ordering/sections/ordinals.tex:113–127`
for the typed-neutral / computable-fresh-variable step that needs a real
scalar report at its actual selected application **output address**.

- **Actual source numerical carrier.** In
  `NumberedWindowFixedApplicationOutputGuardProof.exact_FixedApplicationOutputScalar`,
  the exact antecedent is the unchanged
  `NumberedWindowAddressApplication.graph (fixed S K) f u y = true`.
  The proof decodes both held addresses with the original all-input
  correspondence, extracts the two actual classes at matching contexts
  and argument types from the original canonical bits, and uses the
  original checked class application to identify an actual output
  `ActualCodeAt … (appClass …)`. The existing admitted-address reflection
  yields `scalar (fixed S K) y = true`. `DecisionSourceUniverse.Closed K`
  is explicit and essential to this proof. No arbitrary Settings,
  raw-picked shape or new physical address is used.
- **Fresh numeric callback.** For actual programs `i,p`, choose literally
  `conjunction p (NumberedWindowGuardedGraphTargets.atSlot i 2)`, with
  tape `[f,u,y]` just as in the original checker. With actual all-input
  fits for `i` and `p` at the same fixed closed S/K,
  `exact_NumericFixedApplicationOutputGuard` calibrates that exact
  new program on every raw value, with no fallback changes.
- **Independent same-body object projection.**
  `NumberedWindowInternalApplicationOutputGuardOpenProof.exact_OpenApplicationOutputGuard`
  needs acceptance of the **new** program in actual body and context.
  It returns the preserved original `accepts p f u y` and
  `RawDomain i y` on that same y. It only unfolds genuine conjunction
  and projection graph rules; it does not reflect numeral equality.
  In particular it does not assume, or conclude, old
  `accepts p f u y → RawDomain i y` at arbitrary open input.
- Shape/equality laws that consume old `accepts p` may consume the
  projected old report. An argument needing fresh `h`, its typed
  callback or its ForwardRule must explicitly select them using the new
  physical callback; there is no transfer of old `h`, typed reports,
  or ForwardRule by numerical equivalence. This proof does not give
  fresh-variable computability, neutral endpoint closure, `C→I`, or
  unconditioned least idempotence in the old callback.

Suggested independent serial gates (local/external direct-reachable
closure counts): OpenProof (989/28), NumericProof (798/28), legacy
FixedApplicationOutputGuardProof (1014/30). None reports the blocked
Hydra/Linarith/Rank family in the source import scan.

Current source and relevant existing premise pins (SHA256):
~~~text
ed4c06024da4d5fd50bff998a7ad3681d6003e74c5ee80907edcb518e158e552  formalization/LogicLineages/PersistentMarking/NumberedWindowFixedApplicationOutputGuardProof.lean
91305f64c073c238319367b51c8cb6cfd4a05f5f393d9174baa49f2ad250f9c0  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardNumericProof.lean
2cccb521ed095e3a7b76b4716e2298be095775864b6c5bf87a45484d704b1a75  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardOpenProof.lean
e9d232ff0c727b3df7038a5dc8a472749f8c436dcf22c89f4e3c242d7a5a0f93  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardTargets.lean
6f4858113f8b8c2a102e2f6d3a345400d66e39f75fe8ab6bd1078d5cabe61b30  formalization/LogicLineages/PersistentMarking/NumberedWindowAddressApplication.lean
d900d8153cb21f194bde14f3c22c72feab841a152168641e77adf2cff54e82a2  formalization/LogicLineages/PersistentMarking/NumberedWindowAddressApplicationChecks.lean
3dd40d15055cea0ce3403845984dbbc0c774b836e487e297db8db44d8f9b7dbb  formalization/LogicLineages/PersistentMarking/NumberedWindowArithmeticAllContextAdmittedProof.lean
0ec626b475453d5c16b7a75aab1a8916c5a05eda2dc3c45bc2a36b264cdbed09  formalization/LogicLineages/PersistentMarking/NumberedWindowArithmeticScalarChecks.lean
28ec6612a049b4bb439db17a1ff4c8b1f9726ce61285fea3cbb47d1da8157e4b  formalization/LogicLineages/PersistentMarking/NumberedWindowGuardedGraphTargets.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
~~~
