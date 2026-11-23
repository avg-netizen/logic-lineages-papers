# Paper 16 (T): mixed-domain right-spine C→I

Original target fragment: `16-persistent-marking-termination-ordering/sections/ordinals.tex:113–127`.
The manuscript's joint higher-type assertion is not closed by this source packet.
`MixedDomains` indexes the unchanged original type syntax: each domain
along the right spine is either ground or `σ→ground` for arbitrary σ;
the final codomain is ground. This includes arbitrarily high σ inside an
admissible domain, not every possible domain of an arrow.

- `NumberedWindowInternalMixedDomainSpineProof` follows the genuine object
  cut in `NumberedWindowInternalLiteralRefinedGroundSpineProof.groundSpine`
  but indexes each step by its own supported dom. The actual same h/p/a
  totality produces one **same** fresh argument u, application p(q,u,v),
  and h-typed result v. It opens the actual two existential binders,
  uses the true Cσ(u) supplier in that context, original application
  elimination, recursive I(v), and finally the supplied real Pullback.
- `NumberedWindowInternalLiteralNeutralMixedSpineProof` pairs the ground
  supplier (uses real same-u carrier from the held tuple) with the exact
  fresh arrow-to-ground supplier (uses parsed selected free shape and real
  type code). Calls `exact_InternalPullback` using the held original
  InputGuards and explicit `ForwardRule` on the exact same literalNeutral
  body and same new physical callback.
- The specialized theorem requires an active `TupleAt` on that exact
  body with `v.applicationGuard = outputGuard i (refinedApplication p)`.
  The matching h is literally `chosenH v W`; no older h, no older
  ForwardRule, and no calibration/reflection supplies the new tuple.
  The proof neither selects the tuple nor discharges ForwardRule. It
  does not claim arbitrary C→I, untyped I, or neutral C at all types.

Independent serial roots: MixedDomainSpineProof (1142/28), then
LiteralNeutralMixedSpineProof (1561/30, after ArrowGroundFresh).
Static direct-reachable import scan finds no known blocked
Hydra/Linarith/Rank/Sym2/GameAdd imports.

Frozen source/premise SHA256 pins:
~~~text
f80991f4ffea68cd4c9245604f3ee9040b0f91d67ceba65cb009952f7feebb4b  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalMixedDomainSpineProof.lean
bc8917bae2b4db9656c0d6b658d99e8ee8dcf40392a6dd207e6ffb3bd0d2c975  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralNeutralMixedSpineProof.lean
35e70ce3f64c5de28c3aadc063b8c0924ff9018b88ae465e22d7f3f6599c7809  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralRefinedGroundSpineProof.lean
b9404e2fc9ed9cd199418981d30ac2ffc4348d6bc813dfef9d51ffc99dda4b9f  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralAuxiliaryFreshGroundProof.lean
bcde6b710d1335674b7a006188cd6df9fb4c0952f1bf6b01a0c0af347f93cdd8  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralNeutralArrowGroundFreshProof.lean
2e896ed4b0615a91534e4bdf060e77837b38979ee8dd33621017bcf0390137b7  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalPullbackChecks.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
~~~
