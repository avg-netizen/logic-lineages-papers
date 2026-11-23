# Paper 16: original symbolic J fold from exact local singleton J

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
149–153 derives J for an arbitrary successor of a scalar singleton by already
having J of the actual singleton occurrences of its descendants.
The necessary fold must not assume the general I-to-singleton theorem it will
later support.

* [Interface](../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonProgressTargets.lean)
  fixes the same installed literal-count body and
  `singletonMembers scratch` as the actual first-order condition
  `∀q (actualScratchMember scratch q → J(rawCons q 0))`.
* [Syntax and transport](../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonTargetFoldSyntaxProof.lean)
  specializes the actual ordered fold motive to typed scratch and this local
  premise. An actual tail member is also an actual parent member through the
  same decoded scratch cons; no cross-body or unrelated occurrence is used.
* [Proof](../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonTargetFoldProof.lean)
  supplies exactly `SingletonTargetFoldSupply i r c`. The nil branch uses
  #1596's actual same-body J(empty). At a genuine cons the actual head
  membership opens its local singleton J, the true lower tail uses the
  exact typed scratch tail and local occurrence transfer, and #1578 and
  #1576's actual per-cons U and conditional J union recombine the same
  raw term and transport to the observed raw target. The original parsed
  fold is object-calculus induction, not a host counter/list.
* The only separate theorem-level supplier is still the genuine
  `CertifiedOriginSplit (literalData i r) c permutation`. The actual
  parser, typed scratch, and local singleton-member derivations are
  retained input observations. General scalar singleton promotion,
  singleton progress, proof of the split, and numbered claims are not
  assumed or asserted here.

Native author status: source only; one exact named axiom audit.
