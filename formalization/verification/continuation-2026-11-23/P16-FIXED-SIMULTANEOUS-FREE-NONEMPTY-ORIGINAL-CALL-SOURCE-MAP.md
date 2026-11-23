# P16: original simultaneous free substitution, one whole nonempty call at a fixed point

Source-only current freeze, no native result. Exact gate order:
1. `LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeTupleProof`
   for `exact_FreeImageTupleCodes`, `exact_FreeImageTupleCallTyped`, and
   `exact_FreeImageTupleDomains`.
2. `LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeCallProof`
   for `exact_FixedSimultaneousFreeNonemptyCall`.

## Exact source boundaries and provenance

| Source | Literal correspondence |
| --- | --- |
| decision.tex 138–148, 149–172 | Same original protected spine and simultaneously appended whole tuple, not a sequence of unary calls. Both original source q and every old argument are interpreted in the *one* original concrete free-image assignment. The final source and list are original `freeSub θ 0 q`, `freeSubArgs θ 0 xs`. |
| `ProtectedSpineFreeCases.ArgsSub` and checked #396 | Its `ArgumentsAgree` says equality of the *ordered complete `(Ty, Code)` list*. Induction on the literal original Args list uses the exact already-checked cons lemma and source `expression` agreement (the latter compares interpreter evaluations of each original child and its actual substitution). At concrete default post-assignment the right side is exactly `closedCodes`. No inferred equality from weak/strict bits. |
| Original typing and annotations | Transfer original `CallTyped` by induction on its actual spine and `FreeTypingProof.freeSubTyped` for each original argument. Preserve the same `domainTypes` list using exact existing `FreeCallProof.annotation`. Project actual code-list agreement into the tuple values for the original checker. |
| #1480 distinct input | #1480 interprets q in the free-image assignment but takes arguments already concrete after substitution. This root replaces that already-concrete input with the original tuple evaluated in the same actual input environment, and instantiates #1480 at its genuinely substituted, proved-typed ordered tuple. No old proof body is copied. |
| #398 original apply and none | Through #1480, apply the same actual `Spine.apply` to the substituted source and the complete substituted tuple, using `concreteOutput` for the exact option. The none case retains entire bottom. Neither original success nor original failure under the old default environment is a hypothesis. |

Both old and substituted source and tuple have explicit genuine finite
type/head coverage. The source inputs require the original `FreeImages`,
actual `InputValid` and actual `FreeSubstitutionInputs`, with the same
original Γ and retained `M` satisfying `step S E H M = M`. This does
not synthesize a free environment or remove finite coverage. The internal
list-equality helper does not require a fixed point; application does.
No arbitrary-stage result, zero-argument result, parallel measured
program, change of printed text, or numbered promotion. #396’s retained
bottom-family counterexample is unaffected.

## Source pins

```
98f06a0a1e9644d054e549680cb2716f5e959f2e0c0ab110fa59786794c8daaa  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedSimultaneousFreeCallTargets.lean   (local names: 47)
c5877db50cb6a078328dadce6d7db7cea6a550190ed0e581ad93048feb81b58b  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedSimultaneousFreeTupleProof.lean   (local names: 237)
6d9266784ed716967ee312224c55f2b6570c61fc22a221828de5c09cd225befa  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedSimultaneousFreeCallProof.lean   (local names: 247)
```

Static checked import graph excludes Hydra, GameAdd, Sym2 and Rank.
Unchanged dependencies and manuscript:

```
26a98e8e2f1a546762ba138b65687f62f922708b3e359e0987dcbe96be7d6a62  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedFreeImageCallTargets.lean
7254670e8565fda31bbc46f8a1bcaaf6d634b2ec4a7cb39f4b82825ec34a82cd  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedFreeImageCallProof.lean
1ad8647d4710eb0bd0d95458eeaa95d763929f7b2e1a3267d54cc53efac64e72  formalization/LogicLineages/PersistentMarking/ProtectedSpineFreeCases.lean
a4f8328c7ff3d6515659d2a589fa32242a07824f5b961d0f12d535f95d46342b  formalization/LogicLineages/PersistentMarking/ProtectedSpineFreeSubstitutionProof.lean
9a8f36b46094ce4b86e3f4b63b4a264db0735da36703ffacbc1fe134f857311c  formalization/LogicLineages/PersistentMarking/ProtectedSpineConstructorAgreementProof.lean
78e436e9d5010cfd4c1cf2627c2e5b40c50aa17a49fc8b912d87361f9da3aa9d  formalization/LogicLineages/PersistentMarking/ProtectedSpineInterpreter.lean
1c94f21bfd2bd65f75bda6e6d8d760e6c7e11ec68be450b95067889ec53ba27d  formalization/LogicLineages/PersistentMarking/FreeSubstitution.lean
8949260abf66d1bd999e0652d6c7522ae07746aa8a097411794fce6e4ddb6cd0  formalization/LogicLineages/PersistentMarking/FreeTypingProof.lean
2c309ed6c1bf1e4f19be1f573d8a222f2edbd22b31e6e5b09fa6f23f8b3e4acb  formalization/LogicLineages/PersistentMarking/FreeCallProof.lean
28fa5423c177cceee69eec67a3eeaeffe6a8c2cb393c8d4d728e3238c8082d0a  formalization/LogicLineages/PersistentMarking/SpineCallTypingProof.lean
746e256ad5d740697e77de542fa0982e3d1682c989280ca3940e5ff65fab3a76  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedApplicationTargets.lean
2dcac539d8d6466fa8baa87f88cc3841f17c64e4481bd860bb6f67690eada275  16-persistent-marking-termination-ordering/sections/decision.tex
```
