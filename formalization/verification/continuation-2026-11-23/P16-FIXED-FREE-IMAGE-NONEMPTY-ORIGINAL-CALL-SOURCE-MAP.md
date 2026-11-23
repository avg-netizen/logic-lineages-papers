# P16: fixed-point original whole call under a concrete free-image environment

New exact source-only target:
`ProtectedSpineFixedFreeImageCallTargets.FixedFreeImageNonemptyCall`.
Gate the original modules plus the new exact alias
`LogicLineages.PersistentMarking.ProtectedSpineFixedFreeImageCallProof.exact_FixedFreeImageNonemptyCall`.
The statically traced proof closure has 244 local module names and no Hydra, GameAdd, Sym2, or Rank. Native verification is pending.

## Exact correspondence

| Printed source or earlier packet | Exact relation here |
| --- | --- |
| decision.tex 138–148 | Same protected original-spine helper, one whole nonempty tuple of actual source-expression codes. No currying or individual application stages. |
| decision.tex 149–172, free-image application case | Nonempty call on q using a genuine type-preserving covered free-image map and an actual valid Γ free assignment satisfying the original `FreeSubstitutionInputs` relation to empty-default interpretation of those images. The original `freeSub θ 0 q` is the source in the post-substitution application. |
| #396 free substitution component | Its original `Agreement.call` gives equality of the two helper outputs for the one common actual whole argument tuple, with consumed count zero and actual admissible tuple supplied by `fullPrefix`/`codeValid`. |
| #398 `FixedApplication`, `FixedApplicationAux` | The former starts at already supplied q with empty free inputs; the latter has bound images, not the explicit free-map θ and actual original free-environment relation. Here checked typing/annotation preserve calls across actual free substitution, then #398 gives concrete `Spine.apply` at the **same** retained fixed family; no new comparison engine. |
| Undefined cases | The result is literal `concreteOutput … (apply …)`, including the whole-bottom `none` result by its original definition. No assumption of prior undefinedness or preservation of earlier undefinedness. |

## Explicit boundaries

The actual family is retained and satisfies `step S E H M = M`; any
actual designated least fixed point is a valid instance if it meets the
same scope. The counterexample #396 at the retained bottom family still
excludes arbitrary-stage application. The genuine later source and the
already-concrete tuple have explicit finite type/head coverage; the
source annotation and object-environment validity are preserved, not
invented. This is not simultaneous re-encoding of the tuple under θ,
an assignment synthesis theorem, a zero-argument new result, a new
numbered target, or a repair to the printed arbitrary-family clause.
It is unrelated to selected sparse leasts and proves no new ID₁ ordinal
or measured-exchange statement.

## SHA-256 source pins

```
26a98e8e2f1a546762ba138b65687f62f922708b3e359e0987dcbe96be7d6a62  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedFreeImageCallTargets.lean
7254670e8565fda31bbc46f8a1bcaaf6d634b2ec4a7cb39f4b82825ec34a82cd  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedFreeImageCallProof.lean
2dcac539d8d6466fa8baa87f88cc3841f17c64e4481bd860bb6f67690eada275  16-persistent-marking-termination-ordering/sections/decision.tex
97cd773a500ee20f946e72ba3100ddd1e8007fbf46b575c534a4683ba5baecfb  formalization/LogicLineages/PersistentMarking/ProtectedSpineSubstitutionTargets.lean
a4f8328c7ff3d6515659d2a589fa32242a07824f5b961d0f12d535f95d46342b  formalization/LogicLineages/PersistentMarking/ProtectedSpineFreeSubstitutionProof.lean
746e256ad5d740697e77de542fa0982e3d1682c989280ca3940e5ff65fab3a76  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedApplicationTargets.lean
6ace7554ba12507edfdcb447bd5d749143b35ae513feca30c5e098f0855928ea  formalization/LogicLineages/PersistentMarking/ProtectedSpineFixedApplicationProof.lean
4526be46a659043a3c5ace3b03ad5b734b2a485c9486b600cf2c5ce093d67452  formalization/LogicLineages/PersistentMarking/ProtectedSpineConcreteInputProof.lean
c1c46ec414c39fe821f92dcd238001d2f32e4907948a857597ca5fe8ef380d21  formalization/LogicLineages/PersistentMarking/ProtectedSpineAgreementTargets.lean
78e436e9d5010cfd4c1cf2627c2e5b40c50aa17a49fc8b912d87361f9da3aa9d  formalization/LogicLineages/PersistentMarking/ProtectedSpineInterpreter.lean
8949260abf66d1bd999e0652d6c7522ae07746aa8a097411794fce6e4ddb6cd0  formalization/LogicLineages/PersistentMarking/FreeTypingProof.lean
2c309ed6c1bf1e4f19be1f573d8a222f2edbd22b31e6e5b09fa6f23f8b3e4acb  formalization/LogicLineages/PersistentMarking/FreeCallProof.lean
```
