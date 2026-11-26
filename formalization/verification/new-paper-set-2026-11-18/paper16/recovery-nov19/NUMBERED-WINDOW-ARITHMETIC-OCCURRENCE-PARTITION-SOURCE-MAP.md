# Paper 16 occurrence origins and component descent

The source is [ordinals.tex, lines 142–148](../../../../../16-persistent-marking-termination-ordering/sections/ordinals.tex#L142-L148), in `lem:arithmetic-accessibility`. The paper labels removed occurrences by their source component and assigns every insertion to a removed dominator. It then uses the two component replacements in a nested induction for closure of `J` under multiset union.

| Lean declaration | Source obligation |
| --- | --- |
| `KeptRemovedByOrigin` | Tag the two source lists before transporting their supplied occurrence permutation. Recover the exact kept and removed lists after erasing the tags. |
| `DirectAddressUnionSplit` | Assign each inserted occurrence to the component of one genuine removed `AddressPositive` dominator. The target is a permutation of the two component targets. Each component is unchanged up to permutation or has an actual `AddressDirect` replacement, and at least one component strictly decreases. |

The comparator imports the retained `NumberedWindowArithmeticDirectMultisetTargets`. `AddressDirect` keeps the actual canonical-address domains and the original positive same-fiber quotient relation. A tag records the origin separately from an address, so equal values in either component retain their multiplicities. The split permits deletion, empty components and reuse of a removed dominator. The existing typedness preservation theorem supplies the domain of each strict component target.

These two contracts supply the occurrence argument for the nested induction. Closure of `J`, an object-language arithmetic definition, and the numbered ID₁ accessibility proof remain separate obligations.

The cloud-loss handoff records that historical exact1720 failed in `KeptRemovedProof` and its archival command never launched. No exact1720 Lean source, receipt or diagnostic log was available from the checkout at `3dd39b57a`. The comparator and proofs in this packet are newly written from the retained manuscript and semantics. The existing simulation split supplies a different source obligation at ordinals.tex lines 280–290. [Cloud-loss handoff](../../recovery-nov19/CLOUD-LOSS-1511-HANDOFF.md)
