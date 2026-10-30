# Quotient-filtration dependency chain

Current checkpoint, 30 October 2026: the entire two-conclusion quotient lemma
below was completed by the external continuation, including the actual Ulm
isomorphism and rank equality (`1793267996776944661-6`). The step statuses below
describe its earlier construction history. The resumed local lane has also
completed the original finite-product back-and-forth lemma; see
`BackForth-ACCEPTED.json` and `status/models-algebra.md`. Infinitary/Scott
semantics, the cited realization/comparison theorems and full classifications
remain pending; neither completed lemma assumes them.

The current source is paper 01, `lem:quotient-filtration`, not the final
Scott-complexity classification. Its first conclusion concerns actual
ordinal filtration stages; its second concerns actual Ulm quotients and
their dimensions. Neither conclusion will be taken as a theorem premise.

1. **Successor and limit suppliers — accepted.** Multiplication-by-p
   images commute with additive homomorphisms. Finite filtration images
   commute with surjections. Images commute with arbitrary subgroup
   intersections when each subgroup contains the kernel. The independent
   exact gates and axiom reports passed in receipt
   `1793249492913314109-2.json`.
2. **Actual ordinal recursion — accepted.**
   `TransfiniteDefinitions.lean` uses `Ordinal.limitRecOn` with top,
   multiplication-by-p image, and all-earlier-stage intersection. Prove
   the recursion equations and antitonicity from closure under nsmul.
3. **Image below a kernel cut — accepted.** Derive containment
   in every earlier subgroup from antitonicity, then perform the actual
   ordinal induction using item 1. The fixed target has only the genuine
   surjection and kernel-cut inputs.
4. **Literal quotient map — accepted.** Use the actual
   `QuotientAddGroup.mk'`, its proved surjectivity, and
   `QuotientAddGroup.ker_mk'`. This gives the first source conclusion for
   arbitrary cuts, hence in particular at omega times gamma. Items 2–4
   passed the exact gates and standard-three axiom audit in receipt
   `1793251592919663407-2.json`, closing the complete first displayed
   conclusion of the source lemma.
5. **Actual socles and Ulm quotients — written, uncompiled.** Define the p-socle of
   an actual subgroup by its intersection with the kernel of nsmul. The
   next-stage socle is a subgroup of it, and their actual additive-group
   quotient is the Ulm quotient. Construct its p-annihilation proof.
   Mathlib's `AddCommGroup.zmodModule` then constructs its scalar action;
   it is not an assumed vector-space interface.
6. **The induced Ulm map — construction and candidate written, uncompiled.** Restrict the quotient map to the
   actual socles and descend it to those quotients. Surjectivity uses the
   source's explicit correction: for px in T contained in the second
   successor stage, choose z in the first successor stage with pz=px.
   Injectivity uses kernel containment in the first successor stage.
   `UlmDefinitions.lean` and `UlmMapDefinitions.lean` contain the actual
   data and well-definedness proofs. `UlmTargets.lean` fixes bijectivity
   of that actual map under kernel containment in p²S. The bijectivity
   candidate in `UlmIsomorphism.lean` proves the preimage identity for
   the denominator, injectivity by the actual map kernel, and
   surjectivity by the explicit x-z correction. Neither the data nor
   this candidate is accepted until compilation and the fixed exact gate.
7. **Linearity and dimensions — pending.** The existing proved
   `AddMonoidHom.toZModLinearMap` supplies scalar compatibility for the
   actual additive map. Establish its bijectivity from item 6, construct
   the linear equivalence, and derive the rank identity. Prove the ordinal
   fact beta+2 < omega*gamma for beta < omega*gamma, including the vacuous
   gamma=0 case, before applying kernel containment.

Only items 1–7 together close the full two-conclusion source lemma. This
does not supply infinitary syntax, Scott sentence semantics, Ulm/Zippin
classification or existence, the back-and-forth suppliers, Walker group
constructions, or the final Scott-complexity classifications. Those remain
the full-paper obligations recorded in the lane status.
