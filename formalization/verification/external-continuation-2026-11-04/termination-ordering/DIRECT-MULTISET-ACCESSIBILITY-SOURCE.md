# Explicit-irreflexivity accessibility bridge

Parent reviewed exact targets and correspondence at 2026-11-04 10:51 UTC. Standard comparator and prospective freeze must precede proof authoring. No export or publication is authorized.

Paper06 lines598–603 uses accessibility of multiset members to obtain multiset accessibility. This is a generic standard metatheoretic prerequisite, not an ID1 derivation. R is source-to-successor. Scalar accessibility is Acc (fun successor source => R source successor). List accessibility is Acc (fun target source => Direct R source target).

First, a strictly positive accepted CutPath gives TransGen (CutExpand (flip R)) target source, reversing the written forward path endpoints to match Lean accessibility. The count must be positive; a reflexive empty path does not give TransGen.

Second, GLOBAL irreflexivity ∀a, ¬R a a is an explicit hypothesis. Mathlib Logic/Hydra.Acc.cutExpand and Relation.acc_of_singleton require Std.Irrefl (flip R). Together with the given accessibility of every source occurrence these produce CutExpand accessibility of the source multiset. Transitive-closure accessibility and pullback along list-to-multiset, combined with the accepted Direct-positive-path result, yield accessibility for ReverseDirect. Permutations and duplicates are preserved, not replaced by finite sets. No transitivity or global well-foundedness is assumed.

This cannot yet be instantiated for unrestricted actual R without separately proving irreflexivity. To remove that hypothesis, a later component must restrict to the subtype of scalar-accessible elements, derive its irreflexivity and forward closure from Acc, lift every Direct successor occurrence and its permutation/decomposition witnesses into that subtype, and transfer accessibility back to original lists. Merely knowing each initial member accessible does not provide global irreflexivity on the ambient type. None of those subtype lifting claims is assumed or proved here. No global WF, ID1, or original-order transitivity claim.
