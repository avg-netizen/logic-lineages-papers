# Independent PairImage refactor review

Approved native check. Original archive7c5e765b7329e5fdafd7970bce01a74f35a3916fc699619f5e27cc95fd0b0a9e and two current pins independently verified. Original imageMatrix/image definitions, four theorem headers, imageRename and introduce proofs byte-identical. Only helper import and imageSubst/imageWitness implementations change.

Generic existential one-binder schema exactly preserves membership(member,1,raw,source) AND pairing(pair,node,param,source), both using same bound source. Generic substitution and witness lemmas use original syntax rules and opaque graph2Subst, no semantic premise/oracle. Original direct exact applications specialize to actual contains/InternalPairing.pairing, no changed AST/public statement. No native/compiler/limit change or resource guarantee; old failure preserved, reviewer ran no compiler.
