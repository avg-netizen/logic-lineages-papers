# First constructive nonlinear elimination bundle: exact inverse cuts

Supporting dependency toward complete m:thm:snyatkov, not a restricted replacement for that theorem. Read actual Snyatkov2008 p40 total floor-inverse convention and pp50–51 inverse boundary witnesses. Existing SnyatkovInverse targets already prove actual Phi/H floor graphs, order and PR; reuse these real proofs, not a caller-supplied monotonicity/inverse oracle.

Choose an exact parameter-preserving one-variable nonlinear cut with fixed-modulus residue:
exists x:Nat, a<=x and x<=b and lo<=g(x) and g(x)<=hi and x%m=r,
where g is exactly Phi or the actual fixed-seed H, m>=1 and r<m. Parameters a,b,lo,hi are arbitrary naturals, not bounded numerals; later they may be arbitrary expanded terms in other free names. This is a nontrivial nonlinear quantified cut and preserves all correlations by a pointwise identity for every parameter tuple.

Define actual lower preimage index Lg(lo)=0 if lo<=g(0), otherwise floorInverse_g(lo-1)+1. Set A=max(a,Lg(lo)); set candidate C=A+((r+m-A%m)%m). Then the exact quantifier-free answer is C<=b and g(C)<=hi. Prove Lg exact minimal lower index, candidate congruence/minimality, and iff directly. This handles below-range defaults, empty intervals, modulus1/r0 and arbitrary large inputs. No assumption of existing solution, supplied witness, search bound or eventual tail. Closed upper raw bound b can be omitted in a separately exact unbounded variant, but should not be conflated with full elimination.

Freeze total numeric definitions on all inputs, with invalid m=0/r>=m returning false for the encoded decision. Require genuinely PR candidate/Boolean decision, concrete Phi and H endpoints, and actual quantifier semantics. The formula translation later can use a syntactic expanded Term made from max (encoded by cases), addition/subtraction/division/residue and actual inverse symbols. This first packet pays the arithmetic identity and computation; it does not yet pay arbitrary conjunctions, affine sums of several nonlinear terms, sign branches, whole-formula closure, negation-driven alternation or general QE.

Independent conceptual/exact scope review before proof. No source theorem promotion from this supporting packet. This is deliberately smaller than a purported full parameter solver, and its all-parameter semantics is stronger than fixed-valuation existential decision reuse.
