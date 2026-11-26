# Next progress obligation: eliminate an actual inactive binder

## Source and current boundary
The primary Snyatkov proof, printed p43 before strict ordering, removes a variable without nonlinear occurrences by Presburger elimination and explicitly requires the matrix to retain the required shape. The currently implemented OrderedOccurrence tag1 exposes exactly an unfinished version of this obligation. Tag3 ordered-maximum continuations also remain unfinished. Neither is a decreasing branch merely because it has been enumerated.

Read actual NormalForm.Formula/Summand/guardedAtom and AdditiveParameterDecisionTargets. The additive decision endpoint rejects every Phi node and returns a Boolean for a supplied valuation. It is NOT parameter-preserving elimination of a linear binder in a matrix containing nonlinear terms in other shared names. It cannot be used as the missing theorem.

## Proposed next complete supporting endpoint
For an actual Formula p, name i, and proof that every nonzero nonlinear occurrence in p has name different from i, compute a quantifier-free formula E(i,p), with no free i, such that for EVERY shared valuation nu:

  E(i,p).eval nu iff exists n : Nat, p.eval (Function.update nu i n).

Require actual support containment in p.variables minus i, and derive the corresponding arbitrary Nodup-block existential equivalence with xs.erase i and exact one-name length decrease. Use this to replace a tag1 continuation by a genuinely decreasing outcome. Original domains, including zero-coefficient nonlinear occurrences, must be retained through the actual guarded formula; no global domain or new tail may be imposed. All Boolean negations and divisibility atoms must be covered, not only conjunctions of positive inequalities.

## Required implementation, not a caller oracle
1. Extract each row exactly as a_i*x + R_i, with signed a_i computed by summing every variable occurrence of i. R_i is the actual remaining finite signed row. Nonlinear i-occurrences with coefficient zero contribute zero numerically; their original syntactic domain guards remain separate rows in the original matrix. Show R_i is update-invariant using the no-live premise, without assuming syntactic i-freeness first. Then erase zero terms in R_i with a semantic/support proof.
2. Build a literal finite Boolean normalization and coefficient-normalization procedure for this ONE binder. Preserve nonlinear summands on other names as correlated parameter expressions, not separately existentially chosen values. Constants, coefficient zero, absent lower bounds and negated divisibility must all have explicit cases.
3. Implement one-variable Cooper-style elimination using the common positive multiple of nonzero coefficients/moduli, finite residue disjunctions and actual boundary candidates. The natural lower bound x>=0 must be represented during any integer-variable implementation and proved in both directions. Invalid modulus is not part of NormalForm (stored modulusMinusOne+1), but malformed raw input behavior must remain total and calibrated.
4. Prove finite candidate completeness, then literal substitution-back and normal-form closure. Any new modular modulus/coefficient is computed. Nonlinear parameter expressions remain the original expressions in the same original names. No arbitrary semantic decision oracle or supplied successful candidate list.
5. Provide genuine joint numeric program and exact syntax/code calibration. A semantic existence proof or a Boolean decision at fixed parameters is insufficient.

## Manageable staged freeze
First inspect existing actual linear elimination code for a reusable parameter-preserving transformer, not its advertised status. If absent, author the signed one-binder normalizer/candidate construction as the first exact definitions bundle and freeze the complete semantic/program obligations before proofs. Supporting stages may be checked separately, but tag1 is not marked discharged until the full endpoint above is proved.

The final block decrease only removes i. Tag3 still needs actual row partition, coefficient alignment, dominant-versus-close cases, runner-up completeness and closure. Arbitrary SourceFormula normalization, modulo normalization for nonlinear nodes, nested binders/negated existential closure and a global decreasing elimination algorithm remain separate. No full Snyatkov/common/balanced decision promotion from this packet.
