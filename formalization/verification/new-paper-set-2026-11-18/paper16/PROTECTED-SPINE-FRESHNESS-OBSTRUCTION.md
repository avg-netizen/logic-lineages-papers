# Same-family opening independence: obstruction and precise boundary

Read against actual HereditaryDomainSemantics.Valid, MarkedFamilyCoherence.Coherent/InputLE, and decision.tex structural interpretation. This is a mathematical counterexample design, not a compiled theorem or a change to any frozen carrier.

## A retained family can distinguish fresh ports

Correction after independent source-budget review: the original version used identity as the entire target with two slots. That is permitted by the generic Environment interface but does not instantiate the manuscript budget B = lambdaDepth(target), which would be one. Preserve this distinction; the source-compatible witness is instead as follows.

Let o be ground, I = lambda x:o.x, J = lambda x:o.lambda y:o.y, and let h have declared argument list [o→o, o→(o→o)] and result o→o. Take the closed ordinary target h(I,J), and the closed ordinary source lambda x:o.f, with nullary f:o. Both endpoints have type o→o. Then V=[] and the actual target depth B=2. I occurs at external binder stack [], and its body bound o 0 occurs at stack [o]. Set Gamma=[none,none], Gamma0=[some o,none], Gamma1=[none,some o], and Omega=[some o,some o]. The literal names are portName [] 0=1 and portName [] 1=2. Thus the actual ground observations contain free o 1 at Gamma0 and free o 2 at Gamma1, and both at Omega, by the body occurrence and the two allowed reused-slot assignments. The lambda I itself is an observation at Gamma. Take K from the actual source/target declaration support and subtype closure; it contains o and both declared arrow types. There are no base inputs for f and no source-body free names.

Define a semantic ground value G whose availability and strict bits are false, and whose weak bit at every context is true exactly on the literal free typed name of slot 0. There are no nonempty full prefixes of ground, so all three Valid clauses about application coordinates are vacuous. Consequently the already proved unconditional EncodeDecode supplies an actual retained ground code g at the empty context, with these exact weak bits at every extension. In particular, at the context with both slots occupied the slot-0 and slot-1 observation bits differ. Neither hereditary (N) nor validity compares these distinct weak coordinates.

For every type sigma select an actual root carrier code c_sigma: g at ground, the actual whole bottom otherwise. Define the family output at parameter (head,sigma,Gamma,base,extras) to be `restrict empty Gamma c_sigma`, ignoring base and extras. This is not an oracle: existing global restriction supplies actual output membership; actual code reflexivity gives input monotonicity; actual restriction composition gives exactly (C). The proved family EncodingComplete therefore represents this semantic family by a retained family code M. No extra equivariance condition is present in that theorem or its filter.

Now compare source `lam ground (marked f ground nil nil)` against target `lam ground (bound ground 0)`. Opening at slot 0 reads M's ground weak bit at the literal slot-0 variable and obtains true. Opening at slot 1 reads the distinct slot-1 bit and obtains false. Both source-body freshness requirements hold, both target openings are legitimate, and both can be embedded in the common extension with the two slots occupied. The source body does not use the bound variable, so the assigned port value cannot cancel the distinction.

## Why the suggested proofs cannot work

A common extension preserves the slot-0 coordinate and separately preserves the slot-1 coordinate. It does not identify them. Renaming M transports g's distinguished bit to the other coordinate; that proves a statement about a different family, not invariance of this arbitrary M. The distinction is permitted by all frozen carrier/family contracts. Strengthening M to be equivariant would narrow the already accepted source carrier and is not authorized.

Thus the plan's proposed independence of fresh opening choice at the SAME arbitrary retained M is false. It must not be frozen as a theorem, assumed as a hidden premise, or justified by (C).

## What this does and does not refute

This directly refutes same-M choice independence, not automatically every canonical structural interpreter. A potential alternative is to define the opening port solely from the actual observation context Delta and its domain, uniformly across the entire construction. In a Value at root Gamma, the field at Delta would use Delta's canonical choice, not Gamma's choice. Restricting the value to Theta still reads that very same Delta field for Delta extending Theta. Consequently a root-dependent-choice discrepancy need not arise in the weakening theorem. Locally nameless source syntax can also avoid syntactic bound-name renaming of M.

But that alternative is only a design possibility, NOT a proof of the printed full lemma or adequacy. It needs separate independent review of (i) finite budget and choices at every observation coordinate, (ii) capture-avoiding substitution under the same chosen port, including all environment images, (iii) the four operator tests and their (C), and (iv) how later adequacy reconciles arbitrary syntactic fresh-name witnesses. It cannot claim same-M opening independence. Restricting attention to equivariant bottom iterates might be useful for adequacy, but does not establish a theorem for all retained M or the printed endomap on that full carrier.

No new definitions, frozen targets, carrier edits, or native runs have been made for this investigation. Request a decision on the exact source interpretation of canonical openings before proceeding to freeze.

## Source conclusion after review

The printed lemma does not state arbitrary same-M opening independence. This witness refutes that extra proof obligation we proposed, not the printed structural interpretation lemma or least-fixed-point adequacy. A canonical coordinate-local realization must still prove their exact conclusions. See PROTECTED-SPINE-CANONICAL-COORDINATE-PLAN.md for the proposed proof route without M invariance.
