# Source plan: actual atomic positive refinement and fresh same-body closure

Plan only, not Lean comparators/proofs or native evidence. Intended
continuation of Paper16 ordinals.tex 112–127, using the new selected
actual packed fresh/literal typed block and given-u carrier alignment.
Whole variable/bottom/neutral application computability remains open.

## Literal old and chosen interfaces

Old numerical predicates are exactly
`NumberedWindowConcreteCheckers.step xs s`,
`NumberedWindowPresentationCheckers.checks xs s`, its literal
`positive = addressRS step (least s)`, and its scalar bit `scalar s`.
The selected certificate AST consumes exactly [source,witness,target].
`data i j r d` adds the original fixed context parameter c in the
original declaration; the proof must never reassign the internal
certificate as a source/target operand. Here `r` is the old positive
Program3, `d` the unchanged direct Program3, and p the same actual
chosen original application guard, not an extensional replacement.

Use the shared actual sparse envelope AST, with these exact shape views:

* Address shell: tag 3, precisely [rawPackedContext,result,least].
* Free leaf inside that shell: raw **term** tag 0, exactly [type,name],
  with actual equality of this stored type and the shell result.
* Bottom leaf inside that shell: raw term tag 3, exactly [type], with
  the same equality. Outer tag 3 by itself does not mean bottom.
* Malformed, other tags/arity, nonmembers and type/annotation mismatch
  either fail the respective physical test or remain in the other
  branch. The literal atom test is structural; it is *not* a substitute
  for `addressView`, `contextView`, `typeBit` or `scalar`.
* Construct expected bottom via the original field-cons polynomial:
  `packNode 3 [rawPackedContext,result,packNode 3 [result]]`. Lift the
  very same physical context/result of x, not a decoded replacement
  list or fresh prover-selected code. Equality test compares with
  the same original target y.

Proposed actual arity-three AST, preserving the old programs as leaves:

    r′ := branch freeSource
            (branch bottomSource r zero)
            (andOne r (andOne literalBottomTarget (scalarAtTarget i)))

All branches see the same [x,w,y]. `freeSource`/`bottomSource` are
lifted from x, never from w or y; `scalarAtTarget i` calls the actual
same i on y. `andOne` and `branch` are the existing exact normalized
original AST combinators. Free and bottom recognition are disjoint by
the source term tag, yet may use separately compiled ground tests.
An accepted free output reports genuine target equality *and* carrier
checker on y. An actual bottom source rejects. The variant is chosen
as an actual Program AST; no transfer of arbitrary old object
derivations across numerical equality is proposed.

## Source-exact numerical contracts before any selected-object proof

1. Literal original raw projection/recognizer calibration everywhere,
   including sparse gaps, wrong arity, wrong tag, invalid payload
   and type mismatch. The target emitter must agree on all raw
   packedContext and raw type, not just well-typed contexts. Separately
   show physically canonical source addresses report their same raw
   slots when original addressView returns success (pack-of-unpack).

2. Original concrete raw atomic callback behavior with arbitrary
   x/w/y encodings and actual `Entries`, not a new reduction
   relation: an accepted `ConcreteCheckers.step xs s Γ t` from
   `packNode 0 [t,n]` lands on `packNode 3 [t]`; its step from the
   latter is always false. Justification to formalize:
   * Root certificate tags 0..6 all require source tags 4,5,6
     (against raw free/bottom 0/3). Tag 7 is actual bottom root
     and guards against reflexive source==target. On both atoms
     annotations read the same literal t.
   * A context step only enters raw source tags 2,4,5,6. For
     a free/bottom raw term the first proper-context tick cannot
     descend. Raw tick terminal none is absorbing; with fuel zero
     the original run rejects, and any accepted root branch keeps
     its actual explicit given certificate.
   * No claim that a free redex always admits a particular malformed
     t/name/cert. Positive implication retains window/syntax truth
     and gives admitted same-context/type bottom when it accepts.

3. Singleton behavior of the **same original** least calculation,
   for both free and bottom raw leaves, independently at all actual
   `Settings`, contexts/types and raw caps: no original exchange
   edge starts or lands at the leaf because outer tags must agree
   and exchange parts has no accepting case at raw 0 or 3. Prove
   backward singleton (least s Γ t q = some atom ⇒ q = atom) and
   forward singleton (least s Γ t atom = some y ⇒ y = atom) by
   exact finite `members/rounds/advance` and min membership.
   No total least assumption; a leaf missing from the pool can
   still give none. Neither arbitrary Settings symmetry nor
   an unchecked equivalence relation is needed.

4. Full original positive class path on all raw [x,w,y]. Original
   success gives valid addressView for x/y, same decoded context and
   type, nonempty witness field list and accepting fold. None stays
   none. If source leaf is free, first successful hop reports raw
   predecessor whose least is that exact free leaf, so step 3
   identifies it; actual raw step then lands on literal bottom.
   Forward singleton identifies the reported least. A nonempty
   suffix cannot start from bottom, by the same backward singleton
   and no bottom step. Therefore actual target y equals the literal
   same packed-context/type bottom address. Its scalar bit is true:
   actual step window gave admission of the bottom raw target,
   the accepted least result is literally that bottom, and actual
   target addressView has the same context/type/least. A bottom
   source cannot even start a positive path. This argument uses
   the *original* nonempty positive path, not direct edges, a
   semantically equivalent arbitrary typed graph, or source-only
   least idempotence on arbitrary malformed Settings.

5. Exact executable calibration: for every x,w,y, exact evaluate r′
   equals original positive toNat given the original r/i calibrations.
   The false original bit stays false even if an invalid address has
   superficially atomic shell fields. When source is not recognized
   as either atom, evaluation remains the original r literally.
   Mismatched result/payload annotation is the other case; mismatch
   of decoded source/target context or type already rejects in
   addressRS. A positive recognized free must pass the added exact
   target/equality/i checks by claim 4; a positive recognized bottom
   is impossible by that same original-source claim. A final tuple
   must **prove** claims 1–5, never assume a supplied preservation
   predicate. Numeric contracts may be independently staged before
   actual AST transport and open evidence.

## Open contracts and actual same-d′ final tuple

* At arbitrary open terms and body/context, a genuine arithmetic
  equality to the literal packed free (or bottom) source gives
  actual recognized tag/arity and source raw context/result graphs.
  Build these through the same selected sparse cell/envelope graph,
  actual arithmetic equality transport and real equals-one branch
  operations, not `evaluate` of open terms.
* Actual output-one r′ at the literal free source gives genuine
  object equality of its **same y** to the exact bottom emitter value
  and a genuine graph i(y)=1. Actual r′ at the literal bottom is
  impossible, using the real branch rules and tag disjointness.
  Prove that graph also equals canonical `certificate` for the new
  data through the existing literal coordinate rules; do not change
  the witness or context parameter.
* For a concrete final packet, choose the exact same prior #642
  i,j,r,d,p/a/h, then put actual `refined i r` in the new `data`
  and nowhere else. Prove `Evaluates` again with exact claims 1–5;
  obtain fresh `Interprets` via the existing
  `InterpretsEvaluatingPrograms` supplier. Use the same original
  generic Rules theorem instances at this new Data (equation,
  carrier, successor, certified, intro). Re-prove `InputGuards`
  at the new Data: its supplier quantifies over every actual body,
  and its two *scalar* carrier formulas only mention i, not the
  changed r. This uses a structural identity of the carrier
  formulas and a fresh instantiation at the new body, not old
  `sourceBody` transport. Preserve p/a/h, all original calibrations,
  fixed `ValidWindow` interface, guarded uniqueness and literal
  parse/typed shape. Instantiate #641 actual arbitrary-Data #611
  totality and the new alignment theorem directly at the new d′.
* If claiming actual I, separately pay the open original edge-to-
  certificate existential/renaming bridge *at new data*. Bottom
  with carrier gives I via the actual Rules and vacuous
  successor premise; free with carrier gives I via that bottom
  proof and the actual added i/target evidence, same context/type.
  Ground-domain fresh C is then just the original base I formula.
  Do not assert full FreshVariablesComputable or compute higher
  arrow C from I; neutral application, function-side closure,
  pullback for new r′, same-object original context decoding,
  numbered theorem and BH comparison stay separate.

## Gate staging and resource discipline

Use additive modular roots, not the stopped fixed-S,K legacy mixed
assembly. Keep original `ValidWindow` explicit for eventual selected
tuple while separate #627 retains literal original specialization.
Candidate stage boundaries: numeric literal atom/step; numeric
least/positive transport; literal refined AST/normalization; genuine
open recognized atom graph; actual same-d′ selection, and optionally
atomic I only after all actual edge/certificate prerequisites
preflight and pass. The legacy external symbolic variable/class
proofs are scope references only; they do not pay open graphs or
justify bypassing the exact current source evaluator. No cap increase
or unchanged retry proposed. No comparator/proof/native work done
for this plan.
