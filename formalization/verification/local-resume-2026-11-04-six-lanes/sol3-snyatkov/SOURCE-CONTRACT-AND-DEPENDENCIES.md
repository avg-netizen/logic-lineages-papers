# S3: full Snyatkov endpoint and unpaid dependency chain

The current whole source target is paper08 `thm:snyatkov`, literally
`Th(Nat;0,1,+,<,Phi)` for the variable-seed hierarchy `Phi(n)=F5(n+100)`.
The exact first-order syntax, ordinary named binding/shadowing, numeric
encoding and all-sentence decision proposition are in
`SnyatkovCompletion/ContractDefinitions.lean` and `ContractTargets.lean`.
`FullSourceDecision` is an unpaid proposition, never an assumption or field.
`EffectiveExpandedElimination` fixes the stronger source Theorem2/Corollary2
route: an actual computable numeric program produces an equivalent expanded
quantifier-free matrix, preserving original free-variable membership.

## Direct primary-source reading

Read the original A.S.Snyatkov2008 PDF, pp40--51, from
`/tmp/l3-snyatkov-2008.pdf`, SHA256
`13f5ef161fa40d1bd24de131a0cbe450e9a51cf5a4b9514f5ee48bd2deb8019e`.
Original URL:
https://eprints.tversu.ru/id/eprint/494/1/19950136_2008_2_snyatkov.pdf .
The legacy glyph extraction is broken; the rendered primary pages were read.
The PDF and rendered pages are reading aids, not proof runtime dependencies.

Page40 defines effective compatibility, fixed-seed hyperfunction and floor
inverses with below-range zero. Pages41--42 give growth/inverse/collision and
unique-boundary lemmas. Theorem1 (pp42--50) builds existential normal form by
eliminating a negated existential block, preserving signed linear combinations
of shifted Phi, shifted Phi(H(...)), and variables. Theorem2 (pp50--51)
eliminates an existential block in the inverse-expanded language. Corollary2
asserts the construction is effective. These are separate mathematical stages;
neither follows merely from the hypotheses or a unary decision procedure.

Some internal lemma numbers on pp45--46 do not agree with pp41--42 (the text
refers to unique-boundary lemmas as6/7, where printed statements are5/6).
We use their actual mathematical statements, not those cross-reference numbers.

## Paid inputs, read without modifying

* Actual Phi growth, primitive recursion, uniform constant residues.
* `FixedSeedControlResidue`: literal H(0)=1/H(n+1)=Phi(H(n)), strict growth,
  primitive recursion, residues and period one at the literal modulus bound.
* `SignedShiftCollection` and `SignedPhiSeparation`: original signed domains,
  collection, exact source delta, actual leading/lower separation and programs.
* `SnyatkovInverse`: exact total Phi/H floor graphs, round trips, order,
  coefficient compression d(c)=c, actual bounded primitive-recursive searches.
* `SnyatkovHyperCollision`: actual inverse-based coefficient elimination and
  finite smaller-hyper-index collision bound with exact original signed domains.
* `SnyatkovDivisibility`: actual modular-atom finite-prefix/tail BASE compiler.
* `SnyatkovUnarySign`/`SnyatkovUnaryDecision`: complete unary finite-DNF decision
  with one shared input and all original signed-domain occurrences.

The current source audit and TARGETS register keep the whole theorem pending.
The common-head/balanced translators are already paid and are not rebuilt here.

## End-to-end dependency map

1. **Literal source/expanded syntax and coding.** Freeze actual source FO and
   expanded term/matrix semantics; prove coding, total numeric evaluators and
   substitution/support programs. New definitions fix natural subtraction and
   inverse defaults explicitly. Their numerical evaluation needs actual proofs.
   H is an actual recursive expansion: decision of the f-only reduct does not
   require first-order definability of H in that reduct.
2. **General normal-form introduction.** Translate arbitrary nested source
   terms/atoms to existential systems of source shifted unary summands, keeping
   shared names, signed domains, equalities and free-variable support. Convert
   arbitrary Boolean matrices to finite cases with exact quantifier behavior.
   Retain a finite occurrence list: the same original name may occur at multiple
   shifts, in multiple summands and in multiple rows. A one-triple-per-name
   reading of the primary display is not an admissible silent restriction.
   Any narrower normal form would need a proved source conversion first.
3. **Ordering and normalization of a quantified block (pp43--44).** Finite
   equality/order case split on the quantified variables; clear coefficients;
   expose one actual maximal summand and the signed remainders in every row.
   Variables occurring only linearly require actual Presburger elimination.
4. **Dominant-summand case (pp44--46).** Prove unique half-boundary and tail
   tripling for both shifted Phi and shifted Phi(H(...)); prove the exact
   finite boundary-window substitution, including initial-domain cases and
   absent upper bounds. Source Lemma2 and Lemmas5/6 are unpaid here.
5. **Close-summand case (pp47--50).** Pay all six pairs (Phi/Phi, Phi/hyperPhi,
   Phi/linear, hyperPhi/linear, hyperPhi/Phi, hyperPhi/hyperPhi). Reuse actual
   inverse compression and hypercollision. Each substitution must reduce the
   number of original quantified variables, keep all shared matrix constraints
   and have a literal effective finite output.
6. **Theorem1 induction.** Assemble steps2--5 into source-preserving effective
   complement elimination for an existential block, with a well-founded
   progress measure on its number of quantified variables/cases.
7. **Theorem2 boundary elimination (p51).** Replace the dominant boundary
   witness by actual floor-inverse terms (two adjacent possibilities), then
   assemble block elimination and arbitrary alternating-quantifier elimination.
8. **Decision and consumer assembly.** Prove the computed expanded matrix
   evaluator and code calibration; obtain `FullSourceDecision`. Only then join
   the existing source/common-head/balanced compilers to the whole solver.

## First current proof round: actual close-argument finite substitution

`WindowDefinitions`/`WindowTargets` isolate actual clauses from step5, rather
than another unary decision family. If Phi(B) <= Phi(A) <= c*Phi(B), actual
inverse compression gives B <= A <= B+c. Thus A=B+d for one d in0..c.
When A is the original signed argument x_i+e and B is any expanded anchor
omitting original name i, this eliminates x_i from an ARBITRARY Boolean matrix
under the SAME remaining valuation by exactly c+1 actual substitutions.

The anchor may use multiple other variables, actual H, inverses and nested
operations. It covers the variable-versus-variable and variable-versus-hyper
argument windows needed in source cases1/2/5. Every branch retains the original
close-comparison and signed-domain guards. This pays below-range and c=0 cases
without claiming a source convention for invalid negative arguments. The
output must remove i and introduce no new names. The complementary half-boundary,
linear/hyper collision and whole induction obligations above remain unpaid.

This round first proves the concrete finite construction's semantics/support.
Uniform computability of its numeric encoding is a distinct unpaid clause,
not inferred from semantic existence or substituted for the full solver.

Existing accepted source bytes, global register/root, manuscripts and Git are
owned by main and remain read-only to S3. Preflight compilation and immutable
hash pins must precede proof authorship. All native checks require main's
explicit slot grant and use the unchanged one-worker2048heap1536RSS2048free
90CPU180wall `scripts/check.py` profile.
