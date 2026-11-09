# Fixed-program numeric computation certificates

The source HB3 route needs a numeric proof constructor that can be represented
by an installed PR program. Existing numeralCalculation returns Nonempty
Hilbert derivations separately for each input. Numeric proofEquivalence then
returns an existential certificate, without establishing a primitive-recursive
selection. The new target closes precisely that gap for each fixed PR AST.

Registry/program/occurrence precede the generator. A uniform PR evaluator of
arbitrary PR ASTs is neither requested nor available. The target preserves
sorted formulaCode, certificateNumber on original List Line, original registry
node equations and the original checker. No new proof rule is permitted.

The intended proof follows numeralCalculation's AST induction. Construct raw
Line macros for logical/equality reasoning, axiom specialization and actual MP
and generalization, with primitive-recursive raw constructors. Base nodes use
one defining equation. Composition joins child certificates and equality
congruence. Recursion uses primitive recursion on the first input to join its
previous certificate with base/step calculations. Program evaluation is PR
for each fixed AST and is already proved so externally.

The resulting external generator still does not establish INTERNAL universal
checker acceptance of its output. A later symbolic verifier proof using the
actual installed registry equations and source PA induction is required for
HB3. No theorem/register/source-collapse completion follows from this target.

## Concrete certificate-family interface

For any fixed Primcodable input type alpha and fixed object context n, retain
both a formula family with primitive-recursive RAW prefix encoding and a
primitive-recursive numeric certificate family accepted by the original
checker. The existing numeric MP/generalization theorems close these families;
no new proof-checker correctness theorem is needed for those operations.

A logical axiom family is effective whenever its existing logical annotation
is effective: the accepted logical compiler computes its exact conclusion,
and certificateNumber of its singleton logicalLine is primitive recursive.
Each fixed registry equation has a CONSTANT accepted certificate. Therefore
axiom specialization needs only repeated existing allInstantiate annotations
and MP, rather than a new effective enumerator for the entire registry.

Primitive raw formula/term substitution already exists. Mathlib's
Primrec.list_ofFn and Primrec.vector_ofFn build the finite input dictionaries
from component families. Substitution-code exactness turns their primitive
raw output into the required typed instance. Closed lifting preserves the raw
term prefix and should be handled symbolically, without expanding numerical
Gödel codes.

Equality transitivity uses equalityReplace with matrix (lift(t)=var0) and two
numeric MP operations. Term congruence uses matrix
(lift(instantiate(f,t))=f), equalityReplace, reflexivity and MP. The accepted
call-congruence proof then lifts component input certificates through the
fixed call-term skeleton by term induction. All annotation families are
computed with the same raw syntax operations above.

Composition of a fixed program joins its fixed defining-equation instance,
child certificates, call congruence and function certificate. Primitive
recursion on its FIRST natural input retains the previous numerical
certificate; the base and step follow the original numeralCalculation proof.
The step's recursive result value is evaluate of that SAME fixed recursion
AST, whose external primitive recursiveness is already accepted. No uniform
AST evaluator or guessed per-input proof is substituted.

## Runtime occurrence-tag refinement

The producer's occurrence tag must be an input, since installing its own PR
AST can shift the verifier's registered tag. The stronger NEW TagTargets
therefore fixes q before choosing the PR producer but quantifies the ambient
registry p and occurrence tag afterward. produce(tag,inputs) generates
certificates using only the fixed q node equations at tag+localOffset, so it
never evaluates arbitrary program ASTs. The ambient registry enters the
correctness proof through actual occurrence membership, not the producer's
computation. This removes installation circularity without changing or
invalidating the weaker fixed-registry target or any queued source bytes.

The earlier constant-axiom-certificate simplification applies after fixing an
occurrence tag. For the stronger runtime-tag target, generate the CANONICAL
singleton original axiomLine certificate for each of q's fixed node-equation
families instead. Its raw equation code depends primitively on tag and the
fixed node skeleton. This is still finite node-wise syntax generation, not a
new generic registry enumerator or a selection of arbitrary per-input proofs.
When later proving internal correctness at the actual installed tag, each
such source equation/canonical axiom certificate is a closed constant leaf;
its actual same-registry numeral verification must be supplied explicitly.

## Tag-dependent intermediate certificate checker

A single ambient-registry checker cannot certify ALL runtime tags; only real
occurrences satisfy the final target's premise. The certificate-family algebra
therefore permits an axiom-checker FAMILY, applied separately at each runtime
datum. No primitive-recursiveness hypothesis on that checker is used by the
numeric logical/MP/generalization operations.

For fixed q, use the finite recursive list of its node equations at the
runtime root tag and the existing literal child offsets. The intermediate
checker recognizes that list. Child lists are included by construction; at
any actual ambient occurrence, subtree lookup proves that EVERY such equation
belongs to the original registry's equations. Ordinary numeric checker
monotonicity then transports the SAME generated certificate to the actual
registry checker. This is an auxiliary source-subset proof, not an extension
of source S/D, a new checker encoding or an assumed equation supplier.

Runtime-tag call congruence must avoid recursion on the numeral AST of tag.
Use reflexivity for the runtime tag numeral in the header, the already paid
literal pair/tuple header structure, and effective add/mul/U congruence.
This keeps the complete producer primitive recursive in tag and inputs.
