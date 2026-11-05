# Actual numeric recursion

The frozen algorithms recurse on the original radix-four term and radix-five
source formula codes. Numeric child codes are strictly less than their parent.
A graph node consists of the actual finite name/value list and original code.
Term children retain that list. Formula scope tests extend the active binder list
with the original binder name; formula freezing retains the ambient value list.
Repeated and shadowed binder names are never deduplicated.

The owned graph and assembler proofs use the exact existing finite decreasing
graph theorem in BalancedBoxEvaluationGraphProof. No assumption that a recursive
function is computable is supplied. Assemblers use already proved actual source
term evaluation, finite list access, the literal code constructors and actual
additive decision. The evaluator's default-one table is explicitly padded with
the desired default-zero ambient values through all term support.

The independent semantic stage's exact fragment boundary remains unchanged.
Bound-dependent Phi is rejected; nested Phi involving only free parameters is
computed by the actual source evaluator. Arbitrary additive binder alternation
and original shadowing remain present after freezing.
