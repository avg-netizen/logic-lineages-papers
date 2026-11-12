# Proposed role/type annotation and forgetting contract

Proposal only, before the next runtime AST or target is frozen.

## Encoding

An annotated job is `pair(role,pair(expectedType,rawJob))`, where the checked
raw job remains `pair(raw,pair(c,Gamma))`. Role zero means term, role one means
argument list; actual argument-list jobs carry expectedType zero. Other role
numbers remain total malformed data, with no typing claim.

The forgetting Program is the two successive right projections. It never
changes raw, c, or Gamma. The initial semantic annotation is derived from an
actual typed term's outer type or an actual typed argument list's role.

## Expansion without a new recursive evaluator

Reuse the checked raw expansion verbatim. Decorate its output jobs by index:
indices below the parent's actual raw arity are raw children, all later indices
are context deletions. This retains order, multiplicity and the checked child/
deletion boundary without rerunning any native syntax enumeration at runtime.

A bounded index scan over the actual returned list length can use the existing
lookup and append Programs. Decoration takes the parent annotations, parent
raw metadata, index, and the already computed raw job. It never modifies that
raw job. The child annotation table is:

* lambda: term at codomain(expectedType);
* application: first term at arrow(stored domain,expectedType), second term at
  stored domain;
* ordinary: argument list;
* numbered: BASE list, then extras list;
* argument cons: term at stored type, then argument list.

Deletion jobs copy the parent's role and expectedType exactly, including the
new bound-zero deletion in a lambda child's extended context. On inconsistent
role/raw combinations, the raw constructor still governs child count/order and
the table produces total numeric annotations. Such annotations are not claimed
to be well-typed. Numeric codomain extraction is the literal original type-tail
Program; actual typed lambda inputs prove it is the correct codomain.

## Exact contracts to freeze

1. Native calibration of decoration/annotated expansion to that explicit
   numerical annotation table on the exact raw expansion list.
2. Forgetting every output annotation gives EXACTLY the unchanged original
   raw expansion, not just a permutation or set inclusion.
3. On original typed term/list inputs, child annotations have the original
   constructor-prescribed roles/types. Contexts and c already follow the checked
   expansion and are not reconstructed independently.

Native typed deletion correctness can reuse actual prefix erasure to show that
copying role/type is legitimate at the deleted context; this must not become a
new source-validity oracle. The raw code projection of each typed erased term
is the existing eraseCode calibration.

## Boundaries

This is annotation of one expansion, not a typed scheduler integration theorem.
A later agenda-frame translation must retain return metadata and prove its
forgetful simulation as a separate step. No return transition, result-stack
invariant, evaluator fuel, primitive operation cost, internal class law, or
final canonical erasure cancellation follows merely from these native laws.
