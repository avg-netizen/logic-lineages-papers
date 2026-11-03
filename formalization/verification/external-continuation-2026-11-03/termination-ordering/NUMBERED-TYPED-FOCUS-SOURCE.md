# Executable focus in actual typed numbered contexts

Finite paths name only lambda, function-side application, ordinary base indices, numbered base indices and numbered extra indices. Traversal returns an actual hole binder context/type, the actual typed hole term and an accepted one-hole context. Under a lambda it recurses at the actual extended binder context; mismatched constructors and out-of-range argument indices fail. Unchanged siblings and full original type/head data remain in the context. There is no application-argument positive position.

A structural index helper receives only the actual recursive focus on a shorter path from the executable caller. No external visitor or leaf oracle is a premise of any target. Focus termination is by path length, with argument traversal by decreasing index/list; empty paths return the literal hole.

Four targets require exact reconstruction of the original term/argument list on success and coverage of every accepted typed one-hole context. Coverage requires literal equality to the record containing that same context and supplied hole term, not merely an existential approximation. All binder/type identities are explicit in that equality. No step or universe condition is assumed or inferred here; the later checker must decode its root witness at the returned hole context and discharge actual step obligations.

This is not full recursive certificate completeness, arithmetic representation or accessibility, and does not change any original ordering rule.
