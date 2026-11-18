# Concrete proof of the frozen full Transitive endpoint

No endpoint change: RefinementSyntaxTargets.Transitive already freezes all
source and target terms, including marked ones and reusable whole-owner extras.

A naive recursor on the right witness is insufficient at abstraction: its
chosen name may occur in the left outer body. Instead use strong induction on
the right witness's explicit treeSize, with an induction hypothesis covering
all actual right witnesses of smaller count. Choose a fresh name above the
maxFreeName of all three bodies; synchronize both opened witnesses to it.
Right synchronization preserves count exactly, so the new opened right tree
still has count one less than the original right abstraction.

Base-list composition is positionwise and invokes this same strong induction
hypothesis on each actual right base witness. Extra-list composition retains
all actual At occurrence witnesses and permits reuse. For a right existing
extra q→s, select the corresponding left extra witness at that occurrence:
if left-existing, compose its q0→q tree and rebuild existing; if left-owner,
compose its retyped whole-owner→q tree and rebuild owner. Right-tree annotation
agreement q.type=s.type is proved from actual typing, not assumed.

For a right owner→s witness, retype the actual entire left marked refinement
to s.type and compose with that strictly smaller right whole-owner witness.
Every such tree contributes positively to extraSize and extrasSize, themselves
contributing to the original right treeSize. No lambda-spine-only measure or
unaccounted whole-owner shortcut is used.

Helpers return propositional existence of finite trees. There is no extraction
of computational Type data from a Prop proof; obtaining witnesses remains in
Prop goals. Retyping at the Type-witness level is constructed by inversion of
an actual marked tree, preserving all base/extra witnesses. No E, cut,
full-application associativity, or general substitution premise is introduced.
