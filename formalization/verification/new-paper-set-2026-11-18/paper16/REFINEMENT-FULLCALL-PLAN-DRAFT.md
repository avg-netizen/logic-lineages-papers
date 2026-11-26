# Draft route for actual original-spine full-call reflection

Remaining exact endpoint is RefinementSyntaxTargets.FullApplication, unchanged:
actual refinement q→s, positionwise related typed argument tuples as→bs, actual
successful full call apply s bs=some r, imply actual success apply q as=some p
and refinement p→r. No staged/full associativity is available.

Candidate route for review: use fresh distinct symbolic free-variable tuples,
with names absent from both original terms and all actual argument values.
Construct two typed free maps sending each symbolic typed name to its paired
argument, identity elsewhere; the positionwise witness gives pointwise map
refinement. Prove this construction with duplicate types/occurrences handled
by distinct names, not by a set-level argument.

First prove a symbolic full-call reflection lemma on the actual original
spine. Original variable blocking is unchanged by symbolic free variables.
Lambda consumption is literal opening by a symbolic variable, and only the
original residual head is inspected. Prove symbolic successful shape from the
actual successful right call; no assumption that introduced lambdas are
consumed. Head/marked residual calls append the entire remaining symbolic
argument tuple once, after substituting the consumed symbolic binders.

Extra-list append preservation requires a real lemma: old existing suppliers
retain At occurrences; old whole-owner suppliers are composed with genuine
refinement from the new owner with appended extras to the old owner, using
already-checked refinement transitivity. New supplied extras use exact At
positions and the paired argument refinements. Omitting extras must be proved
from the actual refinement constructors, not assumed as an oracle.

Then use actual success-only FreeCall covariance with each map. Because maps
fix both original terms, they map each symbolic successful call to its actual
full call. Apply the two-environment refinement substitution theorem to the
symbolic output relation. Right output equals the given r by deterministic
Option.some injectivity. This is covariance of one full call, not composition
of staged calls; the known λx.x full/staged failure witness remains untouched.

This is a draft strategy, not a new frozen theorem or proof claim. Need exact
symbolic tuple/shape targets and independent scope review before authoring
major helper statements. If source or typing makes direct binder-block
presentation smaller, retain the same actual full-call endpoint and review it.
