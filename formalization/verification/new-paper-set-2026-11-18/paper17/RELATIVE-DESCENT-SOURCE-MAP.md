# Relative actual maximum and full affordable entry recursion

Source: entries.tex eq:affordable-tail, eq:relative-norm and eq:relative-descent.
Definitions use actualMaximumPredecessor and actual descentWith, ordinary ordinal
addition/subtraction throughout. No relative candidate oracle is assumed.

RelativeMaximumSpec proves actual M(mu+rho,b)=mu+R and R is greatest among all
relative y<rho of cost N(y)+s_mu(e(y))≤b, including own membership. N(mu)≤b
is exactly affordability of relative zero. No restriction on candidate leading
exponents or absorption is imposed; checked RelativeNorm supplies full cost.

RelativeDescentStep proves exact limit-part translation and absolute step
conjugacy for mu limit-or-zero and nonfinite y. Its budget is literally
f(N(mu+y)); affordability is explicit for this generic one-step theorem.

RelativeEntryRecursion derives affordability/orbit facts at the actual source
initial tail for both concrete selected controls. It proves existence of a genuine
FirstEntry tau (not assumed), initial delta+t-N(lambda), reconstruction of all
states through tau, exact norm budget f^[i](t), relative norm bound, first finite
iff i=tau, and exact next-maximum recursion at every i<tau. delta is the source
nonzero limit gap satisfying mu+delta=lambda. The zero target is included.

Dependencies: checked EntryExistence/FirstEntry, TerminalSemantics, full control,
full arbitrary-absorption relative norm, actual bounded maximum correctness.
No new suppliers/assumptions replace those. Generic one-step scope is stronger
than selected-control scope, but concrete orbit theorem remains explicit.

Supporting only. Propagation, gap/input, thick block, equal-gap certificate,
threshold, closed arithmetic and main comparison remain excluded.
