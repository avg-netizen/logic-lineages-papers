# Original path checker — frozen targets

Date: 7 November 2026, America/Chicago. Frozen before proof authorship.

The six exact targets specify all-input evaluation calibration to the literal
original `pathTest` and `positivePathTest`, and internal nil/cons acceptance
equations for one concrete Program AST. The original list of pair-coded
next-vertex and edge-certificate entries, decoder and path semantics remain
unchanged. Internal acceptance always means output one.

The summary uses zero for the empty suffix and an original cons cell containing
the first raw entry and the suffix acceptance value otherwise. It is computed
by the checked concrete raw-list recursor, with the target vertex retained as
a parameter. The finish program uses the original equality, conditional,
unpair, head/tail and exact-one conjunction ASTs.

The two external gates assume only all-input calibration of the supplied
original edge Program to the unchanged `numericEdgeTest`. All four internal
gates hold for every actual edge Program without a calibration premise. The
cons guard consists exactly of the original pairing graph for the raw entry
and original cons graph for the path. No decoder-success premise, semantic
reflection, extra induction operator or new calculus is introduced.

This is a supporting checker component for paper06 `lem:id1`. It does not
assert that the internal application-edge preservation rule, positive-path
lifting, or source-specific computability closure arguments are completed.
