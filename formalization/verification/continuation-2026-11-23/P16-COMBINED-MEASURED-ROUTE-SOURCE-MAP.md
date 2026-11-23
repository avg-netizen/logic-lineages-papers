# Paper 16: exact combined route with one installed measured exchange

Base checkpoint: `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9`.
This is supporting source for the measured branch toward #1422, not
numbered promotion or a decision to change the previously checked
unmeasured evaluator. The historical `combinedPrograms` record has
exactly V, R and W; its cover is derived and its X is always selected
by clients separately. The new route has exactly that *same* source
record, and computes the following on the same settings/original base:

- original `thinMatchingWindow P.cover s P.W P.V`;
- original directed candidate, measured by `selectedMeasure P.R`,
  then paired and cover-guarded, in that order;
- the true `edge4`, round graph and packed least on the one installed
  exchange and one original window. There are no independent exchange
  slots for these three clients.

Exact edge preservation is instantiated from #1401 and a measured
edge erases only to a true paired-unmeasured edge. Conversely, a
true paired-unmeasured edge can be *upgraded with two actual reports
of the same selected measure*. This recovers the (a,b) and (b,a)
tests, original two endpoint windows, and the original accepted cover
comparison from the same tape; no external cover report is added.
The exact finite round on the installed program carries the actual
application least, using #1421, retaining both original type guards
and the original argument window.

No claim of numerical equality of an old and new round or least,
or of class equality just from unmeasured graph reachability. The
application existence/domain lane is disjoint; no least-existence
assumption is silently removed here. Gate
`LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteChecks`.
