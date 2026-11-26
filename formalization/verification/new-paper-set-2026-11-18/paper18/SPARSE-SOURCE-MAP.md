# Current18 sparse peaks: exact source correspondence

Source is paper18 `u:lem:sparse`, identities.tex50–64, together with its
explicit preceding terminal identity and foundations/control definitions.

- Domain: every infinite actual alpha<epsilon0 with norm t>=2. This is
  `a < epsilonZero`, `omega0 <= a`, `2 <= actualOrdinalNorm a`; no finite
  head restriction or notation oracle.
- Control: foundations fixes f=G=F5(n+100), with F0=2^n and Fj+1=Fj^[n+1](n).
  The reused `ControlDefinitions.Phi` is literally this definition.
- Norm: actualOrdinalNorm is actual hereditary CNF recursion, charging full
  finite coefficients times one plus exponent norms, exactly the new norm.
- Collapse: actualCollapse is actual ordinal well-founded recursion taking
  max of zero and successor collapse values on norm-bounded strict predecessors.
- L: actualReplacementCount counts ONLY nonfinite greedy replacements, stopping
  at first finite state. actualDescentStep uses the actual LIMIT PART and budget
  Phi(norm of the full current state), not the whole state as predecessor bound.
- Z: actualTerminalValue is the first finite state. Its old independent
  decomposition proof yields Z=Phi^[L](t). The new expanded target identifies
  it with Phi(s), s=Phi^[L-1](t), and includes the printed count and gap chain.
- Final clause: arbitrary u<s implies Phi(u)<=Phi(s-1); no extra distinctness
  premise is needed because strict control monotonicity makes u<s sufficient.

`SparseTargets.SparsePeaks` repeats the exact complete proposition rather than
introducing a provider field. The historical `Targets.ActualSparsePeaks` and
`actualSparsePeaks` are candidates: source comparison finds no changed clause.
Current mathematical semantics are shared only where their definitions match;
old07 provenance labels do not change these literal definitions.

The printed lemma has no effectivity assertion. Noncomputable actual ordinal
recursion is therefore not a weakening of it; other new18 effective algorithms
remain entirely separate. This does not transfer other07 or18 statements.

Before promotion: independent frozen-target review, native current exact alias,
actual standard-axiom audit and recursive source-matched dependency evidence.
No compilation or status promotion has yet occurred for this current gate.
