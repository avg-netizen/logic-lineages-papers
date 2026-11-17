# Independent candidate source review — raw application dynamics

2026-11-17. **Source semantics accepted; native proof gate pending.**
This is a source-first checkpoint review, not final mathematical adoption.
The target and comparator pins remain those accepted in `REVIEW-PREFLIGHT.md`.

## Candidate pins

Under `RawApplicationDynamics/`:

- `Proof.lean`: `d741d52f3cbfcde7e105d47e2a9ed51c4b6bd2dd3925c631c92caf0f4f6b627a`.
- `StatementChecks.lean`: `ccce5845fffbac3dc3cbafbb7ed96f8a91c1facfe88e2fd88f4ed0611f9f6ca1`.

The original step inversion yields only bottom, function-side reduction,
or literal beta contraction for an application. The finite-path induction
retains the original fixed argument and the unrestricted suffix after the
first root beta step. The converse uses original function-path lifting,
beta, path composition, and bottom; no new relation is defined.

Accessibility necessity reflects the original function-side steps and
transports accessibility along the actual finite prefix and beta step.
Sufficiency inducts on function accessibility while retaining accessibility
of every literal beta contractum reachable through a function path. It adds
no argument reduction, argument accessibility, typing, or quotient oracle.
The proof namespace contains nine candidate theorems: two endpoints and
seven helpers, plus two case-predicate definitions.

Both exact aliases retain the frozen target types. Comparator preflight
passed in coordinator receipt `build-reports/1794956369510745590-5.json`.
The 23-module candidate proof closure still requires its native gate,
standard-axiom audit, and source/receipt/log reconciliation. No internal ID1,
global accessibility, or full Paper6 result is accepted here. The reviewer
ran no compiler or Git operation.
