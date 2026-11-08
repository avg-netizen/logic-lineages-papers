# Checked: parameter-carrying original numeric iteration

All **seven unchanged frozen targets** passed exact aliases and actual axiom
checks. The final gate is `build-reports/1794152490593227063-6.json`.
All **48 own declarations** were audited; only propext, Classical.choice and
Quot.sound occur. No frozen specification or original supplier was changed.

For one arbitrary binary AST P with inputs [value, parameter], the actual
unary carried step forms pair(left state, P(right state, left state)). The
actual ternary iterator takes [count, value, parameter], starts from the
original pair(parameter, value), uses the unchanged numeric iterator, and
returns its original right coordinate. Its all-natural-input evaluation is
exactly iteration of P at the same parameter.

Inside the original calculus, actual pair graphs give the carried-step iff.
Full-language natural induction preserves the actual left-coordinate graph
at every symbolic count. This recovers the complete carried output before
transferring zero, front-successor, addition-fusion and fixed-point laws.
Every positive operator body, context, and symbolic term remains arbitrary;
all laws keep the same parameter. There is no evaluation-to-derivability
reflection, interpreter, new primitive, or numeral-only specialization.

The proof/preflight closure has **1,078 current-source-matched local modules**
with successful module rows across **19 immutable native receipts**.
Successful rows remain valid when a later module in the same run failed. All **1,071 broader frozen Lean
inputs** have successful source matches, all **1,080 frozen/prerequisite pins**
match, and both selected pinned upstream source files are unchanged.
Peak successful component RSS was **1,105,868 KiB**, under the unchanged
1,536 MiB cap. There are no current component warnings or axiom failures.

The sole compiler slot was **released at 2026-11-08T15:41:49.010217+00:00**.
All ten native sessions completed; both actual shared locks were verified
free. Failed module outputs from four partially failing attempts are
unaccepted; their module rows and native logs/receipts remain retained.
Successful source-matched rows from those runs are included where applicable. No resource limits, frozen targets, or original sources were changed.

Next: independent postproof review and coordinator adoption if accepted.
This is a prerequisite for a future parameter-threaded canonical pipeline.
Parameterized descent and uniform fold/path correctness are not proved;
existing fixed-window proofs do not automatically generalize. Unqualified
CertifiedApplicationLift, remaining computability/constructor/lambda/
substitution arguments, and all-term accessibility remain outside this
packet. No numbered source promotion, Git action, full-root build, or remote
CI is claimed.
