# Independent final review — raw lambda dynamics

Decision: **accept both exact supporting theorems** on 2026-11-17.
The frozen source/type review remains in `REVIEW-PREFLIGHT.md`.

## Accepted source pins

All paths below are in
`LogicLineages/OrdinalComparison/TerminationOrdering/Continuation20261117/RawLambdaDynamics/`.

| File | SHA-256 |
|---|---|
| Targets.lean | b816a3cab57a4bbfe47d167080cdbea8c6397af741b4a7ab2fbf52f67944826c |
| ComparatorGate.lean | 5defb8dbdccea524def770215fdbf7a57dbd17c242f75f852fb113b6debbffd2 |
| Proof.lean | 8ad1a7bd5c15e48faf53a8b0b249c8ddea54c92543921ae015d4a87b185f5293 |
| StatementChecks.lean | 9512478bab5dbdbc0841235d609929487ff8b48b26c8d156c80df491bfb58ee6 |

The targets and comparator retain their preflight hashes. The final proof
uses the original mutual raw-step recursor for lambda inversion, original
raw-path induction for factorization, and ordinary accessibility induction
for preservation/reflection. The helper case predicates organize elimination;
they neither replace the original relations nor enter the public premises.
The one-line constructor qualification repair changes no theorem statement.

## Native evidence reconciliation

Independently read and reconciled root's final receipt
`build-reports/1794955088742244296-5.json`, SHA-256
`a7beb7627420d5300cfeeb81d3b3ea91135c2b57616dc743c7747312dd7d2aa8`.
All 18 recorded local source hashes match current source files; all rows have
return code zero and an available log. Sixteen rows are verified reuse from
this session's bounded checks; the proof and exact statement gate are fresh
successful rows.

The unchanged profile is one worker, 2048 MiB heap, 1536 MiB process-tree RSS,
90 CPU seconds and 180 wall seconds per module, with a 2048 MiB free-memory
floor. Maximum recorded RSS across this closure is 802,508 KiB; the newly
compiled proof uses 799,836 KiB. No full paper-6 or root build was run for
this acceptance.

Final evidence log hashes:

- Proof log, same receipt stem with suffix
  `-LogicLineages-OrdinalComparison-TerminationOrdering-Continuation20261117-RawLambdaDynamics-Proof.log`:
  `fcec89367d842d96ba211834c3ae24e3309f42720ad7271cd5b1ab40f0cfcb89`.
- StatementChecks log, same stem with suffix
  `-LogicLineages-OrdinalComparison-TerminationOrdering-Continuation20261117-RawLambdaDynamics-StatementChecks.log`:
  `0b821eab88496cc91827b40226d1984645359dcb6d17e87e047f2b7df8accf35`.
- Reused comparator log from preflight receipt `1794954950976448898-2`:
  `578d3233c2a8272fd6bbd93c8dc520ceb3168ef069abc858e204f3dbe8fb3c8c`.

The proof namespace audits 11 theorems, comprising the two main proofs and
nine helpers; each uses only `propext`. Both exact aliases independently
print and audit the same standard axiom closure. Comparator audits also
pass. No additional axioms or proof placeholders appear in the packet.

## Accepted mathematical scope

1. Every finite original raw path from a lambda ends at same-type bottom or
   at a lambda whose body is reached by the original finite body relation;
   both alternatives conversely produce the stated raw path.
2. A lambda is accessible for the original descending raw relation exactly
   when its body is accessible for the corresponding body relation.

The claims remain native raw-reduction suppliers. Internal ID1 derivations,
finite-quotient and final canonical-fold transport, substitution/fundamental
lemmas, global accessibility, the stable-pair source issue, and ordinal bounds
remain outside this acceptance. No numbered statement is promoted. The
reviewer ran no compiler and made no Git operation.
