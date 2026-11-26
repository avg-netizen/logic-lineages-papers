# Paper 16 singleton substitution continuation, 25 November 2026

The continuation starts at `2391fb2434`, the GitHub tip of
`formalization/ii5-reconciled-main-2026-11-24` at branch selection. The local
branch is `formalization/paper16-continuation-2026-11-25`.

The previous checkpoint relates successful singleton-code computation on
numerals to raw certificate witnesses. It supplies the open typed-bound-node
dispatch as well, with a premise giving the computation of `boundInstance H`.
The new module `NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof`
attempts to discharge that premise for two cases using the actual program:

- With a derivation of `i < d`, the original bound-index field and depth
  projection feed the internal strict comparison. The successful selector
  retains the bound node and reports `suc (boundTerm t i)`.
- At index and depth zero, the strict comparison rejects and equality accepts.
  The zero depth selects direct insertion, with output `suc a` for the original
  replacement code `a`.

Both statements preserve the syntax-acceptance premises of
`exact_OpenBoundProgram`. The parameters and proof contexts are open
except for the two explicit zero arguments in the second statement. These
are arithmetic graph lemmas for the substitution used in the
[lambda case of arithmetic accessibility](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex),
where the manuscript also needs raw-step preservation or equality. The proof
of that open preservation, positive-depth shift, the lowered-index case, and
recursive traversal remain separate obligations.

Fable 5.2 High reviewed the public bound-node definitions in one API-first
`claudep` turn. Its response corroborated the comparison-composition route
and the zero-depth case. The repository's branch-introduction lemmas supply
the unused-arm computation by internal case analysis on total programs.
No host evaluation of open inputs is used in the new proof.

## Native status

The new module has not yet passed the native gate. The initial invocation
stopped at the free-memory floor with 1,851 MiB available (receipt
`1795662872823113667-10`). A retry timed out compiling
`DirectMultisetPresentationDefinitions` after 180 seconds wall time and
1.77 seconds of observed CPU time. The worker was waiting on a file page
(receipt `1795663047024213075-10`). Neither run reached a new declaration
or its axiom check. These receipts are in the worktree's `build-reports/`.
The isolated rerun of `DirectMultisetPresentationDefinitions` passed in
138 seconds (receipt `1795663265927575310-10`). The full rerun checked 31
dependencies including that cache hit, then stopped at the 180-second wall
limit on `SourceTypeSupportDefinitions` with 2.0 seconds of CPU and another
file-page wait (receipt `1795663453930512524-12`). Both new declarations and
their axiom audits remain pending.

```sh
python3 scripts/check.py --timeout 180 --cpu-seconds 90 --memory-mib 2048 \
  --rss-mib 1536 --min-free-mib 2048 --threads 1 \
  LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof
```

The current register on this branch has 160 checked and 7 pending.
