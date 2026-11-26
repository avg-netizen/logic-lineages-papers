# Local Fable-pair continuation, round 2 — 22 November 2026 (evening)

User instruction (verbatim): "the external agent pushed its work, please fetch, summarize the findings,
then continue formalization". Fresh explicit release; lifts the pause set at the end of the earlier
round (`PRIOR-LOCAL-RUN-POLICY.json`). No deadline. Root re-pauses at the end.

- Baseline: `a14a93677` on `formalization/github-measured-install-2026-11-22` (the external agent's
  branch, one commit on top of `dd4eddff9`): supporting #1430–#1434, register 156/11, and
  `../github-continuation-2026-11-22/p17/CORRESPONDENCE-REVIEW.md`, which finds no material mismatch for
  the `thm:arithmetic` and `thm:ground` comparators and finds the `thm:main` comparator too weak
  (no uniformity in a supplied policy program; no joint computability in the near-control parameter).
- Parties and rules: as in `../local-fable-pair-2026-11-22/RELEASE.md` and `BRIEF.md` there, with this
  directory as the round home (`gate.sh`, ledgers, evidence here). Owner's standing notes: Lean is the
  validity check; second Fable instance through `claudep` as fresh narrow sessions (API credits are
  limited); two Opus 5.5 High subagents on assigned tasks.
- Aim: Paper 17 `thm:main` uniformity repair (the review's section 4), then Paper 16 from the
  installed carrier.
