# Public cumulative continuation release — 10 November 2026

The user requested continued public-paper formalization after additional work,
through **10 November 2026, 21:00 UTC**. This release supersedes historical
pauses and expired cutoffs only for this public continuation. Preserve every
older instruction and checkpoint record. Private research and the separately
paused supervised Claude lane are not restarted.

- Continue the existing branch:
  `formalization/cumulative-continuation-2026-11-09`.
- Reconciled starting commit:
  `a89b703ffafd70b015aaed43daa3475c7d94b9b2`.
- Authoritative register: 171 checked, 2 inherited, 16 pending / 189.
- The latest mathematical checkpoint and next steps are in
  `verification/continuation-2026-11-09/function-neutrality/`.

Preserve all inherited mathematical sources, frozen targets, source domains,
semantics, quantifiers and effectiveness requirements. Freeze exact new
targets before proving them. Compile first, check the exact target and audit
the actual axiom closure. Only propext, Classical.choice and Quot.sound are
allowed. Supporting components do not promote whole numbered statements.

Native checks remain coordinator-owned and serialized through unchanged
`scripts/check.py`: one thread, 2,048 MiB heap, 1,536 MiB RSS, 2,048 MiB minimum
free memory, 90 CPU seconds and 180 wall seconds per compiler. Preserve locks,
source pins, toolchain and dependency pins, checker, manuscripts and CI.
No cold upstream compilation or independent author compiler is authorized.

Before native checks, install the git-ignored local stop policy with
paused=false and stop_at_utc="2026-11-10T21:00:00Z". At the cutoff, admit no new
proof, author, target or compiler work. Allow the unchanged checker to enforce
its stop, reap owned jobs, and preserve checked results, failed attempts and
pending drafts in an accurate handoff. Do not resume automatically.

This release/setup change is metadata only. It changes no mathematical source,
root import or register entry and performs no publication. It claims no new
theorem acceptance, full-root build or remote-CI pass. Any later publication
remains a separate coordinator action within the user's authorization.
