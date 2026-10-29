# Formalization programme

Local workers are **paused for an external-agent takeover**, as requested on
29 October 2026. The [handoff](formalization/EXTERNAL-HANDOFF.md) records exact
continuation points and optional outside material.

Formalization has started for **all fifteen papers**. The programme is
in [formalization/](formalization/README.md), with an explicit
[paper-by-paper target register](formalization/TARGETS.json).

The register covers the complete manuscript input closure: 178 numbered
theorem-like statements, together with algorithmic and cited-supplier
obligations. Most full targets are still pending. The existing
[calculator formalization](04-pure-r1-calculator/FORMALIZATION.md) remains
the established checked baseline; its coverage is documented separately.

Codex authors and freezes independent comparison statements before Claude
proof work. Candidates are compiled first, repaired when necessary, and
checked against the exact frozen statements and an axiom whitelist.
Published mathematical suppliers missing from Lean/Mathlib remain obligations;
they are not introduced as assumed axioms or correctness interfaces.

Three work streams and main-thread integration are saved at their pause checkpoints. Their current
component results and outstanding dependencies are recorded under
[formalization/status/](formalization/status/). Compilation is serialized
and memory bounded. A compiling intermediate theorem is not completion of
its parent paper.
