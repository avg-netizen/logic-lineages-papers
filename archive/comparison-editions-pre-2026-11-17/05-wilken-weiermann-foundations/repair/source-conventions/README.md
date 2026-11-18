# Literal source conventions and the bounded-norm repair

The complete explanatory note is [source-conventions.pdf](source-conventions.pdf),
with standalone [TeX](source-conventions.tex). [BODY.tex](BODY.tex) is the same
proof body with namespaced helpers for inclusion in the parent paper; it uses
the parent theorem environments and bibliography key `ww`.

The parent paper now includes these proofs in `source-syntax.tex`. Its declared
default is left-comb sum/repeat/numeral/aggregation, including active-sum
partials, with the existing right-associated box tail retained. The proofs
of domain, norm and translation apply to every admissible computable policy.

The substantive findings are:

* The printed formulas do not select a unique binary expansion of all finite
  sums. The closed, typed source `λz:o. λx:o. ((λw:o.z) x)` has actual positive
  assigned values 204 and 184 under two permitted policies. All repeats are
  held identical; only the active-sum partial's three operands are associated
  differently. [Full derivation](GENERATED-WITNESS.md).
* Printed Lemma2.19 is falsely strict at `h=x_0`. Its weak replacement pays
  the domain premise. A sharper positive-grade free-subterm bound proves
  bounded norm using the original multiplier, without the false strict
  appendix estimate(A.5). [Full proof and explicit later-use audit](WEAK-LEMMA-AND-NORM.md).
* Each explicit policy gives an exact actual-source forward translation with
  the original ground-free-name restrictions, and preserves both positive
  subclasses. It does not identify assignments across policies.
  [Finite syntax policy, bounds and translation](POLICY-AND-TRANSLATION.md).

The one bounded control is [check_generated_witness.py](check_generated_witness.py).
It reconstructs the named Var/Lam/App source, checks its type levels, and
evaluates only the finite positive coordinate. It never evaluates ψ or Φ.
[CONTROL.json](CONTROL.json) records the successful single invocation:
1.620 seconds, 19,528 KiB peak RSS, unchanged shared-resource guards. This is
a concrete control, not the proof of the uniform theorems.

[SOURCES.json](SOURCES.json) identifies the actual primary source, inspected
locators, and source hashes. [CHECKPOINT.json](CHECKPOINT.json) pins the final
proofs, control, build and canonical-integration receipt. The mathematical
grade is primary-source hand proof with a separate-agent same-model root
reading; no independent-model, Lean, full-termination-proof audit or priority
claim is made. Fixed zero-history assignments are not claimed to decrease
on all reductions.

Rebuild the standalone note, with an installed and cached Tectonic, using
`tectonic --untrusted --only-cached --keep-logs source-conventions.tex` in this
directory. It uses the same OT1 Computer Modern family as the parent paper.
No network, private library files or external vault conventions are required
to read or typeset it.
