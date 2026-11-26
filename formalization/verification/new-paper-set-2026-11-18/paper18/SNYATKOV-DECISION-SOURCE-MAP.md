# Current paper18 Snyatkov supplier: source-to-target and compilation plan

**Scope**: numbered `m:thm:snyatkov`, `18-standard-control-comparison/sections/control.tex`
66–69. The endpoint is actual effective decidability of the first-order
theory of `(Nat; 0, 1, +, <, f)`. The manuscript's expanded-language QE
argument (71–84) does not enlarge the numbered theorem. This packet does
not claim arbitrary expanded-language elimination, common-head or balanced
frontend correctness, or comparison decision for those languages.

| Current source | Literal frozen interpretation |
|---|---|
| 4–10: variable-seed hierarchy and exact shifted level five | `fastControl 0 n = 2^n`, `fastControl (j+1) n = (fastControl j)^[n+1] n`, `Phi n = fastControl 5 (n+100)`. The separately fixed-seed hyperfunction never substitutes for it. |
| 66–69: first-order arithmetic theory over naturals | Unchanged `BaseTerm` has constants/natural numerals (the latter are finite 0,1,+ abbreviations), raw names, plus and arbitrarily nested actual Phi. Unchanged `SourceFormula` has equality, strict order, negation, conjunction and existential Nat; the remaining Boolean connectives and universals are definable. All closed formulas are covered, with arbitrary nesting, raw-name shadowing through `Function.update`, repetitions, and no boundedness or input-shape restriction. |
| 68: effective decision | Frozen `FullSourceDecision` quantifies a total `Computable` Nat-to-Bool program on the unchanged `SourceFormula.encode` and exact truth for every closed formula at every valuation. Closure is precisely original free-variable-list exhaustion, not a solver admissibility check. |
| 79–84: evaluability of eliminated closed syntax | Concrete `SixSol20261112.SourceDecision.answer = groundMatrix ∘ eliminate`; elimination is H-free and retains only original free names. Congruence of actual `Matrix.eval` transfers evaluation at zero to every valuation in the closed case. `groundTerm` and `groundMatrix` have total raw radix recursion and calibrated expanded-term/Boolean zero-valuation semantics. They evaluate the actual Phi and bounded-floor inverse; their stronger numerical support for H and H-inverse does not claim decision/QE for that expanded source language. |

## Exact reuse, not historical register transfer

The superseded paper08 theorem at its `thm:snyatkov` had the same source
structure, fixed control, formula grammar, and closure quantifiers. Its
BUILD-014 (276 current-source-matched receipt entries at that time) and
ROOT-SNYATKOV-ADOPTION identify an actual full coded compiler/evaluator, not
an existence-only placeholder. Reuse those immutable **Working** modules:
`SourceDecisionWorkingDefinitions` / `SourceDecisionWorkingTargets` and
`BooleanGraphCodeWorkingDefinitions` / `BooleanGraphCodeWorkingTargets`.
Older non-Working and Code-named scaffolds are not the active theorem sources,
and must not enter this new import closure. The target is independently
spelled here; the old register is not adopted by name or count.

OriginalSourceElimination already proves typed equivalence at every
valuation, literal free-name containment and H-free output. The active old
compiler calibrates its radix-four term inclusion, radix-five formula
recursion and actual binder to that very typed elimination; all code functions
are genuinely `Computable`, via decreasing numeric child graphs. On a
valid `Matrix.encode`, both the active old binder and current packet 378's
raw graph route produce the same literal typed graph allocation and formula.
The current bound really is `i :: Code.names i p.encode` (`Code.bound`): the
name `i` is NOT part of the allocated fresh names. Current packet 393's literal
whole-bound projection calibration then proves current and old binder code
output equal on *every typed matrix encoding* even without H-free admission;
formal semantics only apply when the existing closure proof establishes it.
No all-raw equality of the two graph programs or semantic claim on malformed
payloads is needed or asserted. The chosen existing program is total for
all natural inputs, with deterministic inherited raw defaults. The semantic
claim is on the typed encodings named in the targets, with closure admission
only at the numbered endpoint.

Term subtraction is truncated natural subtraction; division by zero uses
Nat division's zero result. Expanded matrix divisibility at 0 means its term
is 0 (`0 ∣ n ↔ n = 0`); perfect residue-storage code 0 instead represents
modulus 1 inside `BlockRows`, not that expanded atom. Graph normalization
handles the distinction before projection. `phiInverse` uses actual
`Nat.findGreatest (fun n => Phi n ≤ x) x`, including 0 below Phi(0), with
computability paid by `SnyatkovInverse.Proof.actualPrimitiveRecursion.1`.
No trusted decision or inference from native computation participates.

## Order and gate

1. Freeze the source bytes, typed/raw semantics, active immutable old proof
   modules, current numbered comparator and current 378/393 suppliers.
2. Independent scope review and comparator-only native preflight, under the
   unchanged serialized profile and coordinator ticket. No proof before
   approval; keep any failed attempt and do not rewrite frozen declarations
   without the proposed/applied independent review process.
3. Assemble control arithmetic from definitional exactness and existing
   primitive-recursive witnesses; prove current binder equality using current
   calibration and the old literal binder compiler. Assemble literal
   elimination, H-free output, original name support and zero evaluator.
   Re-derive actual closed-answer calibration from these and original
   matrix valuation congruence; exhibit the literal program in the exact
   numbered target.
4. Native gate all named exact aliases and audit actual axiom closure
   (only standard permitted foundations); recursively verify current source
   and artifact evidence, confirm no alternate historical scaffolds enter
   closure, reproduce evidence independently and request numbered adoption.
   No conclusion is verified merely by this plan or the historical receipt.
