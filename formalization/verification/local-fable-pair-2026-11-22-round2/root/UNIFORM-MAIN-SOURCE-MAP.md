# Paper 17 `thm:main`: strengthened comparator with the printed uniformity

Answers the external review `../../github-continuation-2026-11-22/p17/CORRESPONDENCE-REVIEW.md`:
#1429's `MainComparison` gives a decider per effective policy and per near-control parameter, but the
printed theorem (`paper.tex` l.83–100) is "uniformly in a supplied computable admissible literal parsing
policy" and "for every supplied b".

Frozen `LogicLineages/PermittedControl/UniformGroundComparisonTargets.lean`
(sha256 `b9c21bc475811a5f06928495c37ea4e529e29c0332396cbaa266251a6d123d4a`, compiled alone: receipt `1795396390006055903-3224155`):

- `UniformGroundDecidable ctrl` — for each relation ONE partial recursive procedure whose runtime input
  is the policy program (`Nat.Partrec.Code`), the context length and the two term codes; the existential
  is outside the quantifier over policies. For every program realizing a policy (`RealizesPolicy`, #1433)
  it halts on every raw input and is correct on codes of typed terms with ground free variables.
- `UniformNearGroundDecidable` — the same with the near-control parameter b as a further runtime input.
- `UniformGroundComparison` — both; `UniformImpliesGround` — it implies #1428's `GroundComparison`.
- `UniformMainComparison` — control laws, near-control modular bound, `UniformGroundComparison`, the
  functional hardness of #339, and the literal reduction programs with their exact total reductions
  (`SelectedFiniteQueryTargets.{LiteralProgram,ExactTotalReduction}`,
  `SelectedSingleQueryTargets.{LiteralPrograms,ExactTotalReduction}`), which are policy- and
  control-independent functions.

Choices made, for the owner/reviewer: one procedure per relation rather than the relation as an input
(three relations; a tagged single procedure follows by cases); divergence is allowed on programs that
realize no policy, as the review recommends; the answer on raw inputs that are not codes of typed
ground-context terms is unconstrained beyond halting. Not claimed: uniformity of the hardness
statements beyond what the literal reduction programs give; any change to #1418/#1428.

## Outcome (same round)

`UniformGroundComparison.uniformMainComparison : UniformMainComparison` is gated with no hypothesis
(`LogicLineages/PermittedControl/UniformGroundComparisonProof.lean`, receipt `1795399023916468157-3254750`,
record #1445). Chain: #1433/#1434 (external agent: supplied-code macro and realization) → #1444 (Opus A:
compiler taking the policy program as input) and #1441 (Opus B: closed-block decider computable jointly
in b) → #1439 (root: assembly, both controls) → #1437 (root: the remaining conjuncts are accepted
statements; the uniform statement implies #1428) → #1445.

For a reader checking this comparator against `paper.tex` l.83–100, the points to look at:
1. "uniformly in a supplied computable admissible literal parsing policy" ↔ the procedure's first
   runtime input is a `Nat.Partrec.Code` and the hypothesis is `RealizesPolicy e p` (the code computes
   the policy's selector at every site and arity). Admissibility of the policy is whatever the type
   `Policy` already carries (reviewed for `thm:ground`).
2. "For every supplied b" ↔ `UniformNearGroundDecidable` takes `b` as a runtime input.
3. Clause (i) "decidable" ↔ halting on every raw input for realizing programs plus correctness on codes
   of typed terms with ground free variables; one procedure per relation (weak, strict, equality).
4. Clauses (ii), (iii) ↔ `SelectedFunctionalHardness` (no decider at levels 2 and 3, for every selected
   control and every policy) together with the literal reduction programs `FiniteQueryCode.reduceCode`
   and `SeededQueryCode.reduceCode` (primitive recursive, policy- and control-independent) and their
   exact total reductions. The paper's "finite-query" and "single-query" reductions are these programs.
5. "an explicit permitted primitive recursive control f_*" and the f_b clauses ↔ `Targets.FullControl`
   and `Targets.NearControlModular`, as in #1429; "permitted" is still carried by the control-law
   clauses, not by a formalisation of Wilken–Weiermann §2.1 (unchanged from the earlier table).
