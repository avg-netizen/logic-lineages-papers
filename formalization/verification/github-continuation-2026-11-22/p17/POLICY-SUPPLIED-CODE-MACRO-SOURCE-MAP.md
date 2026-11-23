# Supplied policy code: one macro call

Baseline: `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9`.

## Source and purpose

Paper 17 `paper.tex`, `thm:main`, explicitly requires uniformity in a
supplied computable admissible literal parsing policy.
`sections/source.tex`, `def:literal-policy`, defines the selector by macro
site and arity, independently of operand syntax and values. The existing
`GroundComparison.GroundDecidable` provides one computable decider per
effective policy without a uniform program-index interface. See the scoped
`CORRESPONDENCE-REVIEW.md` in this directory.

The new frozen target is
`LogicLineages/PermittedControl/PolicySuppliedCodeMacroTargets.lean`.
It defines one code-indexed interpreter for exactly one call to the existing
`StandardControlCurrent.PolicyShape.macroCode`; it does not alter that
definition, the admissible policy type, or any accepted source.

## Exact contract

- `RealizesPolicy e p` identifies the supplied ordinary `Nat.Partrec.Code`
  with the existing `PolicyShape.selector p`, on the literal encoding of
  every site-and-arity pair. This is a specification of the actual input
  program, not a premise about a source compiler or comparison result.
- `macro` evaluates that program, decodes its result as a Boolean shape
  script, and uses the existing `PolicyShape.expandCode` on the unchanged
  operand-code list. The outer `Part` retains possible nontermination of
  arbitrary code; the inner `Option` retains malformed-script and expansion
  rejection. No default successful value replaces a failure.
- `MacroPartrec` asserts joint partial recursiveness in code, site, arity,
  and the entire operand list.
- `ExactMacroCalibration` identifies the result with
  `Part.some (PolicyShape.macroCode p tag n xs)` whenever the supplied code
  realizes that policy. This includes termination for valid selector
  programs and all raw argument lists, including rejected expansions.

The proof may use the pinned Mathlib `Nat.Partrec.Code.eval_part` and the
accepted `PolicyShapeProgramsProof.expandProgram` supplier. No compiler
construction, ground-comparison decider, uniform near-control family, or
promotion of `thm:main` is claimed. Those remain subsequent obligations.

## Freeze and validation

The Targets source is hashed and recorded in the lane ledger before the
Proof source is authored. Root owns the sole native queue. No compiler is
launched by this lane; a passing exact native/axiom gate remains required
before this supporting contract can be recorded as checked.
