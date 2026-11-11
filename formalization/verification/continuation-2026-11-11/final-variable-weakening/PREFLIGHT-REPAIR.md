# Preflight parser repair

The first serialized preflight, receipt 1794401432731771020-17, rejected reserved Lean identifier `variable` in Definitions line 16 and following uses. The three original specification files and their frozen manifest are preserved in `preflight-attempt1/`, with the matching failure log.

The sole mathematical-file change renames that bound identifier and its occurrences to `variableCode`. There is no proposition, quantifier, graph AST, selector, or premise change. All three files are refrozen; proof authoring remains stopped pending successful preflight.
