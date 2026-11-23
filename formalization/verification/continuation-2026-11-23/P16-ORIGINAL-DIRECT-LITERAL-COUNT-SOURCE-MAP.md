# Original literal occurrence-count AST and numerical fit

Native gate: `LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks`,
alias `exact_OriginalLiteralCountFit`. Uses the same existing raw constants,
equality combinator, actual original list recursors and append as
`Continuation20261114.ArgumentEntryCount.Definitions` and
`Continuation20261114.ArgumentCountComparison.Definitions`.
Same literal list occurrence counter (never deduplicates); check all
queried counts over append left right, then `List.perm_iff_count`, including
queries outside both supports (both counts zero). Numeric appendix proof
is replayed against the actual original append AST with light exact imports,
not the unrelated older primary-expansion dependency.

`NumberedWindowInternalLiteralCountNominalSourceChecks` is deliberately
source-only and excluded from the numeric root. Its original defining
import transitively needs absent Hydra. No checked nominal identity or
open count/member reflection is claimed. Numeric CountFit, once native,
applies to this newly selected AST in the parameterized dCore.
eb65567f0c366bb29301e704167745fceaec140fe41d5c065dd38e8fd7991ed1  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountDefinitions.lean
c90b56475bfa165cac29442e0d6c57c11b13120e9d4d89294a4d354227c646ab  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountNominalSourceChecks.lean
eca237a381f59d522a9b150ebb3890481ddc57bdb37ed268b4111976988d1025  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountNumericChecks.lean
98dc2e9f0c0686a0195ea957c2ae8417ab569158eb5aea8885fc05d5f8965507  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountNumericProof.lean
