# Literal ordinary-head standalone recurrence, exact1

Status: frozen for independent review/preflight. No proof authored.

## Source correspondence and important boundary
`LogicLineages/OrdinalComparison/TerminationOrdering/NumberedExchangeCodeDefinitions.lean:45-48` has `(headMove && equal result) || (equal semantic head && recursive child exchange)`.
`Continuation20261114/ConcreteHeadMoveLayer/Targets.lean:InternalOrdinary` gives the actual internal field-level law using `eqn rg rf` and `eqn ef eg`. The new target preserves those precise computations as transparent equality-test compositions `resultEqual g f` and `encodedEqual f g`. It DOES NOT assert encoded-head equality is raw headNumber equality on all raw inputs. Existing native head encoding calibration applies to genuine HeadCode encodings; it is not an internal injectivity theorem. General internal semantic/raw-head equality remains a separate obligation.

The five premises are actual original ordinary constructors, parent pair, child pair and parameter pair(symbols,types). No validity/Some/answer-list/field-calibration/output-injectivity assumption. The actual guard is on the RHS at dummy answer0; paid guard independence pays that spelling. Target-result/source-result order is explicit.

## Duplicate check and proof plan
Existing ConcreteHeadMoveLayer.InternalOrdinary is conditional on guard, four head field outputs and a supplied answer-list cons graph. No standalone recurrence is claimed there. The new proof queries those outputs internally, proves actual singleton D and ordered singleton standalone answer, invokes the paid recursive equation and the original field-level clause, and derives equality-test equivalences from actual composition/equality-test graphs. Shared guard necessity handles malformed rejection. Prior lambda singleton/cross and binary full-order helpers may be reused without replacing R/D/G.

This is one literal ordinary-head recursion clause, not full semantic E/typed packed edge, numbered-head clause, installed supplier completeness or accessibility. Do not collapse encoded equality to raw equality or infer internal semantics from native calibration. Fixed standard axioms/resources.
