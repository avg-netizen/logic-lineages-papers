# Original quotient-edge checker

The source is `NumberedNumericQuotientEdge.numericEdgeTest`, with its original source universe decoder, target packed decoder, numeric step checker, and least-code representatives. The existing certificate fields remain the original nested Nat.pair selectors. Source and target representative builders are totalized with zero only on their respective decoder failures.

`numericStepTest` already rejects if either decoder fails. Therefore its exact Boolean output guards both representative comparisons on every natural input, without requiring subtype closure of S or adding a target universe test. The candidate checker is the explicit original Program composition of the existing selectors, a calibrated step Program, two calibrated representative Programs, the original equalityTest, and exact-one conjunction.

The primitive witnesses are chosen for each fixed n, arity, symbols, S, Gamma and table. This component does not claim a context-uniform source presentation. Its three internal targets quantify arbitrary Program data, arbitrary positive inductive body, arbitrary variable type, and symbolic terms. Their contextual proof helpers use only actual original graph witnesses. No standard-model evaluation fact is reflected into an internal Derivation.

Five exact frozen targets cover simultaneous all-input witness existence; exact all-input numericEdgeTest calibration; selector-guarded internal acceptance decomposition and reconstruction; the equivalent rule at supplied representative graph outputs; and the rule for an original constructor-produced certificate. These expose the pending step-preservation and representative-congruence obligations needed for application-edge lifting without assuming or claiming those obligations.
