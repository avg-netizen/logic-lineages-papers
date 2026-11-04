# Numeric CPS scaling spine

This implements the existing exact ParametricScalingPlan.scalePlan for the e-fold doubling in paper09 hardness.tex lines 294–314. It is a code-construction bridge, not a new semantic or complexity theorem.

The raw state contains two numeric ports and a canonical continuation spine. One advance inserts a fresh source coordinate, shifts the input port by one, chooses fresh output port 1, and prepends the addition gate (1,1,shifted old output) to the binder-aware insertion of the old continuation. Existing existential binders within that continuation remain protected. After e advances, build prefixes e existential instructions and a final equality gate before the accumulated continuation.

ExactNumericRecursion proves precisely the zero/successor CPS equations on all raw inputs. ExactScaling identifies build with the canonical spine of the unchanged actual scalePlan for every actual input/output port and arbitrary Supported continuation. The zero-port sentinel is preserved and the proof must identify insertion [] [ground] Γ with actual weakening, including its action under lifted binders. No semantic satisfaction assumption is needed.

UniformPrimitiveRecursive proves the finite state advance and e-fold constructor primitive recursive using standard list/product coding and finite iteration. This does not evaluate Gamma or control/halting, and claims no binary-literal construction, complete (b,e)-to-code map, scalar Nat wrapper, malformed-code typedness, runtime or size bound. Accepted files and package bytes remain unchanged; verification-only, no export.
