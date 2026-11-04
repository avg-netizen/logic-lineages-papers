# Actual one-step iff between two weakened images

Draft for exact review; no proof/export. Structural context prerequisite for paper 06 lines 583–597.

Targets are literal iff for WindowStep and WindowArgumentStep between q/r or tuple endpoints and their explicit weakenings. Forward is accepted StepRenaming. Reverse uses singleSubstitution with a closed non-bottom filler app(bottom(sigma→sigma))(bottom sigma), not bottom itself. All substitution images are non-bottom: the fresh variable maps to that application, and old variables map to themselves. Accepted strict substitution induction then gives an actual step, while weakeningCancellation restores both endpoints.

No irreflexivity or no-self-step assumption is used. No arbitrary-successor image invariant is assumed. The filler need not be in S; the raw strict-substitution theorem has no universe premise, and both final endpoints are exactly the original terms. This is not a GoodSubstitution/carrier claim for arbitrary intermediate inputs. All original head/window/precedence guards and allowed contexts remain unchanged.

This does not assert that every successor of one weakened term is itself a weakening, nor does it establish quotient reflection, Acc or C stability. No all-term/ID1/export claim; accepted files unchanged.
