# Exact numeric code for literal I/K wrappers

Paper09 paper.tex lines 193–201 uses direct K R and I L, not the existing magnify-based weakPair. This component calibrates the unchanged literal identityApply/constantApply syntax to the existing radix-eight source encoding.

I is lambda ground (variable zero), so its code is 6. K is lambda ground zeroC, so its code is 8*Nat.pair 0 1+6. The application tag is 5. The original operand code appears unchanged as the application argument: no operand variable shift or insertion is performed, since the operand is outside the lambda body. ExactEncoding applies in any typed context.

The two numeric constructors are primitive recursive on all natural codes; this does not assert malformed operands become well-typed. FragmentPreservation retains the exact recursive ground-binder/zero/successor restriction. InternalLevelPreservation uses the existing typeSupport-based structural theorem with AllGround explicitly required, rather than ignoring functional free-variable types.

No coded weak language, tuple packaging, generated reduction, evaluator upper bound, numerical complexity, runtime or source-register promotion is included. All existing syntax, assignments and weakPair remain unchanged.
