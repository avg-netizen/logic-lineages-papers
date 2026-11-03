# Degree-two complete-count convention diagnostic

This component fixes degree2, retained mass1 and original input4. The independently defined whole-state count starts at omega squared and uses the literal schedule budget(i)=Phi iterated i+1 times on the original input, minus one. It does not recompute budgets from the changed whole-state norm. The companion count is the unchanged actualSuffixKernelCount under paper07 limit-part semantics.

The exact first target calibrates the first two schedule entries and gives companionCount= q+1, q=(Phi(4)-1)/2. The second proves q+2 ≤ wholeCount, hence strict complete-count disagreement. The proof will use ordinal-well-founded first-finite counting, the verified common first state omega*q+1 and whole second state omega*q, and a uniform lower bound for the remaining shifted schedule. No enormous control value is numerically evaluated. Parameterized helper proofs specialize exactly to input4.

These are different formally specified complete counts at a degree-two instance. This does not refute the paper08 rank-at-least-three lem:counter, decide intended interpretation, amend either manuscript, or promote a numbered source theorem. The literal wording discrepancy remains a source-correspondence issue. No assumption of agreement between scheduled whole-state counts and norm-controlled companion counts is made.
