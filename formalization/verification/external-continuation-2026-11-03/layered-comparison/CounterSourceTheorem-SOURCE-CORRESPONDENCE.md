# Counter expansion and collision under the companion kernel convention

## Scope qualification and pending numbered source
The checked Lean targets use the explicit actualSuffixKernel convention of paper07, def:kernel: at a nonfinite state eta+n, the next suffix is M(eta,Phi(v)-c), using the limit part eta and the current total norm v. All accepted proof conclusions in this component are valid for that convention.

They do NOT yet establish unconditional correspondence to the printed paper08 lem:counter. Paper08 lines239–242 says to replace the nonfinite suffix by the greatest smaller suffix. Read literally as the whole current state, this differs from selecting below its limit part at later states with positive finite tails. For example, at omega+1 with sufficient norm budget, the greatest ordinal below the whole current state is omega, whereas selecting below its limit part omega yields a finite ordinal. This is a mathematical convention discrepancy, not a failed Lean proof.

The explicit startup target aligns the first replacement from the principal input and proves no extra startup transition is counted. It does not resolve the later-step discrepancy. The reference to full-budget saturation and the companion's definition may indicate an intended convention, but no manuscript correction or implicit reinterpretation is authorized. The registered paper08 lem:counter remains pending. The Lean target name WholeCounterLemma denotes the assembled claims under the fixed Lean kernel convention, not an unconditional certification of the printed paper08 statement.

## Exact checked data and startup interface
Write r=n+3 and s=m+3, covering ranks at least three, with arbitrary natural retained masses c,e and original inputs t,u. CounterLeaderExpansion.count is actualSuffixKernelCount at omega^r; kernel is its actual total exit norm. The descending entries contain every original aligned A_h in order, bottomInput is A_3, leaderPreimage is X^3_(c+3)(A_3), and leader is Phi of that preimage. The residual list contains every actual E^h_(c+h)(A_h), including the cubic term. No numerical oracle or independent chain is substituted.

The initial suffix omega^d+(t-c-N(omega^d)) records total norm t. The startup theorem proves that its first counted replacement is M(omega^d,Phi(t)-c), that its full count is one plus the actual count after this replacement, and that output is Phi iterated by that same count at original t. All later steps still use the explicit companion limit-part convention. No equality with a different whole-current-suffix transition system is claimed.

## Uniform effective bounds
A common maximum of both previously saved comparison tails is uniformly primitive recursive. Each comparison tail combines c+2r+1, 2c+10 and the cubic recognition modulus max(16,max(c+3,e+3)+4). These are sufficient bounds, not minimality claims. Uniform primitive recursion is also proved for the quantitative residual and fixed-shift tails. No eventuality witness or correctness certificate is an input.

## Assembled mathematical clauses under the fixed convention
1. Actual entry ranks are r down to3. The integer identity is E=H/2+1-ceil(c/2)+the complete residual sum; H is even, and subtraction is not truncated.
2. H<2E and4E<3H give the strict rational half/three-quarter inequalities.
3. Equal actual leaders imply equal retained mass. For r>=s, the smaller input is the actual aligned A_s and the integer difference is the complete upper residual sum. Each introduced rank exceeds s; when r>s the order is strict.
4. Strict count comparison is leader order followed by rank order on a leader tie; count equality is exactly equal leader and equal rank on the explicit tails.

Actual cubic mass/input comparison supplies recognition without assuming the still-pending whole uniform-separation lemma. Separately accepted proofs give quantitative residual divergence and positive true integer fixed shifts under the same fixed convention. Their computed tails do not repair the printed convention discrepancy.

No manuscript or frozen Lean target is changed by this clarification. The original freeze and compiler evidence remain preserved. Source correspondence and any numbered promotion require a separately authorized resolution and independent review. Word-composition, ordered-guard elimination, the unsafe higher-rank signed recurrence and arithmetic decision remain outside this component.
