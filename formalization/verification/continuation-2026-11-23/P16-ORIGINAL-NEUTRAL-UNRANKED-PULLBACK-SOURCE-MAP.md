# Paper 16 (T): original accessibility pullback with a zero-rank forward obligation

Original (T), `16-persistent-marking-termination-ordering/sections/ordinals.tex:113–127`.
Staged, native checks pending. The original `Pullback`, inverse motive,
successor/certificate formulas and same physical argument are unchanged.

`UnrankedForwardRule S g p c` is the original pointwise `forwardImage`
only at a source f with a real `g(f)=0` graph. Given the unchanged
original actual `accepts p f u x` and actual edge f→f', it still must
supply the original real output of p on f',u and the true x→y image
edge. The successor f' need not have rank zero.

The generic proof recuts `NumberedWindowInternalPullbackChecks`:
the actual input carrier is extracted from the same accepted p. The
same physical unary g graph is split by the original object zero/successor
elimination. The positive branch uses verified same-body RankDrop
strong induction at that actual k and f, without consuming a forward
law or an assumed I(f). In the zero branch, actual original
accessibility introduction uses the held zero graph at each genuine
edge and the restricted ForwardRule. The original output-side ID₁
slice induction, descendants, and inverse elimination are preserved.

The exact separately staged `exact_RankGuardUnrankedPullback` supplies
RankDrop using its physical rankEven theorem, for the true same
`data i j (rankEven i g r) d` and `rankApplication i g p`.
It still needs actual input guards and true `UnrankedForwardRule`.
Neither numeric calibration, rank coverage for arbitrary inputs,
forward image of any source, nor full (T) is claimed.

Serial: `NumberedWindowInternalNeutralUnrankedPullbackProof` (1261/30,
target 855/28) after RankAccessibility, then
`NumberedWindowInternalNeutralRankGuardUnrankedPullbackProof` (1320/30)
after RankGuardDrop. No blocked import families in the static closure.

Exact source and premise pins (SHA256):
~~~text
3375377355da6c4fad04b4f30fbb817e163e7f91c22abfd1f7b96e65bb66cb51  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralUnrankedPullbackTargets.lean
db5e6b6aad3a18f80c3f9ef064c83b273268cbc22df103fa26446fe551826c86  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralUnrankedPullbackProof.lean
d76d6a0d97941acc7b4cc353cff6ee90e147bda926e9d0445e2f3a6ca38ede67  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralRankGuardUnrankedPullbackProof.lean
e19bd06739bd9afd5a0e515c535f634e56db21063058c41345a9f1f9bc3ac2c1  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralRankGuardDropProof.lean
2c2ac3401021dbbe0db94e16b7ee69fed4013eb3b9c392eb5db1d6d02ac9c14d  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralRankAccessibilityProof.lean
2e896ed4b0615a91534e4bdf060e77837b38979ee8dd33621017bcf0390137b7  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalPullbackChecks.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
~~~
