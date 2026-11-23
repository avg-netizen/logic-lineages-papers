# Paper 16: visible singleton-bottom direct-checker branch

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`
lines 74–76, 84–98 and 142–153. This is a certificate result toward the
internal multiset argument, not membership or induction on J.

A new physical dSB first recognizes the packed singleton with its literal
selected one-field bottom recognizer. On that branch, target zero delegates
to the original d and a nonzero target returns zero; outside that branch
all original result values are retained. The already checked exact
numeric singleton-bound proof gives calibration against the original
checker on **all numeral inputs**, including malformed data.

On the same newly selected body, the genuine object certificate projects
to dSB. The open recognizer exposes the inner branch at a literal singleton
bottom with symbolic packed context/type, leaving successor and witness
arbitrary. Case splitting inside the original object calculus shows that
every positive successor would route to constant zero and contradicts the
accepting graph by functionality; hence the certificate proves equality
of its actual target to zero. No claim transports a derivation from d0 or
#660. Fresh interpretation/reinstallation and J(0)/J(singleton) membership
on the new body are not proved here. No singleton-free or full multiset claim.

Native candidate (pending):
`LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranchChecks`.
Exact authored source SHA-256:
- e0ae121ae0cde8d1916b8f3f756106507d933d81d325c8085aa0e462078416d8  LogicLineages/PersistentMarking/NumberedWindowInternalSingletonBottomBranchChecks.lean
- d7c10b8a53963555d7c2ba82c970d428479510de9629a50013742b83632afca0  LogicLineages/PersistentMarking/NumberedWindowInternalSingletonBottomBranchProof.lean
- ea9a0dcfb190a6da4f24115784afc3506a588cb00a893a15e13956a05f09b494  LogicLineages/PersistentMarking/NumberedWindowInternalSingletonBottomBranchTargets.lean
