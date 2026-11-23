# Paper 16: actual reverse parser success at a literal original cons

This is the positive-cons coverage supplier needed for the eventual original
packed-list proof of [ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
149–153. It does not decompose an arbitrary positive raw code.

[Exact source](../../LogicLineages/PersistentMarking/NumberedWindowInternalOriginalRawConsParserReverseProof.lean):
* `exact_OriginalRawConsRejectsOfTailReject` uses the actual zero branch of
  the original prepend program, the literal raw cons graph, and the checked
  thin forward parser rule #1552. It proves actual parent parser output zero
  when the actual tail parser reports zero.
* `exact_OriginalRawConsParserReverse` uses the original internal Option
  analysis of the genuine tail parser. In its zero branch the parent's
  original positive parser report contradicts the actual zero report by
  functionality. In its positive branch, open the actual standard scratch
  cons output using the same input head and the actual selected scratch
  tail; #1553's original forward parser then reports that value for the
  original raw parent. Parser functionality and successor cancellation
  force it to be exactly the supplied parent scratch output. Transport
  the true scratch cons graph, preserving every original argument.
* The original open raw-cons order argument pays the strict raw tail
  bound at the same actual head and tail. Fresh contexts keep all source
  hypotheses and may eliminate for arbitrary object formulas; no outside
  decoder, proof of observer reflexivity, or permutation substitute is used.

Scope given literal raw cons and real positive parent report. Arbitrary
raw decomposition, full symbolic fold, numbered J or other closures are
not claimed. Native author status: source only.
