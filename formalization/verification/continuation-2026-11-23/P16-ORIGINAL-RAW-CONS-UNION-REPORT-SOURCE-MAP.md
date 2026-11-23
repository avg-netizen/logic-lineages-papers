# Paper 16: actual open U at one literal raw cons

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
142–153 uses finite union of the original singleton occurrences. #1540's
finite builder requires the literal U proofs at each cons. This packet
supplies **one** such U from the actual tail parser and one observer premise.

* [Raw program build](../../LogicLineages/PersistentMarking/NumberedWindowInternalConsUnionReportBuildProof.lean)
  assembles the original `rawSourceCheck (observePartition count)` program
  on the same literal source/kept/removed tapes. Its three parser successes,
  guarded projections, actual scratch append, and actual observer acceptance
  are separate proof inputs. There is no manufactured test or output.
* [Actual cons report](../../LogicLineages/PersistentMarking/NumberedWindowInternalOriginalRawConsUnionReportProof.lean)
  opens genuine object-code scratch cons outputs for the singleton and parent.
  The parent parser uses precisely the supplied successful parser for the
  actual raw tail. The singleton parser uses the checked nil parser and the
  same original raw cons computation. Scratch append of the singleton and
  exact decoded tail produces the **same** parent scratch output by the
  original cons/zero append equations. The raw sparse polynomial syntax
  and standard scratch cons are not identified.
* `OpenObserverReflexivity` supplies a real open derivation of acceptance on
  that same scratch operand twice. It is an explicit **unproved premise**,
  not derived from `CountFit`, interpreted numeric truth, or a substitute
  comparator. This leaf neither installs this fact nor assumes a split.
* Scope only one given original raw cons. Reverse parser/head-tail coverage,
  general symbolic-length proof, arithmetic split and carrier supply,
  unconditional J and numbered promotion are not claimed.

Native author status: source only; Build audit `unionReportOfGraphs`,
main audits `actualRawConsParser` and `exact_OriginalRawConsUnionReport`.
