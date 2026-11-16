module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem unary (n : Nat) (raw child childDepth deps values : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps raw z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values childDepth z)))
    (he : Nonempty (Derivation body Delta (graph1 (depth n) childDepth child))) :
    Nonempty (Derivation body Delta (graph1 (depth n) (suc childDepth) raw)) := by
  have hm := AnswersProof.consMap n deps child z z z childDepth values hc (AnswersProof.nilMap n z)
    (AnswersProof.extractFromDepth n child childDepth he) hv
  exact ValueProof.atAnswers n raw values childDepth hg (AnswersProof.answersAt n raw z deps values hd hm)
    (CollectProof.singleton values childDepth hv)

theorem binary (n : Nat) (raw left right leftDepth rightDepth maximum rest deps valueRest values : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps raw z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps left rest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightDepth z)))
    (hvc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftDepth valueRest)))
    (hel : Nonempty (Derivation body Delta (graph1 (depth n) leftDepth left)))
    (her : Nonempty (Derivation body Delta (graph1 (depth n) rightDepth right)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum leftDepth rightDepth))) :
    Nonempty (Derivation body Delta (graph1 (depth n) (suc maximum) raw)) := by
  have htail := AnswersProof.consMap n rest right z z z rightDepth valueRest hr (AnswersProof.nilMap n z)
    (AnswersProof.extractFromDepth n right rightDepth her) hvr
  have hfull := AnswersProof.consMap n deps left rest valueRest z leftDepth values hc htail
    (AnswersProof.extractFromDepth n left leftDepth hel) hvc
  exact ValueProof.atAnswers n raw values maximum hg (AnswersProof.answersAt n raw z deps values hd hfull)
    (CollectProof.double values valueRest leftDepth rightDepth maximum hvr hvc hm)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildValuesProof
