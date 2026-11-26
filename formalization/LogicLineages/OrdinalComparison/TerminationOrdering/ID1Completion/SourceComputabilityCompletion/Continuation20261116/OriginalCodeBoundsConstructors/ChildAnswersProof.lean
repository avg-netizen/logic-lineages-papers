module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.AnswersProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ChildAnswersProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open Continuation20261115 OriginalCodeBoundsRecursion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem binary (n : Nat) (raw left right lv rv rest deps valueRest values : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps raw z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps left rest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rv z)))
    (hvc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values lv valueRest)))
    (hel : Nonempty (Derivation body Delta (graph1 (bounds n) lv left)))
    (her : Nonempty (Derivation body Delta (graph1 (bounds n) rv right))) :
    Nonempty (Derivation body Delta (graph2 (OriginalCodeBoundsEquation.answers n) values raw z)) := by
  have ht := AnswersProof.consMap n rest right z z z rv valueRest hr (AnswersProof.nilMap n z)
    (AnswersProof.extractFromBounds n right rv her) hvr
  have hf := AnswersProof.consMap n deps left rest valueRest z lv values hc ht
    (AnswersProof.extractFromBounds n left lv hel) hvc
  exact AnswersProof.answersAt n raw z deps values hd hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ChildAnswersProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ChildAnswersProof
