module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem resultFactor (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (V : Program 3) (target : Bool) (node code param rawHead out : OTerm alpha)
    (hh : Nonempty (Derivation body Delta
      (graph3 (TransparentMetadataFields.head V target) rawHead node code param))) :
    Nonempty (Derivation body Delta (graph3 (result V target) out node code param)) ↔
    Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult out rawHead)) :=
  ⟨fun h => unaryRecover OriginalHeadResult.headResult (TransparentMetadataFields.head V target)
    out rawHead ![node,code,param] h hh,
   fun h => unaryValue OriginalHeadResult.headResult (TransparentMetadataFields.head V target)
    out rawHead ![node,code,param] h hh⟩

theorem internalOrdinary : Targets.InternalOrdinary := by
  intro body alpha Delta V target tag node code param raw rawHead payload base out hV hq hc hp
  have hh := (TransparentMetadataFields.InternalProof.ordinaryFields V target
    node code param raw rawHead base hV hq hc).2.1
  exact (resultFactor body alpha Delta V target node code param rawHead out hh).trans
    (OriginalHeadResult.InternalProof.internalTagFactor body alpha Delta tag rawHead payload out hp)

theorem internalNumbered : Targets.InternalNumbered := by
  intro body alpha Delta V target tag node code param raw rank rawHead payload tau base ts extras out hV hq hc hp
  have hh := (TransparentMetadataFields.InternalProof.numberedFields V target
    node code param raw rank rawHead tau base ts extras hV hq hc).2.1
  exact (resultFactor body alpha Delta V target node code param rawHead out hh).trans
    (OriginalHeadResult.InternalProof.internalTagFactor body alpha Delta tag rawHead payload out hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.InternalProof
