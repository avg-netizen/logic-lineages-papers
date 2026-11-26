module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def active (U : Fin 19 → Program 3) (V : Program 3) := TransparentExchangeLayer.fields (fields U V)

theorem rawSides (node code param source target : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target))) :
    Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode false) source node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode true) target node code param)) := by
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha node source target) hp
  exact ⟨unaryValue InternalUnpair.left (.projection 0) source node ![node,code,param]
      ⟨Derivation.conjunctionLeft hi⟩ (projectionValue 0 ![node,code,param]),
    unaryValue InternalUnpair.right (.projection 0) target node ![node,code,param]
      ⟨Derivation.conjunctionRight hi⟩ (projectionValue 0 ![node,code,param])⟩

theorem sideGraphs (U : Fin 19 → Program 3) (V : Program 3) (side cons : Bool)
    (node code param raw domain left right : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode side) raw node code param)))
    (hc : Nonempty (Derivation body Delta (graph3
      (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
      raw domain left right))) :
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 7 else 0))
      (numeral (if cons then 7 else 2)) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 8 else 1)) domain node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 12 else 5)) left node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 13 else 6)) right node code param)) := by
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht : Nonempty (Derivation body Delta (programGraph
      (leftOf (TransparentChildFields.rawCode side)) (numeral (if cons then 7 else 2)) xs)) := by
    cases cons with
    | false => exact applicationTag _ raw domain left right xs hq hc
    | true => exact consTag _ raw domain left right xs hq hc
  have htag := successorBranchIntro V (InternalAcceptance.constantZero 3)
    (leftOf (TransparentChildFields.rawCode side)) (numeral (if cons then 7 else 2)) z xs hV ht
  obtain ⟨ha,_,_,_⟩ := TransparentMetadataFields.InternalProof.internalApplication body alpha Delta V side cons
    node code param raw domain left right hV hq hc
  obtain ⟨hf,hs⟩ := TransparentChildFields.InternalProof.internalApplication body alpha Delta V side cons
    node code param raw domain left right hV hq hc
  cases side with
  | false =>
    refine ⟨?_,?_,?_,?_⟩
    · simpa [active,fields,TransparentExchangeLayer.fields,TransparentTagFields.sourceTag,
        TransparentTagFields.sourceRawTag,TransparentChildFields.rawCode,xs] using htag
    · simpa [active,fields,TransparentExchangeLayer.fields,EncodedMetadataFields.annotation] using ha
    · simpa [active,fields,TransparentExchangeLayer.fields] using hf
    · simpa [active,fields,TransparentExchangeLayer.fields] using hs
  | true =>
    refine ⟨?_,?_,?_,?_⟩
    · simpa [active,fields,TransparentExchangeLayer.fields,TransparentTagFields.targetTag,
        TransparentTagFields.targetRawTag,TransparentChildFields.rawCode,xs] using htag
    · simpa [active,fields,TransparentExchangeLayer.fields,EncodedMetadataFields.annotation] using ha
    · simpa [active,fields,TransparentExchangeLayer.fields] using hf
    · simpa [active,fields,TransparentExchangeLayer.fields] using hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.SupportProof
