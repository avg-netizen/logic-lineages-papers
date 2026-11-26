module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem internalFactor : Targets.InternalFactor := by
  intro body alpha Delta R D J V K source target param node window out hV hn hK
  let xs : Fin 3 → OTerm alpha := ![source,target,param]
  have hv : Nonempty (Derivation body Delta (programGraph V (suc z) xs)) := hV
  have hk := unaryValue K (.projection 2) window param xs hK (projectionValue 2 xs)
  constructor
  · intro h
    have he := successorBranchElim V (InternalAcceptance.constantZero 3)
      (.composition (ExchangeSelectedRecursor.exchange R D J) ![nodeCode,windowCode K]) out z xs hv h
    exact binaryRecover (ExchangeSelectedRecursor.exchange R D J) nodeCode (windowCode K)
      out node window xs he hn hk
  · intro he
    have hc := binaryValue (ExchangeSelectedRecursor.exchange R D J) nodeCode (windowCode K)
      out node window xs he hn hk
    exact successorBranchIntro V (InternalAcceptance.constantZero 3) _ out z xs hv hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.InternalProof
