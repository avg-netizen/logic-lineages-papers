module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem dependencyAt (raw param values : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children values raw))) :
    Nonempty (Derivation body Delta (graph2 dependency values raw param)) :=
  unaryValue ArgumentEntriesChildren.children (.projection 0) values raw ![raw,param] hc (projectionValue 0 ![raw,param])

theorem leafChildren (raw : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf ArgumentEntriesChildren.raw) z raw))) :
    Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children z raw)) :=
  zeroBranchIntro (OriginalRawSyntaxTransport.arityOf ArgumentEntriesChildren.raw) (OriginalRawSyntaxTransport.constant 1 0)
    (InternalAcceptance.branch (OriginalRawSyntaxTransport.sameOf (OriginalRawSyntaxTransport.arityOf ArgumentEntriesChildren.raw) (OriginalRawSyntaxTransport.constant 1 2))
      ArgumentEntriesChildren.singleton ArgumentEntriesChildren.double)
    z ![raw] ha (constantValue 0 ![raw])

theorem variable (raw param index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index))) :
    Nonempty (Derivation body Delta (graph2 dependency z raw param)) :=
  dependencyAt raw param z (leafChildren raw (variableArity ArgumentEntriesChildren.raw raw index ![raw] (projectionValue 0 ![raw]) hc))

theorem bottom (raw param typ : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw typ))) :
    Nonempty (Derivation body Delta (graph2 dependency z raw param)) :=
  dependencyAt raw param z (leafChildren raw (bottomArity ArgumentEntriesChildren.raw raw typ ![raw] (projectionValue 0 ![raw]) hc))

theorem nil (raw param  : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (graph2 dependency z raw param)) :=
  dependencyAt raw param z (leafChildren raw (nilArity ArgumentEntriesChildren.raw raw ![raw] (projectionValue 0 ![raw]) hc))

theorem unary (ordinary : Bool) (raw param metadata child listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2
      (if ordinary then OriginalRawSyntaxTransport.ordinaryConstructor else OriginalRawSyntaxTransport.lambdaConstructor) raw metadata child)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode child z))) :
    Nonempty (Derivation body Delta (graph2 dependency listCode raw param)) :=
  dependencyAt raw param listCode (ArgumentEntriesChildren.InternalProof.internalUnary body alpha Delta ordinary raw metadata child listCode hc hl)

theorem binary (cons : Bool) (raw param typ left right rest listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3
      (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) raw typ left right)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode left rest))) :
    Nonempty (Derivation body Delta (graph2 dependency listCode raw param)) :=
  dependencyAt raw param listCode (ArgumentEntriesChildren.InternalProof.internalBinary body alpha Delta cons raw typ left right rest listCode hc hr hl)

theorem numbered (raw param label head typ base types extra rest listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,typ,base,types,extra])))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest extra z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode base rest))) :
    Nonempty (Derivation body Delta (graph2 dependency listCode raw param)) :=
  dependencyAt raw param listCode (ArgumentEntriesChildren.InternalProof.internalNumbered body alpha Delta raw label head typ base types extra rest listCode hc hr hl)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
