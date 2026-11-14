module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem finalGraphValue (R D : Program 2) (G : Program 3)
    (seed param rankValue table : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R rankValue seed param)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (ExchangeGraphRecursion.graph R D G) table (suc rankValue) seed param))) :
    Nonempty (Derivation body Delta (graph2 (finalGraph R D G) table seed param)) := by
  let xs : Fin 2 → OTerm alpha := ![seed,param]
  have hc := unaryValue .succ R (suc rankValue) rankValue xs
    (successorValue (Fin.cons rankValue Fin.elim0)) hr
  exact ternaryValue (ExchangeGraphRecursion.graph R D G) (count R) (.projection 0) (.projection 1)
    table (suc rankValue) seed param xs ht hc (projectionValue 0 xs) (projectionValue 1 xs)

theorem internalFinalGraph : Targets.InternalFinalGraph := by
  intro body alpha Delta R D G seed param rankValue table out hr ht
  have hf := finalGraphValue R D G seed param rankValue table hr ht
  constructor
  · intro h
    apply compositionRecover extract (fun _ : Fin 1 => finalGraph R D G)
      out ![seed,param] (Fin.cons table Fin.elim0) h
    intro i
    exact Fin.cases hf (fun k => Fin.elim0 k) i
  · intro h
    exact unaryValue extract (finalGraph R D G) out table ![seed,param] h hf

theorem extractSingleton (seed table pair value : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair seed value))) :
    Nonempty (Derivation body Delta (graph1 extract value table)) := by
  obtain ⟨hh⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalListCodecProof.actualOriginalConsDestruction body alpha table pair z) hc
  obtain ⟨hu⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha pair seed value) hp
  exact unaryValue InternalUnpair.right InternalListCodec.headCode value pair ![table]
    ⟨Derivation.conjunctionRight hu⟩ ⟨Derivation.conjunctionLeft hh⟩

theorem internalSingletonValue : Targets.InternalSingletonValue := by
  intro body alpha Delta R D G seed param rankValue table pair value hr ht hc hp
  exact (internalFinalGraph body alpha Delta R D G seed param rankValue table value hr ht).mpr
    (extractSingleton seed table pair value hc hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.InternalProof
