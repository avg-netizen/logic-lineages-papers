module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atWindow (seed param context win symbols types : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (hw : Nonempty (Derivation body Delta (graph1 InternalUnpair.left win context)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols seed param)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param))) :
    Nonempty (Derivation body Delta (graph1 OriginalGuardedHeadSourceCoverage.contextSymbols symbols context)) ∧
    Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) := by
  let xs : Fin 2 → OTerm alpha := ![seed,param]
  have hwin := unaryValue InternalUnpair.left OriginalClassCodes.context win context xs hw hc
  have hsymbols := unaryRecover InternalUnpair.left OriginalClassCodes.window symbols win xs hs hwin
  have htypes := unaryRecover InternalUnpair.right OriginalClassCodes.window types win xs ht hwin
  exact ⟨unaryValue InternalUnpair.left InternalUnpair.left symbols win ![context] hsymbols hw,
    unaryValue InternalUnpair.right InternalUnpair.left types win ![context] htypes hw⟩

theorem typesAt (seed param context types : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param))) :
    Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) := by
  apply InternalAcceptanceSupportProof.programCases InternalUnpair.left ![context] _
  intro beta j Theta win hj hw
  have hx : (fun i => (![context] i).relabel j) = ![context.relabel j] := by
    funext i; obtain rfl := Fin.eq_zero i; rfl
  rw [hx] at hw
  rw [graph1Rename]
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  rw [graph2Rename] at hcj htj
  let xs : Fin 2 → OTerm beta := ![seed.relabel j,param.relabel j]
  have hwin := unaryValue InternalUnpair.left OriginalClassCodes.context win (context.relabel j) xs hw hcj
  have htypes := unaryRecover InternalUnpair.right OriginalClassCodes.window (types.relabel j) win xs htj hwin
  exact unaryValue InternalUnpair.right InternalUnpair.left (types.relabel j) win ![context.relabel j] htypes hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
