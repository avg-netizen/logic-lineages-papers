module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.SymbolsProof
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

theorem symbolsAt (seed param context symbols : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols seed param))) :
    Nonempty (Derivation body Delta (graph1 OriginalGuardedHeadSourceCoverage.contextSymbols symbols context)) := by
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
  have hsymbols := unaryRecover InternalUnpair.left OriginalClassCodes.window (symbols.relabel j) win xs htj hwin
  exact unaryValue InternalUnpair.left InternalUnpair.left (symbols.relabel j) win ![context.relabel j] hsymbols hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.SymbolsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.SymbolsProof
