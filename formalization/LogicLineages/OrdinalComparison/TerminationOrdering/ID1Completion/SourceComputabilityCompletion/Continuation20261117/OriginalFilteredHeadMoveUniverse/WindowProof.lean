module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.SourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.WindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalGuardedHeadSourceCoverage
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rebuild (n : Nat) (arity : Fin n → Nat) (head context symbols types : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)))
    (hh : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)))
    (hs : Nonempty (Derivation body Delta (graph1 contextSymbols symbols context)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)))
    (hm : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) head symbols types))) :
    Nonempty (Derivation body Delta (graph2 (window n arity) (numeral 1) head context)) := by
  have hw := HeadWindowBooleanRange.SourceProof.sourceWindow n arity body alpha Delta head symbols types hm
  apply InternalAcceptanceConjunctionProof.conjunctionAccept _ _ ![head,context]
  · exact unaryValue (OriginalDecodedContextValidity.contextGuard n) (.projection 1) (numeral 1) context ![head,context] hg (projectionValue 1 ![head,context])
  · apply InternalAcceptanceConjunctionProof.conjunctionAccept _ _ ![head,context]
    · exact unaryValue (OriginalHeadDecoderValidity.check n) (.projection 0) (numeral 1) head ![head,context] hh (projectionValue 0 ![head,context])
    · exact ternaryValue (OriginalHeadWindow.window n arity) (.projection 0)
        (.composition contextSymbols (fun _ : Fin 1 => .projection 1))
        (.composition OriginalUniverseDomainCoverage.contextTypes (fun _ : Fin 1 => .projection 1))
        (numeral 1) head symbols types ![head,context] hw (projectionValue 0 ![head,context])
        (unaryValue contextSymbols (.projection 1) symbols context ![head,context] hs (projectionValue 1 ![head,context]))
        (unaryValue OriginalUniverseDomainCoverage.contextTypes (.projection 1) types context ![head,context] ht (projectionValue 1 ![head,context]))

theorem selectors (seed param context symbols types : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols seed param)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param))) :
    Nonempty (Derivation body Delta
      (graph1 contextSymbols symbols context ⊓ graph1 OriginalUniverseDomainCoverage.contextTypes types context)) := by
  apply InternalAcceptanceSupportProof.programCases InternalUnpair.left ![context] _
  intro beta j Theta win hj hw
  have hx : (fun i => (![context] i).relabel j) = ![context.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hw
  have hc' := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  have hs' := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  have ht' := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename] at hc' hs' ht'
  have hw' := unaryValue InternalUnpair.left OriginalClassCodes.context win (context.relabel j) ![seed.relabel j,param.relabel j] hw hc'
  have hsl := unaryRecover InternalUnpair.left OriginalClassCodes.window (symbols.relabel j) win ![seed.relabel j,param.relabel j] hs' hw'
  have htr := unaryRecover InternalUnpair.right OriginalClassCodes.window (types.relabel j) win ![seed.relabel j,param.relabel j] ht' hw'
  simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,InternalApplicationCertificateConstructorsSyntaxProof.graph1Rename]
  exact InternalApplicationStepPeelSupportProof.andIntro
    (unaryValue InternalUnpair.left InternalUnpair.left (symbols.relabel j) win ![context.relabel j] hsl hw)
    (unaryValue InternalUnpair.right InternalUnpair.left (types.relabel j) win ![context.relabel j] htr hw)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.WindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.WindowProof
