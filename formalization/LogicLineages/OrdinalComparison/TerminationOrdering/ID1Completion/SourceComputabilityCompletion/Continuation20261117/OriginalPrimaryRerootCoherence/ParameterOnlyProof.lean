module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ParameterOnlyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphSuccessorEliminationProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
attribute [local irreducible] programGraph

/-- Exact graph-output transport for a selector that ignores its first input. -/
def Stable (P : Program 2) : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (seed candidate parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 P out seed parameter)) →
  Nonempty (Derivation body Delta (graph2 P out candidate parameter))

theorem vector2Rename {alpha beta : Type} (a b : OTerm alpha) (j : alpha → beta) :
    (fun i => (![a,b] i).relabel j) = (![a.relabel j,b.relabel j] : Fin 2 → OTerm beta) := by
  funext i
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun z => Fin.elim0 z) k) i

theorem parameter : Stable (.projection 1) := by
  intro body alpha Delta seed candidate parameter out h
  obtain ⟨he⟩ := valueUnique (.projection 1) out parameter ![seed,parameter] h
    (projectionValue 1 ![seed,parameter])
  exact outputTransport (.projection 1) parameter out ![candidate,parameter] ⟨symm he⟩
    (projectionValue 1 ![candidate,parameter])

theorem composition {k : Nat} (P : Program k) (gs : Fin k → Program 2)
    (hg : ∀ i, Stable (gs i)) : Stable (.composition P gs) := by
  intro body alpha Delta seed candidate parameter out h
  apply programCompositionCases P gs out ![seed,parameter] _ h
  intro beta j ys Theta hj ho hi
  rw [graph2Rename]
  rw [vector2Rename] at hi
  exact compositionValue P gs (out.relabel j) ![candidate.relabel j,parameter.relabel j] ys ho
    (fun i => hg i body beta Theta (seed.relabel j) (candidate.relabel j) (parameter.relabel j) (ys i) (hi i))

theorem unary (P : Program 1) (g : Program 2) (hg : Stable g) :
    Stable (.composition P (fun _ => g)) := composition P (fun _ => g) (fun _ => hg)

theorem context : Stable OriginalClassCodes.context := unary InternalUnpair.left (.projection 1) parameter
theorem window : Stable OriginalClassCodes.window := unary InternalUnpair.left OriginalClassCodes.context context
theorem types : Stable OriginalClassCodes.types := unary InternalUnpair.right OriginalClassCodes.window window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ParameterOnlyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ParameterOnlyProof
