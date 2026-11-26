module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open UniformCertificateCompletion

/-- Literal pre-minimum key; no newly selected minimum or traversal occurs. -/
def source (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
 OriginalUniverseDecoder.source H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W

def Opened {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (value parameter cutoff mark context gamma erasedType deleted erased erasedParam keyValue rank : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing parameter context gamma ⊓
 (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma ⊓
 (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma ⊓
 (OriginalContextInsertion.Insert erasedType cutoff deleted gamma ⊓
 (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased erasedType cutoff value ⊓
 (graph2 InternalPairing.pairing erasedParam context deleted ⊓
 (graph2 (source p H G W) (numeral 1) erased erasedParam ⊓
 (OriginalFunctionNeutrality.windowGraph p.window erased erasedParam ⊓
 (OriginalStructuralClassKeyDefinitions.Active p H G W erased erasedParam ⊓
 (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) keyValue erased erasedParam ⊓
 (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erased ⊓
  graph2 InternalPairing.pairing mark keyValue rank))))))))))

/-- Open a real in-range paired observation and derive erased original
source/window/key activation at the exact deleted context. Every coordinate
is queried internally; neither insertion, activation nor key covariance is
supplied. This is a constructor-law bridge, not full-fold preservation. -/
def ActualOpening : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (value parameter cutoff mark : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) value parameter)) →
 Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window value parameter)) →
 Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)) →
 Nonempty (Derivation body Delta
   (graph3 (OriginalClassContextAllPositionObserver.positionObservation
     (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff value parameter)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (context gamma erasedType deleted erased erasedParam keyValue rank : OTerm beta),
   (∀ h ∈ Delta, h.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (Opened p H G W (value.relabel j) (parameter.relabel j)
     (cutoff.relabel j) (mark.relabel j) context gamma erasedType deleted erased erasedParam keyValue rank)) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningDefinitions
