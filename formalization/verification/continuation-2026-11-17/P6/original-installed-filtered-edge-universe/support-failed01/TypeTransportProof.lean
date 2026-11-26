module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.TypeTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalTagArithmeticSupportProof (refl)
theorem universe (H : Program 1) (M W : Program 2)
 (left right raw gamma context : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn left right)))
 (ha : Nonempty (Derivation body Delta
   (OriginalUniverseDecoderTransport.Accepted H M W false left raw gamma context))) :
 Nonempty (Derivation body Delta
   (OriginalUniverseDecoderTransport.Accepted H M W false right raw gamma context)) := by
 unfold OriginalUniverseDecoderTransport.Accepted at ha ⊢
 simp only [Bool.false_eq_true, ↓reduceIte] at ha ⊢
 unfold programGraph at ha ⊢
 apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 4 Delta _ (numeral 1)
   ![left,raw,gamma,context] ![right,raw,gamma,context] _ ha
 intro i
 fin_cases i
 · rw [InternalSourceInversionSupportProof.onEquality]
   exact he
 · rw [InternalSourceInversionSupportProof.onEquality]
   exact ⟨refl _⟩
 · rw [InternalSourceInversionSupportProof.onEquality]
   exact ⟨refl _⟩
 · rw [InternalSourceInversionSupportProof.onEquality]
   exact ⟨refl _⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.TypeTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.TypeTransportProof
