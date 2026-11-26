module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SortWeightedDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem nilResult {k : Nat} (Q : Program 2) (F : Program (k+1))
 (raw parameter observations rank : OTerm alpha) (params : Fin k → OTerm alpha)
 (hn : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) observations raw parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw))) :
 Nonempty (Derivation body Delta (programGraph (weighted F) rank (Fin.cons observations params))) := by
 obtain ⟨he⟩ := valueUnique (OriginalTypedArgumentObservations.argumentObservations Q) observations z
   (Fin.cons raw (Fin.cons parameter Fin.elim0)) ho
   (OriginalTypedArgumentObservationsInternalNilProof.nilValue Q raw parameter hn)
 have hz := headTransport (weighted F) z z observations params ⟨symm he⟩
   (SortWeightedFoldProof.nilValue F params)
 have hrz := OriginalRawVariableRankLeafProof.rankNilForward raw rank hn hr
 rw [equalEqn] at hrz
 obtain ⟨hrz⟩ := hrz
 exact outputTransport (weighted F) z rank (Fin.cons observations params) ⟨symm hrz⟩ hz
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentNilProof
