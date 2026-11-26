module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightDeletionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalHereditaryInternalWeightDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalHereditaryInternalWeightValueProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)

theorem deletion : OriginalHereditaryInternalWeightTargets.Deletion := by
 intro body alpha Delta parent child input erased gamma deleted typ cutoff count before after W V hp hc he hb ha hl hk hd hw hv
 obtain ⟨hinv⟩ := OriginalStructuralNodeSizeInternalErasureProof.actualInternalErasureInvariant
   body alpha Delta input erased typ cutoff before after
 obtain ⟨hall⟩ := andIntro he (andIntro hb ha)
 have hcounts : Derivation body Delta (eqn before after) := by
   simpa only [equalEqn] using Derivation.implicationElimination hinv hall
 have hnew : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw before erased)) :=
   outputTransport OriginalStructuralNodeSize.raw after before (Fin.cons erased Fin.elim0) ⟨symm hcounts⟩ ha
 have hlen := OriginalAllPositionContextDeleteLengthProof.deleteLength gamma count cutoff deleted hl hk hd
 exact InternalOriginalPairingOrderArithmeticProof.strictTransport V W (mass count before) (mass (suc count) before)
   (weightEqual child erased deleted count before V hc hlen hnew hv)
   (weightEqual parent input gamma (suc count) before W hp hl hb hw)
   (OriginalHereditaryInternalWeightArithmeticProof.deletion count before)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightDeletionProof
