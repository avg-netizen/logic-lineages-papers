module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsPairQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryZero (P : Program 1)
 (supply : ∀ (beta : Type) (Theta : List (Formula beta)) (state : OTerm beta),
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing state z z)) →
  Nonempty (Derivation body Theta (graph1 P z z))) :
 Nonempty (Derivation body Delta (graph1 P z z)) := by
 apply programCases InternalPairing.pairing ![z,z] (graph1 P z z)
 intro beta j Theta state hj hp
 rw [graph1Rename,zRelabel]
 exact supply beta Theta state hp

theorem binaryZero (P : Program 2) (Q : Program 0) (raw parameter : OTerm alpha)
 (hq : Nonempty (Derivation body Delta (programGraph Q raw Fin.elim0)))
 (supply : ∀ (beta : Type) (Theta : List (Formula beta)) (state r c : OTerm beta),
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing state r z)) →
   Nonempty (Derivation body Theta (programGraph Q r Fin.elim0)) →
   Nonempty (Derivation body Theta (graph2 P z r c))) :
 Nonempty (Derivation body Delta (graph2 P z raw parameter)) := by
 apply programCases InternalPairing.pairing ![raw,z] (graph2 P z raw parameter)
 intro beta j Theta state hj hp
 rw [graph2Rename,zRelabel]
 have hq' := renameInto hq j Theta hj
 simp only [programRename,emptyRename] at hq'
 exact supply beta Theta state (raw.relabel j) (parameter.relabel j) hp hq'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsPairQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsPairQueryProof
