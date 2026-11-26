module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsFuelEqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalAdditionLawsProof (add)
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsInternalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walkStep

/-- Two already stationary outputs of the SAME initial walk coincide.
Compare both at the sum of their counts; no subtraction/fuel oracle. -/
theorem stationaryUnique (R : Program 2) (count1 count2 initial parameter out1 out2 : OTerm alpha)
 (hr1 : Nonempty (Derivation body Delta (graph3 (walk R) out1 count1 initial parameter)))
 (hr2 : Nonempty (Derivation body Delta (graph3 (walk R) out2 count2 initial parameter)))
 (hf1 : Nonempty (Derivation body Delta (graph2 (walkStep R) out1 out1 parameter)))
 (hf2 : Nonempty (Derivation body Delta (graph2 (walkStep R) out2 out2 parameter))) :
 Nonempty (Derivation body Delta (eqn out1 out2)) := by
 have h1 := walkPadding R count1 count2 initial out1 parameter hr1 hf1
 have h2 := walkPadding R count2 count1 initial out2 parameter hr2 hf2
 have h2' := headTransport (walk R) out2 (add count2 count1) (add count1 count2)
   (Fin.cons initial (Fin.cons parameter Fin.elim0))
   ⟨InternalAdditionCancellationProof.commutativity count2 count1⟩ h2
 exact valueUnique (walk R) out1 out2
   (Fin.cons (add count1 count2) (Fin.cons initial (Fin.cons parameter Fin.elim0))) h1 h2'

theorem sufficientCountsUnique (R : Program 2)
 (count1 count2 raw acc initial parameter out1 out2 : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial raw acc)))
 (hb1 : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw count1)))
 (hb2 : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw count2)))
 (hr1 : Nonempty (Derivation body Delta (graph3 (walk R) out1 count1 initial parameter)))
 (hr2 : Nonempty (Derivation body Delta (graph3 (walk R) out2 count2 initial parameter))) :
 Nonempty (Derivation body Delta (eqn out1 out2)) :=
 stationaryUnique R count1 count2 initial parameter out1 out2 hr1 hr2
   (OriginalTypedArgumentObservationsTerminationProof.rawTermination R body alpha Delta count1 raw acc initial parameter out1 hb1 hp hr1)
   (OriginalTypedArgumentObservationsTerminationProof.rawTermination R body alpha Delta count2 raw acc initial parameter out2 hb2 hp hr2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsFuelEqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsFuelEqualityProof
