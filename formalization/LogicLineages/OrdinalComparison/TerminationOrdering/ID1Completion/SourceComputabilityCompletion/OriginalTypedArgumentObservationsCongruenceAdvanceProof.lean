module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAdvanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsCongruenceAgreementProof
open OriginalTypedArgumentObservationsCongruenceBinaryProof OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] childPacked childObservation typedObservation advance

theorem childForward (R S : Program 2) (parameter input out : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (childObservation R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (childObservation S) out input parameter)) := by
 apply binaryCases childPacked input parameter _
 intro beta j Theta packed hj hp
 rw [graph2Rename]
 have ha' := renameInto ha j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [agreementRename] at ha'
 rw [graph2Rename] at ho'
 let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hproj := projectionValue (body := body) (Gamma := Theta) (1 : Fin 2) xs
 have hraw := binaryRecover R childPacked (.projection 1) (out.relabel j) packed (parameter.relabel j) xs
   (by simpa only [childObservation] using ho') hp hproj
 have hs := agreementForward R S (parameter.relabel j) packed (out.relabel j) ha' hraw
 simpa only [childObservation] using binaryValue S childPacked (.projection 1) (out.relabel j)
   packed (parameter.relabel j) xs hs hp hproj

theorem childAgreement (R S : Program 2) (parameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter))) :
 Nonempty (Derivation body Delta (Agreement (childObservation R) (childObservation S) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta j Theta input left right hj hl hr
 have ha' := renameInto ha j Theta hj
 rw [agreementRename] at ha'
 have hleft := childForward R S (parameter.relabel j) input left ha' hl
 simpa only [equalEqn] using valueUnique (childObservation S) left right
   (Fin.cons input (Fin.cons (parameter.relabel j) Fin.elim0)) hleft hr

theorem advanceAgreement (R S : Program 2) (parameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter))) :
 Nonempty (Derivation body Delta (Agreement (advance R) (advance S) parameter)) := by
 have hc := childAgreement R S parameter ha
 have ht : Nonempty (Derivation body Delta (Agreement (typedObservation R) (typedObservation S) parameter)) := by
   simpa only [typedObservation,pairOf] using binaryAgreement InternalPairing.pairing childType childType
     (childObservation R) (childObservation S) parameter (agreementRefl childType parameter) hc
 have hl : Nonempty (Derivation body Delta (Agreement
   (consOf (typedObservation R) accumulated) (consOf (typedObservation S) accumulated) parameter)) := by
   simpa only [consOf] using binaryAgreement InternalListCodec.consCode (typedObservation R) (typedObservation S)
     accumulated accumulated parameter ht (agreementRefl accumulated parameter)
 simpa only [advance,pairOf] using binaryAgreement InternalPairing.pairing tailRaw tailRaw
   (consOf (typedObservation R) accumulated) (consOf (typedObservation S) accumulated)
   parameter (agreementRefl tailRaw parameter) hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAdvanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAdvanceProof
