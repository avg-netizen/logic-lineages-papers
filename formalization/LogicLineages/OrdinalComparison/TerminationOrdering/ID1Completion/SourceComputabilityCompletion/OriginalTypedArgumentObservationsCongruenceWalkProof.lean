module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceWalkProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn suc sucRelabel)
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsWalkQueryProof
open OriginalTypedArgumentObservationsCongruenceAgreementProof OriginalTypedArgumentObservationsCongruenceStepProof
open OriginalTypedArgumentObservationsCongruenceIterationProof OriginalTypedArgumentObservations
open OriginalUniverseDecoderInternalFuelNumericSyntaxProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue ternaryRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walked walkStep

theorem walkForward (R S : Program 2) (count state parameter out : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (ho : Nonempty (Derivation body Delta (graph3 (walk R) out count state parameter))) :
 Nonempty (Derivation body Delta (graph3 (walk S) out count state parameter)) := by
 apply ternaryCases (walk S) count state parameter _
 intro beta j Theta other hj hv
 rw [graph3Rename]
 have ha' := renameInto ha j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [agreementRename] at ha'
 rw [graph3Rename] at ho'
 have he : Nonempty (Derivation body Theta (equal (out.relabel j) other)) := by
   apply iterationValues (walkStep R) (walkStep S) (count.relabel j) (state.relabel j) (parameter.relabel j) (out.relabel j) other
   · exact stepAgreement R S (parameter.relabel j) ha'
   · simpa only [walk,repeatGraph,repeatProgram,repeatStep] using ho'
   · simpa only [walk,repeatGraph,repeatProgram,repeatStep] using hv
 obtain ⟨he⟩ := he
 have he' : Nonempty (Derivation body Theta (eqn other (out.relabel j))) :=
   ⟨InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using he)⟩
 exact outputTransport (walk S) other (out.relabel j)
   (Fin.cons (count.relabel j) (Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) he' hv

theorem walkedForward (R S : Program 2) (parameter input out : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (walked R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (walked S) out input parameter)) := by
 apply binaryCases initial input parameter _
 intro beta j Theta state hj hi
 rw [graph2Rename]
 have ha' := renameInto ha j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [agreementRename] at ha'
 rw [graph2Rename] at ho'
 let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hf := unaryValue (body := body) (Gamma := Theta) .succ (.projection (0 : Fin 2))
   (suc (input.relabel j)) (input.relabel j) xs
   (successorValue (Fin.cons (input.relabel j) Fin.elim0)) (projectionValue 0 xs)
 have hp := projectionValue (body := body) (Gamma := Theta) (1 : Fin 2) xs
 have hr := ternaryRecover (walk R) (OriginalRawSyntaxTransport.succOf (.projection 0)) initial (.projection 1)
   (out.relabel j) (suc (input.relabel j)) state (parameter.relabel j) xs
   (by simpa only [walked] using ho') hf hi hp
 have hs := walkForward R S (suc (input.relabel j)) state (parameter.relabel j) (out.relabel j) ha' hr
 simpa only [walked] using ternaryValue (walk S) (OriginalRawSyntaxTransport.succOf (.projection 0)) initial (.projection 1)
   (out.relabel j) (suc (input.relabel j)) state (parameter.relabel j) xs hs hf hi hp

theorem walkedAgreement (R S : Program 2) (parameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter))) :
 Nonempty (Derivation body Delta (Agreement (walked R) (walked S) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta j Theta input left right hj hl hr
 have ha' := renameInto ha j Theta hj
 rw [agreementRename] at ha'
 have hleft := walkedForward R S (parameter.relabel j) input left ha' hl
 simpa only [equalEqn] using valueUnique (walked S) left right
   (Fin.cons input (Fin.cons (parameter.relabel j) Fin.elim0)) hleft hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceWalkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceWalkProof
