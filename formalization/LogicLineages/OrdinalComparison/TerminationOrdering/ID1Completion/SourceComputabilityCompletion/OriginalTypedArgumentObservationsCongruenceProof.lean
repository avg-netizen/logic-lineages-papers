module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceWalkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsCongruenceAgreementProof OriginalTypedArgumentObservationsCongruenceWalkProof
open OriginalTypedArgumentObservationsCongruenceUnaryProof OriginalTypedArgumentObservations
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walked reversedObservations argumentObservations

theorem argumentAgreement (R S : Program 2) (parameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter))) :
 Nonempty (Derivation body Delta (Agreement (argumentObservations R) (argumentObservations S) parameter)) := by
 have hw := walkedAgreement R S parameter ha
 have hr : Nonempty (Derivation body Delta (Agreement (reversedObservations R) (reversedObservations S) parameter)) := by
   simpa only [reversedObservations,rightOf] using unaryAgreement InternalUnpair.right (walked R) (walked S) parameter hw
 simpa only [argumentObservations] using unaryAgreement reverse (reversedObservations R) (reversedObservations S) parameter hr

theorem agreementSymm (R S : Program 2) (parameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter))) :
 Nonempty (Derivation body Delta (Agreement S R parameter)) := by
 apply agreementIntro S R parameter
 intro beta j Theta input left right hj hl hr
 have ha' := renameInto ha j Theta hj
 rw [agreementRename] at ha'
 obtain ⟨he⟩ := agreementApply R S (parameter.relabel j) input right left ha' hr hl
 simpa only [equalEqn] using (Nonempty.intro
   (InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using he)))

theorem actualArgumentCongruence : OriginalTypedArgumentObservationsCongruenceTargets.ArgumentCongruence := by
 intro R S body alpha Delta raw parameter left right
 let A := Agreement R S parameter ⊓
   (graph2 (argumentObservations R) left raw parameter ⊓ graph2 (argumentObservations S) right raw parameter)
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨he⟩ := agreementApply (argumentObservations R) (argumentObservations S) parameter raw left right
   (argumentAgreement R S parameter (andLeft h)) (andLeft (andRight h)) (andRight (andRight h))
 exact ⟨Derivation.implicationIntroduction he⟩

theorem actualArgumentIff : OriginalTypedArgumentObservationsCongruenceTargets.ArgumentIff := by
 intro R S body alpha Delta raw parameter out
 let A := Agreement R S parameter
 let L := graph2 (argumentObservations R) out raw parameter
 let Q := graph2 (argumentObservations S) out raw parameter
 have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hg := argumentAgreement R S parameter ha
 obtain ⟨hf⟩ := agreementForward (argumentObservations R) (argumentObservations S) parameter raw out
   (withHyp hg L) (show Nonempty (Derivation body (L :: A :: Delta) L) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 obtain ⟨hb⟩ := agreementForward (argumentObservations S) (argumentObservations R) parameter raw out
   (withHyp (agreementSymm (argumentObservations R) (argumentObservations S) parameter hg) Q)
   (show Nonempty (Derivation body (Q :: A :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
   (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceProof
