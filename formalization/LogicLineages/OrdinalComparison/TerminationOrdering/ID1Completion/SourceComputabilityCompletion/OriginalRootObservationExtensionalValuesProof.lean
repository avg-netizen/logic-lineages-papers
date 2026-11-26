module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalCallProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceAgreementProof
open OriginalTypedArgumentObservationsCongruenceBinaryProof OriginalTypedArgumentObservationsCongruenceUnaryProof
open OriginalRootObservationExtensional OriginalRootObservationExtensionalCallProof
open OriginalRootObservation
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pairAgreement (F G U V : Program 2) (param : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agreement F G param)))
 (hu : Nonempty (Derivation body Delta (Agreement U V param))) :
 Nonempty (Derivation body Delta (Agreement (pairOf F U) (pairOf G V) param)) :=
 binaryAgreement InternalPairing.pairing F G U V param hf hu

theorem taggedAgreement (k : Nat) (F G : Program 2) (param : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Agreement F G param))) :
 Nonempty (Derivation body Delta (Agreement (tagged k F) (tagged k G) param)) :=
 pairAgreement _ _ F G param (agreementRefl _ param) h

theorem typedAgreement (R S typ child childParam : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (typed R typ child childParam) (typed S typ child childParam) param)) :=
 pairAgreement typ typ _ _ param (agreementRefl typ param) (outerCallAgreement R S child childParam param hg)

theorem lambdaAgreement (R S : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (lambda R) (lambda S) param)) := by
 apply taggedAgreement 1 _ _ param
 apply pairAgreement domain domain _ _ param (agreementRefl domain param)
 exact pairAgreement codomain codomain _ _ param (agreementRefl codomain param)
   (typedAgreement R S codomain bodyPacked childParameter param hg)

theorem applicationAgreement (R S : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (OriginalRootObservation.application R) (OriginalRootObservation.application S) param)) := by
 apply taggedAgreement 2 _ _ param
 apply pairAgreement domain domain _ _ param (agreementRefl domain param)
 apply pairAgreement resultType resultType _ _ param (agreementRefl resultType param)
 exact pairAgreement _ _ _ _ param
   (typedAgreement R S (consOf domain resultType) functionPacked parameter param hg)
   (typedAgreement R S domain argumentPacked parameter param hg)

theorem argumentsAgreement (R S A : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (arguments R A) (arguments S A) param)) :=
 fixedCallAgreement _ _ A param
   (OriginalTypedArgumentObservationsCongruenceProof.argumentAgreement R S param (globalAt R S param hg))

theorem sortedArgumentsAgreement (R S A : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (sortedArguments R A) (sortedArguments S A) param)) :=
 unaryAgreement OriginalNumericListSort.sort _ _ param (argumentsAgreement R S A param hg)

theorem ordinaryAgreement (R S : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (ordinary R) (ordinary S) param)) := by
 apply taggedAgreement 4 _ _ param
 apply pairAgreement resultType resultType _ _ param (agreementRefl resultType param)
 exact pairAgreement _ _ _ _ param (agreementRefl (headClass (leftOf payload)) param)
   (sortedArgumentsAgreement R S (rightOf payload) param hg)

theorem numberedAgreement (R S : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (numbered R) (numbered S) param)) := by
 apply taggedAgreement 5 _ _ param
 apply pairAgreement (leftOf payload) (leftOf payload) _ _ param (agreementRefl _ param)
 apply pairAgreement resultType resultType _ _ param (agreementRefl resultType param)
 apply pairAgreement (headClass (leftOf (rightOf payload))) (headClass (leftOf (rightOf payload))) _ _ param (agreementRefl _ param)
 exact pairAgreement _ _ _ _ param
   (sortedArgumentsAgreement R S (leftOf numberedTail) param hg)
   (argumentsAgreement R S (rightOf (rightOf numberedTail)) param hg)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalValuesProof
