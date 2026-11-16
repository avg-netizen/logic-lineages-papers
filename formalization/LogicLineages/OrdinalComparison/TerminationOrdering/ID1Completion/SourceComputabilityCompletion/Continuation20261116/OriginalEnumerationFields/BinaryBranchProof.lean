module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BothPointAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaChooseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof SelectorInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forward (xs : Fin 6 → OTerm alpha) (key answers param typ : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (ht : Nonempty (Derivation body Delta (graph3 (leftOf payload) typ key answers param)))
    (hr : Nonempty (Derivation body Delta (Boolean.PointRange.At firstAnswer ![key,answers,param])))
    (hb : Nonempty (Derivation body Delta (graph3 binaryBranch (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ ⊓
      (graph3 firstAnswer (suc z) key answers param ⊓ graph3 secondAnswer (suc z) key answers param))) := by
  have ranged := Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.compositionRange contains
    ![types,leftOf payload] Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.containsRange
  have hm := BothAcceptanceProof.leftOne (typeMember (leftOf payload)) (both firstAnswer secondAnswer) ![key,answers,param] ranged hb
  have hc := binaryRecover contains types (leftOf payload) (suc z) (xs 2) typ ![key,answers,param]
    hm (typesAt xs key answers param hp) ht
  have hi := BothAcceptanceProof.rightOne (typeMember (leftOf payload)) (both firstAnswer secondAnswer) ![key,answers,param] ranged hb
  exact andIntro hc (andIntro
    (BothPointAcceptanceProof.leftOne firstAnswer secondAnswer ![key,answers,param] hr hi)
    (BothPointAcceptanceProof.rightOne firstAnswer secondAnswer ![key,answers,param] hr hi))

theorem backward (xs : Fin 6 → OTerm alpha) (key answers param typ : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (ht : Nonempty (Derivation body Delta (graph3 (leftOf payload) typ key answers param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (hf : Nonempty (Derivation body Delta (graph3 firstAnswer (suc z) key answers param)))
    (hs : Nonempty (Derivation body Delta (graph3 secondAnswer (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph3 binaryBranch (suc z) key answers param)) := by
  have hc := binaryValue contains types (leftOf payload) (suc z) (xs 2) typ ![key,answers,param]
    hm (typesAt xs key answers param hp) ht
  have hi := successorBranchIntro firstAnswer (OriginalRawSyntaxTransport.constant 3 0) secondAnswer (suc z) z ![key,answers,param] hf hs
  exact successorBranchIntro (typeMember (leftOf payload)) (OriginalRawSyntaxTransport.constant 3 0)
    (both firstAnswer secondAnswer) (suc z) z ![key,answers,param] hc hi
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryBranchProof
