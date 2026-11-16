module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafChooseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChildInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BothAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaChooseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof SelectorInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem memberAt (xs : Fin 6 → OTerm alpha) (key answers param domain child value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor (xs 0) domain child)))
    (hm : Nonempty (Derivation body Delta (graph2 contains value (xs 2) domain))) :
    Nonempty (Derivation body Delta (graph3 (typeMember (leftOf payload)) value key answers param)) := by
  have hr := rawAt xs key answers param hk
  have ht := lambdaDomain raw (xs 0) domain child ![key,answers,param] hr hc
  exact binaryValue contains types (leftOf payload) value (xs 2) domain ![key,answers,param]
    hm (typesAt xs key answers param hp) ht

theorem introValue (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param domain child value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor (xs 0) domain child)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) domain)))
    (hv : Nonempty (Derivation body Delta (graph3 firstAnswer value key answers param))) :
    Nonempty (Derivation body Delta (graph3 (choose n) value key answers param)) := by
  have ht := lambdaTag raw (xs 0) domain child ![key,answers,param] (rawAt xs key answers param hk) hc
  apply ChooseInternalProof.tag1Intro n ![key,answers,param] value ht
  exact successorBranchIntro (typeMember (leftOf payload)) (OriginalRawSyntaxTransport.constant 3 0)
    firstAnswer value z ![key,answers,param] (memberAt xs key answers param domain child (suc z) hk hp hc hm) hv

theorem elimValue (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param domain child value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor (xs 0) domain child)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) domain)))
    (hv : Nonempty (Derivation body Delta (graph3 (choose n) value key answers param))) :
    Nonempty (Derivation body Delta (graph3 firstAnswer value key answers param)) := by
  have ht := lambdaTag raw (xs 0) domain child ![key,answers,param] (rawAt xs key answers param hk) hc
  have hb := ChooseInternalProof.tag1Elim n ![key,answers,param] value ht hv
  exact successorBranchElim (typeMember (leftOf payload)) (OriginalRawSyntaxTransport.constant 3 0)
    firstAnswer value z ![key,answers,param] (memberAt xs key answers param domain child (suc z) hk hp hc hm) hb

theorem acceptedMember (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param domain child : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor (xs 0) domain child)))
    (hv : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) domain)) := by
  have hr := rawAt xs key answers param hk
  have ht := lambdaTag raw (xs 0) domain child ![key,answers,param] hr hc
  have hd := lambdaDomain raw (xs 0) domain child ![key,answers,param] hr hc
  have hb := ChooseInternalProof.tag1Elim n ![key,answers,param] (suc z) ht hv
  have hm := BothAcceptanceProof.leftOne (typeMember (leftOf payload)) firstAnswer ![key,answers,param]
    (Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.compositionRange contains _
      Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.containsRange) hb
  exact binaryRecover contains types (leftOf payload) (suc z) (xs 2) domain ![key,answers,param]
    hm (typesAt xs key answers param hp) hd
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaChooseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaChooseProof
