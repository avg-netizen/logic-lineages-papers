module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BothPointAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedControlsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport
open Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def labelTest : Program 3 := .composition InternalLessThan.ltTest ![numberedLabel,succOf labels]
def headTest (n : Nat) : Program 3 := headMember n numberedHead
def typeTest : Program 3 := typeMember numberedType
def lengthTest : Program 3 := .composition InternalLessThan.ltTest
  ![.composition OriginalContextInsertion.length ![numberedTypes],succOf tupleBound]
def typesTest : Program 3 := .composition allTypes ![numberedTypes,types]
def tail5 : Program 3 := both typesTest secondAnswer
def tail4 : Program 3 := both lengthTest tail5
def tail3 : Program 3 := both firstAnswer tail4
def tail2 : Program 3 := both typeTest tail3
def tail1 (n : Nat) : Program 3 := both (headTest n) tail2

theorem forward (n : Nat) (xs : Fin 3 → OTerm alpha)
    (hr : Nonempty (Derivation body Delta (Boolean.PointRange.At firstAnswer xs)))
    (hv : Nonempty (Derivation body Delta (programGraph (numberedBranch n) (suc z) xs))) :
    Nonempty (Derivation body Delta
      ((((((programGraph labelTest (suc z) xs ⊓ programGraph (headTest n) (suc z) xs) ⊓
        programGraph typeTest (suc z) xs) ⊓ programGraph firstAnswer (suc z) xs) ⊓
        programGraph lengthTest (suc z) xs) ⊓ programGraph typesTest (suc z) xs) ⊓ programGraph secondAnswer (suc z) xs)) := by
  have r0 : Ranged labelTest := compositionRange _ _ Boolean.LayerPointProof.ltRange
  have r1 : Ranged (headTest n) := compositionRange _ _ containsRange
  have r2 : Ranged typeTest := compositionRange _ _ containsRange
  have r4 : Ranged lengthTest := compositionRange _ _ Boolean.LayerPointProof.ltRange
  have r5 : Ranged typesTest := compositionRange _ _ Types.Range.Proof.allTypesRange
  have h0 := BothAcceptanceProof.leftOne labelTest (tail1 n) xs r0 hv
  have t1 := BothAcceptanceProof.rightOne labelTest (tail1 n) xs r0 hv
  have h1 := BothAcceptanceProof.leftOne (headTest n) tail2 xs r1 t1
  have t2 := BothAcceptanceProof.rightOne (headTest n) tail2 xs r1 t1
  have h2 := BothAcceptanceProof.leftOne typeTest tail3 xs r2 t2
  have t3 := BothAcceptanceProof.rightOne typeTest tail3 xs r2 t2
  have h3 := BothPointAcceptanceProof.leftOne firstAnswer tail4 xs hr t3
  have t4 := BothPointAcceptanceProof.rightOne firstAnswer tail4 xs hr t3
  have h4 := BothAcceptanceProof.leftOne lengthTest tail5 xs r4 t4
  have t5 := BothAcceptanceProof.rightOne lengthTest tail5 xs r4 t4
  have h5 := BothAcceptanceProof.leftOne typesTest secondAnswer xs r5 t5
  have h6 := BothAcceptanceProof.rightOne typesTest secondAnswer xs r5 t5
  exact andIntro (andIntro (andIntro (andIntro (andIntro (andIntro h0 h1) h2) h3) h4) h5) h6

theorem backward (n : Nat) (xs : Fin 3 → OTerm alpha)
    (h0 : Nonempty (Derivation body Delta (programGraph labelTest (suc z) xs)))
    (h1 : Nonempty (Derivation body Delta (programGraph (headTest n) (suc z) xs)))
    (h2 : Nonempty (Derivation body Delta (programGraph typeTest (suc z) xs)))
    (h3 : Nonempty (Derivation body Delta (programGraph firstAnswer (suc z) xs)))
    (h4 : Nonempty (Derivation body Delta (programGraph lengthTest (suc z) xs)))
    (h5 : Nonempty (Derivation body Delta (programGraph typesTest (suc z) xs)))
    (h6 : Nonempty (Derivation body Delta (programGraph secondAnswer (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph (numberedBranch n) (suc z) xs)) := by
  have t5 := successorBranchIntro typesTest (constant 3 0) secondAnswer (suc z) z xs h5 h6
  have t4 := successorBranchIntro lengthTest (constant 3 0) tail5 (suc z) z xs h4 t5
  have t3 := successorBranchIntro firstAnswer (constant 3 0) tail4 (suc z) z xs h3 t4
  have t2 := successorBranchIntro typeTest (constant 3 0) tail3 (suc z) z xs h2 t3
  have t1 := successorBranchIntro (headTest n) (constant 3 0) tail2 (suc z) z xs h1 t2
  exact successorBranchIntro labelTest (constant 3 0) (tail1 n) (suc z) z xs h0 t1
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedControlsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedControlsProof
