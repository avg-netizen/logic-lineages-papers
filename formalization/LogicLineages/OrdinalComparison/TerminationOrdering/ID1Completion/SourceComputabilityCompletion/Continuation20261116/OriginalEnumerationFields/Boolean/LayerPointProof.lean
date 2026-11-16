module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.LayerPointProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalQuotientComparisonProof (orLeft orRight)
open OriginalRawSyntaxTransport
open Continuation20261114.HeadWindowBooleanRange
open ProgramRangeProof PointRange PointBindingProof PointBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem ltRange : Ranged InternalLessThan.ltTest := by
  apply branchRange
  · intro body alpha Delta out xs h
    obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 2) out z xs h (InternalLessThanSupportProof.zeroConstantValue xs)
    exact ⟨orLeft he⟩
  · intro body alpha Delta out xs h
    obtain ⟨he⟩ := valueUnique (InternalLessThan.constantOne 2) out (suc z) xs h (InternalLessThanSupportProof.oneConstantValue xs)
    exact ⟨orRight he⟩

theorem bothAt {k : Nat} (p q : Program k) (xs : Fin k → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (At q xs))) :
    Nonempty (Derivation body Delta (At (both p q) xs)) :=
  branchAt p (constant k 0) q xs (fromRange (constant k 0) xs (constantRange k 0)) hq

theorem chooseAt (n : Nat) (xs : Fin 3 → OTerm alpha)
    (hfirst : Nonempty (Derivation body Delta (At firstAnswer xs)))
    (hsecond : Nonempty (Derivation body Delta (At secondAnswer xs))) :
    Nonempty (Derivation body Delta (At (choose n) xs)) := by
  have hv : Nonempty (Derivation body Delta (At variableBranch xs)) :=
    fromRange variableBranch xs (compositionRange InternalLessThan.ltTest _ ltRange)
  have hb : Nonempty (Derivation body Delta (At bottomBranch xs)) :=
    fromRange bottomBranch xs (compositionRange _ _ containsRange)
  have hl : Nonempty (Derivation body Delta (At lambdaBranch xs)) := bothAt _ _ xs hfirst
  have ho : Nonempty (Derivation body Delta (At (ordinaryBranch n) xs)) := bothAt _ _ xs hfirst
  have hbin : Nonempty (Derivation body Delta (At binaryBranch xs)) := bothAt _ _ xs (bothAt _ _ xs hsecond)
  have hnum : Nonempty (Derivation body Delta (At (numberedBranch n) xs)) := by
    apply bothAt _ _ xs
    apply bothAt _ _ xs
    apply bothAt _ _ xs
    apply bothAt _ _ xs
    apply bothAt _ _ xs
    exact bothAt _ _ xs hsecond
  have hzero := fromRange (constant 3 0) xs (constantRange 3 0) (body := body) (Delta := Delta)
  have hone := fromRange (constant 3 1) xs (constantRange 3 1) (body := body) (Delta := Delta)
  exact branchAt _ _ _ xs
    (branchAt _ _ _ xs
      (branchAt _ _ _ xs
        (branchAt _ _ _ xs
          (branchAt _ _ _ xs
            (branchAt _ _ _ xs
              (branchAt _ _ _ xs
                (branchAt _ _ _ xs hzero hbin) hone) hnum) ho) hb) hbin) hl) hv

theorem payloadAt (n : Nat) (xs : Fin 3 → OTerm alpha)
    (hfirst : Nonempty (Derivation body Delta (At firstAnswer xs)))
    (hsecond : Nonempty (Derivation body Delta (At secondAnswer xs))) :
    Nonempty (Derivation body Delta (At (LayerInternalProof.payload n) xs)) :=
  bothAt _ _ xs (chooseAt n xs hfirst hsecond)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.LayerPointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.LayerPointProof
