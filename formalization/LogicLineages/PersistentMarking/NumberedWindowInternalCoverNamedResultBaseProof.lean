module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultLandingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalPathCheckerBranchProof (nonzeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverNamedResultLandingProof (exact_OpenNamedResultLanding)
open NumberedWindowInternalCoverNamedResultTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftReport (P : Program 1) (ctx raw out : OTerm α)
    (seen : Nonempty (Derivation body Γ (unary P out raw))) :
    Nonempty (Derivation body Γ (programGraph (onRaw P) out ![ctx,raw])) := by
  apply compositionValue P (fun _ : Fin 1 => Program.projection 1) out ![ctx,raw] ![raw] seen
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 1 ![ctx,raw]

private theorem physicalType (b : Bool) (ctx ty i : OTerm α) :
    Nonempty (Derivation body Γ (programGraph storedTypeResult (suc ty) ![ctx,namedTerm b.toNat ty i])) := by
  let raw := namedTerm b.toNat ty i
  have shape := exact_OpenCoverNamedLeafIntrinsicShape b body α Γ ty i
  apply compositionValue .succ (fun _ : Fin 1 => onRaw (field 0)) (suc ty) ![ctx,raw] ![ty] (successorValue ![ty])
  intro j
  obtain rfl := Fin.eq_zero j
  exact liftReport (field 0) ctx raw ty shape.2.2.2.1

private theorem fromFallback (B : Program 2) (xs : Fin 2 → OTerm α) (ty result v : OTerm α)
    (fallback : Nonempty (Derivation body Γ (programGraph B v xs)))
    (picked : Nonempty (Derivation body Γ (programGraph (namedPositiveResult B) (suc result) xs)))
    (stored : Nonempty (Derivation body Γ (programGraph storedTypeResult (suc ty) xs))) :
    Nonempty (Derivation body Γ (eqn result ty)) := by
  let F := eqn v z
  apply formulaCases F _
  · have zero : Nonempty (Derivation body (F :: Γ) (programGraph B z xs)) :=
      outputTransport B v z xs ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp fallback F)
    have rejected := zeroBranchElim B (constantZero 2) storedTypeResult (suc result) xs zero (withHyp picked F)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc result) z xs rejected (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · have positive := nonzeroBranchElim B (constantZero 2) storedTypeResult (suc result) v xs
      (withHyp fallback F.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp picked F.not)
    obtain ⟨same⟩ := valueUnique storedTypeResult (suc result) (suc ty) xs positive (withHyp stored F.not)
    exact ⟨cancelSuc same⟩

private theorem typeAt (b : Bool) (B : Program 2) (ctx ty i result : OTerm α)
    (picked : Nonempty (Derivation body Γ (programGraph (namedPositiveResult B) (suc result)
      ![ctx,namedTerm b.toNat ty i]))) : Nonempty (Derivation body Γ (eqn result ty)) := by
  apply programCases B ![ctx,namedTerm b.toNat ty i] _
  intro β j Δ value keep actual
  rw [eqnRelabel]
  simp only [binaryInputsRename,namedRename] at actual
  have sameRow := renameInto picked j Δ keep
  simp only [programRename,sucRelabel,binaryInputsRename,namedRename] at sameRow
  exact fromFallback B ![ctx.relabel j,namedTerm b.toNat (ty.relabel j) (i.relabel j)]
    (ty.relabel j) (result.relabel j) value actual sameRow (physicalType b (ctx.relabel j) (ty.relabel j) (i.relabel j))

theorem exact_OpenCoverNamedResultBase : ExactOpenCoverNamedResultBase := by
  intro b s B body α Γ ctx ty i result actual
  let raw := namedTerm b.toNat ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have shape := exact_OpenCoverNamedLeafIntrinsicShape b body α Γ ty i
  have observed := exact_OpenNamedResultLanding b s B ctx ty i result actual
  cases b
  · have picked := successorBranchElim (onRaw (header 0 2)) (namedResultAt true B)
      (namedPositiveResult (namedResultAt true B)) (suc result) z xs
      (liftReport (header 0 2) ctx raw (suc z) shape.2.2.1) observed
    exact typeAt false (namedResultAt true B) ctx ty i result picked
  · have bound := zeroBranchElim (onRaw (header 0 2)) (namedResultAt true B)
      (namedPositiveResult (namedResultAt true B)) (suc result) xs
      (liftReport (header 0 2) ctx raw z (shape.2.2.2.2.2 rfl)) observed
    have picked := successorBranchElim (onRaw (header 1 2)) B (namedPositiveResult B)
      (suc result) z xs (liftReport (header 1 2) ctx raw (suc z) shape.2.2.1) bound
    exact typeAt true B ctx ty i result picked

#print axioms exact_OpenCoverNamedResultBase

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultBaseProof
