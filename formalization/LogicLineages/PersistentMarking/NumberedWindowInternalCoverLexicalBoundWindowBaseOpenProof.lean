module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicBaseOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowBaseOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (grammarGuard)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverNamedLeafIntrinsicBaseOpenProof (exact_OpenNamedGrammarGuardSelected)
open NumberedWindowInternalCoverLexicalSlotTargets (slotCheck)
open NumberedWindowInternalCoverLexicalBoundWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem acceptedGuard (P C : Program 2) (result : OTerm α) (xs : Fin 2 → OTerm α)
    (checked : Nonempty (Derivation body Γ
      (programGraph (branch (normalize P) (constantZero 2) C) (suc result) xs))) :
    Nonempty (Derivation body Γ (programGraph P (suc z) xs)) := by
  let F := programGraph P (suc z) xs
  apply formulaCases F F
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have rejected := normalizeReject (body := body) (Gamma := F.not :: Γ) P xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := zeroBranchElim (normalize P) (constantZero 2) C (suc result) xs rejected
      (withHyp checked F.not)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc result) z xs zero (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

private theorem liftReport (P : Program 1) (out ctx raw : OTerm α)
    (seen : Nonempty (Derivation body Γ (unary P out raw))) :
    Nonempty (Derivation body Γ (programGraph (onRaw P) out ![ctx,raw])) := by
  apply compositionValue P (fun _ : Fin 1 => Program.projection 1) out ![ctx,raw] ![raw] seen
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 1 ![ctx,raw]

theorem exact_OpenCoverLexicalBoundBaseSlot : ExactOpenCoverLexicalBoundBaseSlot := by
  intro s B body α Γ ctx ty i result actual
  let raw := namedTerm 1 ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let C := lexicalBoundBase B
  let G := onRaw (leafTypeTest s)
  have guarded : Nonempty (Derivation body Γ (programGraph (grammarGuard s C) (suc result) xs)) :=
    exact_OpenNamedGrammarGuardSelected true s C ctx ty i result actual
  have guardHit := acceptedGuard G C result xs guarded
  have inner := successorBranchElim (normalize G) (constantZero 2) C (suc result) z xs
    (normalizeAccept G xs guardHit) guarded
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
  have bound := successorBranchElim (onRaw (header 1 2)) B
    (branch (normalize lexicalGuard) (constantZero 2) B) (suc result) z xs
    (liftReport (header 1 2) (suc z) ctx raw shape.2.2.1) inner
  have slot := acceptedGuard lexicalGuard B result xs bound
  apply compositionRecover slotCheck ![onRaw (field 1),.projection 0,onRaw (field 0)]
    (suc z) xs ![i,ctx,ty] slot
  intro j
  exact Fin.cases (liftReport (field 1) i ctx raw shape.2.2.2.2.1)
    (Fin.cases (projectionValue 0 xs)
      (Fin.cases (liftReport (field 0) ty ctx raw shape.2.2.2.1) (fun k => Fin.elim0 k))) j

#print axioms exact_OpenCoverLexicalBoundBaseSlot

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowBaseOpenProof
