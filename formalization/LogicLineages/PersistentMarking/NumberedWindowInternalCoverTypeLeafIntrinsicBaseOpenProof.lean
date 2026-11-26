module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicBaseOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverTypeLeafIntrinsicShapeProof (exact_OpenCoverTypeLeafShape)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem readK (s : Settings) (ctx raw ty : OTerm α)
    (selector : Nonempty (Derivation body Γ (unary (field 0) ty raw)))
    (positive : Nonempty (Derivation body Γ (programGraph (onRaw (leafTypeTest s)) (suc z) ![ctx,raw]))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  have test : Nonempty (Derivation body Γ (unary (leafTypeTest s) (suc z) raw)) := by
    apply compositionRecover (leafTypeTest s) (fun _ : Fin 1 => Program.projection 1)
      (suc z) ![ctx,raw] ![raw] positive
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 ![ctx,raw]
  have finite : Nonempty (Derivation body Γ (unary (grammarTypeAt s) (suc z) ty)) := by
    apply compositionRecover (grammarTypeAt s) (fun _ : Fin 1 => field 0) (suc z) ![raw] ![ty] test
    intro i
    obtain rfl := Fin.eq_zero i
    exact selector
  let code := Encodable.encode s.types
  apply compositionRecover scratchMember ![literal 1 code,.projection 0] (suc z)
    ![ty] ![numeral code,ty] finite
  intro i
  exact Fin.cases (literalGraph code ![ty])
    (Fin.cases (projectionValue 0 ![ty]) (fun j => Fin.elim0 j)) i

theorem exact_OpenCoverTypeLeafIntrinsicBaseK : ExactOpenCoverTypeLeafIntrinsicBaseK := by
  intro s B body α Γ ctx ty result actual
  let raw := typeLeafTerm ty
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let G := onRaw (leafTypeTest s)
  let F := programGraph G (suc z) xs
  have shape := exact_OpenCoverTypeLeafShape body α Γ ty
  have headerAtRow : Nonempty (Derivation body Γ (programGraph (onRaw (header 3 1)) (suc z) xs)) := by
    apply compositionValue (header 3 1) (fun _ : Fin 1 => Program.projection 1)
      (suc z) xs ![raw] shape.2.1
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  have checked := successorBranchElim (onRaw (header 3 1)) B (branch (normalize G) (constantZero 2) B)
    (suc result) z xs headerAtRow actual
  apply formulaCases F _
  · exact readK s ctx raw ty (withHyp shape.2.2 F) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have rejected := normalizeReject (body := body) (Gamma := F.not :: Γ) G xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := zeroBranchElim (normalize G) (constantZero 2) B
      (suc result) xs rejected (withHyp checked F.not)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc result) z xs zero (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

#print axioms exact_OpenCoverTypeLeafIntrinsicBaseK

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicBaseOpenProof
