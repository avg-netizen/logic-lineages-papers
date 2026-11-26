module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicBaseOpenProof
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
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafIntrinsicBase leafTypeTest onRaw)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets

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

private theorem liftReport (P : Program 1) (ctx raw v : OTerm α)
    (actual : Nonempty (Derivation body Γ (unary P v raw))) :
    Nonempty (Derivation body Γ (programGraph (onRaw P) v ![ctx,raw])) := by
  apply compositionValue P (fun _ : Fin 1 => Program.projection 1) v ![ctx,raw] ![raw] actual
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 1 ![ctx,raw]

/-- Physically select the named grammar guard, omitting all fallbacks only
after their actual branch controls have been read on the same tape. -/
theorem exact_OpenNamedGrammarGuardSelected (b : Bool) (s : Settings) (B : Program 2)
    (ctx ty i result : OTerm α)
    (actual : Nonempty (Derivation body Γ
      (programGraph (leafIntrinsicBase s (namedGrammarBase s B)) (suc result) ![ctx,namedTerm b.toNat ty i]))) :
    let callback := if b then B else namedGrammarAt true s B
    Nonempty (Derivation body Γ
      (programGraph (grammarGuard s callback) (suc result) ![ctx,namedTerm b.toNat ty i])) := by
  let raw := namedTerm b.toNat ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have shape := exact_OpenCoverNamedLeafIntrinsicShape b body α Γ ty i
  have named := zeroBranchElim (onRaw (header 3 1)) (namedGrammarBase s B)
    (grammarGuard s (namedGrammarBase s B)) (suc result) xs
    (liftReport (header 3 1) ctx raw z shape.2.1) actual
  cases b
  · exact successorBranchElim (onRaw (header 0 2)) (namedGrammarAt true s B)
      (grammarGuard s (namedGrammarAt true s B)) (suc result) z xs
      (liftReport (header 0 2) ctx raw (suc z) shape.2.2.1) named
  · have bound := zeroBranchElim (onRaw (header 0 2)) (namedGrammarAt true s B)
      (grammarGuard s (namedGrammarAt true s B)) (suc result) xs
      (liftReport (header 0 2) ctx raw z (shape.2.2.2.2.2 rfl)) named
    exact successorBranchElim (onRaw (header 1 2)) B (grammarGuard s B) (suc result) z xs
      (liftReport (header 1 2) ctx raw (suc z) shape.2.2.1) bound

theorem exact_OpenCoverNamedLeafIntrinsicBaseK : ExactOpenCoverNamedLeafIntrinsicBaseK := by
  intro b s B body α Γ ctx ty i result actual
  let raw := namedTerm b.toNat ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let C := if b then B else namedGrammarAt true s B
  let G := onRaw (leafTypeTest s)
  let F := programGraph G (suc z) xs
  have shape := exact_OpenCoverNamedLeafIntrinsicShape b body α Γ ty i
  have checked := exact_OpenNamedGrammarGuardSelected b s B ctx ty i result actual
  apply formulaCases F _
  · exact readK s ctx raw ty (withHyp shape.2.2.2.1 F) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have rejected := normalizeReject (body := body) (Gamma := F.not :: Γ) G xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := zeroBranchElim (normalize G) (constantZero 2) C
      (suc result) xs rejected (withHyp checked F.not)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc result) z xs zero (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

#print axioms exact_OpenNamedGrammarGuardSelected
#print axioms exact_OpenCoverNamedLeafIntrinsicBaseK

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicBaseOpenProof
