module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowBaseProof
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
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafIntrinsicBase leafTypeTest onRaw)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarAt grammarGuard)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalGuard lexicalBoundBase)
open NumberedWindowInternalCoverNamedResultTargets (namedResultAt namedResultBase namedPositiveResult)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedWindowBase)
open NumberedWindowInternalCoverHeadWindowTargets
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalCoverNumberedTypeWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem readK (s : Settings) (ctx raw ty : OTerm α)
    (selector : Nonempty (Derivation body Γ (unary (field 1) ty raw)))
    (positive : Nonempty (Derivation body Γ (programGraph (onRaw (numberedGrammarType s)) (suc z) ![ctx,raw]))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  have test : Nonempty (Derivation body Γ (unary (numberedGrammarType s) (suc z) raw)) := by
    apply compositionRecover (numberedGrammarType s) (fun _ : Fin 1 => Program.projection 1)
      (suc z) ![ctx,raw] ![raw] positive
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 ![ctx,raw]
  have finite : Nonempty (Derivation body Γ (unary (grammarTypeAt s) (suc z) ty)) := by
    apply compositionRecover (grammarTypeAt s) (fun _ : Fin 1 => field 1) (suc z) ![raw] ![ty] test
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

private theorem acceptedGuard (P C : Program 2) (res : OTerm α) (xs : Fin 2 → OTerm α)
    (seen : Nonempty (Derivation body Γ
      (programGraph (branch (normalize P) (constantZero 2) C) (suc res) xs))) :
    Nonempty (Derivation body Γ (programGraph P (suc z) xs)) := by
  let F := programGraph P (suc z) xs
  apply formulaCases F F
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have blocked := normalizeReject (body := body) (Gamma := F.not :: Γ) P xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := zeroBranchElim (normalize P) (constantZero 2) C (suc res) xs blocked (withHyp seen F.not)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc res) z xs zero (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

private theorem originalHeadAt (s : Settings) (B : Program 2) (ctx h ty k l r result : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (fittedWindowBase s (grammarHeadBase s B))
      (suc result) ![ctx,numberedTerm h ty k l r]))) :
    Nonempty (Derivation body Γ (programGraph (grammarHeadBase s B) (suc result) ![ctx,numberedTerm h ty k l r])) := by
  let raw := numberedTerm h ty k l r
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let H := grammarHeadBase s B
  let N := namedResultBase H
  let L := lexicalBoundBase N
  let C := namedGrammarAt false s (namedGrammarAt true s L)
  have shape := exact_OpenCoverHeadShape true body α Γ h [ty,k,l,r] rfl
  have tag3 := liftReport (header 3 1) ctx raw z shape.notTypeLeaf
  have tag0 := liftReport (header 0 2) ctx raw z shape.notFree
  have tag1 := liftReport (header 1 2) ctx raw z shape.notBound
  have noType := zeroBranchElim (onRaw (header 3 1)) C (grammarGuard s C) (suc result) xs tag3 actual
  have noFreeK := zeroBranchElim (onRaw (header 0 2)) (namedGrammarAt true s L)
    (grammarGuard s (namedGrammarAt true s L)) (suc result) xs tag0 noType
  have noBoundK := zeroBranchElim (onRaw (header 1 2)) L (grammarGuard s L) (suc result) xs tag1 noFreeK
  have noLex := zeroBranchElim (onRaw (header 1 2)) N
    (branch (normalize lexicalGuard) (constantZero 2) N) (suc result) xs tag1 noBoundK
  have noFreeResult := zeroBranchElim (onRaw (header 0 2)) (namedResultAt true H)
    (namedPositiveResult (namedResultAt true H)) (suc result) xs tag0 noLex
  exact zeroBranchElim (onRaw (header 1 2)) H (namedPositiveResult H) (suc result) xs tag1 noFreeResult

theorem exact_OpenCoverNumberedTypeIntrinsic : ExactOpenCoverNumberedTypeIntrinsic := by
  intro s B body α Γ ctx h ty k l r result actual
  let raw := numberedTerm h ty k l r
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let C := numberedTypeBase s B
  let H := onRaw (storedHeadInGrammar s)
  let K := onRaw (numberedGrammarType s)
  have shape := exact_OpenCoverHeadShape true body α Γ h [ty,k,l,r] rfl
  have noOrdinary := liftReport (header 4 2) ctx raw z (shape.notOrdinary rfl)
  have numberedHeader := liftReport (header 5 5) ctx raw (suc z) shape.accepted
  have atHeads := originalHeadAt s C ctx h ty k l r result actual
  have pickHead := zeroBranchElim (onRaw (header 4 2)) (headBaseAt true s C)
    (headPositive s (headBaseAt true s C)) (suc result) xs noOrdinary atHeads
  have checkHead := successorBranchElim (onRaw (header 5 5)) C (headPositive s C)
    (suc result) z xs numberedHeader pickHead
  have approved := acceptedGuard H C result xs checkHead
  have selected := successorBranchElim (normalize H) (constantZero 2) C (suc result) z xs
    (normalizeAccept H xs approved) checkHead
  have checkType := successorBranchElim (onRaw (header 5 5)) B (numberedTypeGuard s B)
    (suc result) z xs numberedHeader selected
  have valid := acceptedGuard K B result xs checkType
  have tag : Nonempty (Derivation body Γ (unary (literal 1 5) (numeral 5) raw)) := literalGraph 5 ![raw]
  have fields := (packedNode (literal 1 5) (numeral 5) [h,ty,k,l,r] tag).2
  exact readK s ctx raw ty fields.2.1 valid

#print axioms exact_OpenCoverNumberedTypeIntrinsic

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowBaseProof
