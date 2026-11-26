module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets (singletonTypeKey)
open NumberedWindowInternalCoverSingletonTypeWindowShapeProof (actualOrdinarySingletonShape)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarAt grammarGuard)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase lexicalGuard)
open NumberedWindowInternalCoverNamedResultTargets (namedResultAt namedResultBase namedPositiveResult)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase headBaseAt headPositive storedHeadInGrammar)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase numberedTypeGuard)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase lambdaPositive)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverSingletonTypeWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

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

private theorem toOrdinaryHead (s : Settings) (B : Program 2) (ctx h a result : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (precedingBase s B)
      (suc result) ![ctx,ordinaryKey h a]))) :
    Nonempty (Derivation body Γ (programGraph (headPositive s (headBaseAt true s (numberedTypeBase s B)))
      (suc result) ![ctx,ordinaryKey h a])) := by
  let raw := ordinaryKey h a
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let H := grammarHeadBase s (numberedTypeBase s B)
  let N := namedResultBase H
  let L := lexicalBoundBase N
  let C := namedGrammarAt false s (namedGrammarAt true s L)
  have shape := exact_OpenCoverHeadShape false body α Γ h [a] rfl
  have tag3 := liftRawReport (header 3 1) ctx raw z shape.notTypeLeaf
  have tag0 := liftRawReport (header 0 2) ctx raw z shape.notFree
  have tag1 := liftRawReport (header 1 2) ctx raw z shape.notBound
  have tag4 := liftRawReport (header 4 2) ctx raw (suc z) shape.accepted
  have noType := zeroBranchElim (onRaw (header 3 1)) C (grammarGuard s C) (suc result) xs tag3 actual
  have noFreeK := zeroBranchElim (onRaw (header 0 2)) (namedGrammarAt true s L)
    (grammarGuard s (namedGrammarAt true s L)) (suc result) xs tag0 noType
  have noBoundK := zeroBranchElim (onRaw (header 1 2)) L (grammarGuard s L) (suc result) xs tag1 noFreeK
  have noLex := zeroBranchElim (onRaw (header 1 2)) N
    (branch (normalize lexicalGuard) (constantZero 2) N) (suc result) xs tag1 noBoundK
  have noFreeResult := zeroBranchElim (onRaw (header 0 2)) (namedResultAt true H)
    (namedPositiveResult (namedResultAt true H)) (suc result) xs tag0 noLex
  have headPath := zeroBranchElim (onRaw (header 1 2)) H (namedPositiveResult H) (suc result) xs tag1 noFreeResult
  exact successorBranchElim (onRaw (header 4 2)) (headBaseAt true s (numberedTypeBase s B))
    (headPositive s (headBaseAt true s (numberedTypeBase s B))) (suc result) z xs tag4 headPath

private theorem readType (s : Settings) (ctx raw ty : OTerm α)
    (selector : Nonempty (Derivation body Γ (unary singletonTypeSelector ty raw)))
    (actual : Nonempty (Derivation body Γ (programGraph (onRaw (singletonArgumentTypeAt s)) (suc z) ![ctx,raw]))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  have test : Nonempty (Derivation body Γ (unary (singletonArgumentTypeAt s) (suc z) raw)) := by
    apply compositionRecover (singletonArgumentTypeAt s) (fun _ : Fin 1 => Program.projection 1)
      (suc z) ![ctx,raw] ![raw] actual
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 ![ctx,raw]
  have member : Nonempty (Derivation body Γ (unary (grammarTypeAt s) (suc z) ty)) := by
    apply compositionRecover (grammarTypeAt s) (fun _ : Fin 1 => singletonTypeSelector)
      (suc z) ![raw] ![ty] test
    intro i
    obtain rfl := Fin.eq_zero i
    exact selector
  let code := Encodable.encode s.types
  apply compositionRecover scratchMember ![literal 1 code,.projection 0] (suc z)
    ![ty] ![numeral code,ty] member
  intro i
  exact Fin.cases (literalGraph code ![ty])
    (Fin.cases (projectionValue 0 ![ty]) (fun j => Fin.elim0 j)) i

theorem actualOrdinarySingletonType (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h ty result : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph
      (precedingBase s (lambdaLexicalBase s (ordinarySingletonKBase s B) T))
      (suc result) ![ctx,ordinaryKey h (singletonTypeKey ty)]))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  let B' := ordinarySingletonKBase s B
  let L := lambdaLexicalBase s B' T
  let N := numberedTypeBase s L
  let C := headBaseAt true s N
  let A := onRaw (storedHeadInGrammar s)
  let K := onRaw (singletonArgumentTypeAt s)
  let a := singletonTypeKey ty
  let raw := ordinaryKey h a
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have shape := actualOrdinarySingletonShape (body := body) (Γ := Γ) h ty
  have selected := toOrdinaryHead s L ctx h a result actual
  have headOK := acceptedGuard A C result xs selected
  have passed := successorBranchElim (normalize A) (constantZero 2) C (suc result) z xs
    (normalizeAccept A xs headOK) selected
  have tag5 := liftRawReport (header 5 5) ctx raw z shape.numberedZero
  have tag2 := liftRawReport (header 2 2) ctx raw z shape.lambdaZero
  have gotN := zeroBranchElim (onRaw (header 5 5)) N (headPositive s N) (suc result) xs tag5 passed
  have gotL := zeroBranchElim (onRaw (header 5 5)) L (numberedTypeGuard s L) (suc result) xs tag5 gotN
  have gotB := zeroBranchElim (onRaw (header 2 2)) B' (lambdaPositive s B' T) (suc result) xs tag2 gotL
  have guard := liftRawReport ordinarySingletonGuard ctx raw (suc z) shape.guard
  have checked := successorBranchElim (onRaw ordinarySingletonGuard) B (ordinarySingletonKBranch s B)
    (suc result) z xs guard gotB
  exact readType s ctx raw ty shape.storedType (acceptedGuard K B result xs checked)

#print axioms actualOrdinarySingletonType

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowBaseProof
