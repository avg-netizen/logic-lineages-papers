module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowBasePeelProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarAt grammarGuard)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase lexicalGuard)
open NumberedWindowInternalCoverNamedResultTargets (namedResultAt namedResultBase namedPositiveResult)
open NumberedWindowInternalCoverHeadWindowTargets
  (headKey headArity grammarHeadBase headBaseAt headPositive storedHeadInGrammar)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase numberedTypeGuard numberedGrammarType)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase lambdaPositive)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalCoverRestrictedListWindowShapeProof (lambdaRejectHeadKey numberedRejectOrdinaryKey)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualGuardReport (P C : Program 2) (res : OTerm α) (xs : Fin 2 → OTerm α)
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

private theorem peelAtomic (b : Bool) (s : Settings) (B : Program 2) (ctx h result : OTerm α)
    (tail : List (OTerm α)) (len : (h::tail).length = headArity b)
    (actual : Nonempty (Derivation body Γ (programGraph (precedingBase s B)
      (suc result) ![ctx,headKey b h tail]))) :
    Nonempty (Derivation body Γ (programGraph (grammarHeadBase s (numberedTypeBase s B))
      (suc result) ![ctx,headKey b h tail])) := by
  let raw := headKey b h tail
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let H := grammarHeadBase s (numberedTypeBase s B)
  let N := namedResultBase H
  let L := lexicalBoundBase N
  let C := namedGrammarAt false s (namedGrammarAt true s L)
  have shape := exact_OpenCoverHeadShape b body α Γ h tail len
  have tag3 := liftRawReport (header 3 1) ctx raw z shape.notTypeLeaf
  have tag0 := liftRawReport (header 0 2) ctx raw z shape.notFree
  have tag1 := liftRawReport (header 1 2) ctx raw z shape.notBound
  have noType := zeroBranchElim (onRaw (header 3 1)) C (grammarGuard s C) (suc result) xs tag3 actual
  have noFreeK := zeroBranchElim (onRaw (header 0 2)) (namedGrammarAt true s L)
    (grammarGuard s (namedGrammarAt true s L)) (suc result) xs tag0 noType
  have noBoundK := zeroBranchElim (onRaw (header 1 2)) L (grammarGuard s L) (suc result) xs tag1 noFreeK
  have noLex := zeroBranchElim (onRaw (header 1 2)) N
    (branch (normalize lexicalGuard) (constantZero 2) N) (suc result) xs tag1 noBoundK
  have noFreeResult := zeroBranchElim (onRaw (header 0 2)) (namedResultAt true H)
    (namedPositiveResult (namedResultAt true H)) (suc result) xs tag0 noLex
  exact zeroBranchElim (onRaw (header 1 2)) H (namedPositiveResult H) (suc result) xs tag1 noFreeResult

private theorem useHeadGuard (s : Settings) (B : Program 2) (ctx raw result : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (headPositive s B) (suc result) ![ctx,raw]))) :
    Nonempty (Derivation body Γ (programGraph B (suc result) ![ctx,raw])) := by
  let A := onRaw (storedHeadInGrammar s)
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have ok := actualGuardReport A B result xs actual
  exact successorBranchElim (normalize A) (constantZero 2) B (suc result) z xs
    (normalizeAccept A xs ok) actual

theorem peelOrdinarySelectedBase (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h a result : OTerm α)
    (seen : Nonempty (Derivation body Γ (programGraph (precedingBase s (lambdaLexicalBase s B T))
      (suc result) ![ctx,(headKey false h [a])]))) :
    Nonempty (Derivation body Γ (programGraph B (suc result) ![ctx,(headKey false h [a])])) := by
  let raw := headKey false h [a]
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let L := lambdaLexicalBase s B T
  let N := numberedTypeBase s L
  let C := headBaseAt true s N
  have shape := exact_OpenCoverHeadShape false body α Γ h [a] rfl
  have head := peelAtomic false s L ctx h result [a] rfl seen
  have tag4 := liftRawReport (header 4 2) ctx raw (suc z) shape.accepted
  have tag5 := liftRawReport (header 5 5) ctx raw z (numberedRejectOrdinaryKey (body := body) (Γ := Γ) h a)
  have tag2 := liftRawReport (header 2 2) ctx raw z (lambdaRejectHeadKey (body := body) (Γ := Γ) false h [a])
  have guarded := successorBranchElim (onRaw (header 4 2)) C (headPositive s C) (suc result) z xs tag4 head
  have passed := useHeadGuard s C ctx raw result guarded
  have num := zeroBranchElim (onRaw (header 5 5)) N (headPositive s N) (suc result) xs tag5 passed
  have lam := zeroBranchElim (onRaw (header 5 5)) L (numberedTypeGuard s L) (suc result) xs tag5 num
  exact zeroBranchElim (onRaw (header 2 2)) B (lambdaPositive s B T) (suc result) xs tag2 lam

theorem peelNumberedSelectedBase (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h ty k l r result : OTerm α)
    (seen : Nonempty (Derivation body Γ (programGraph (precedingBase s (lambdaLexicalBase s B T))
      (suc result) ![ctx,(headKey true h [ty,k,l,r])]))) :
    Nonempty (Derivation body Γ (programGraph B (suc result) ![ctx,(headKey true h [ty,k,l,r])])) := by
  let raw := headKey true h [ty,k,l,r]
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let L := lambdaLexicalBase s B T
  let N := numberedTypeBase s L
  let C := headBaseAt true s N
  let K := onRaw (numberedGrammarType s)
  have shape := exact_OpenCoverHeadShape true body α Γ h [ty,k,l,r] rfl
  have head := peelAtomic true s L ctx h result [ty,k,l,r] rfl seen
  have tag4 := liftRawReport (header 4 2) ctx raw z (shape.notOrdinary rfl)
  have tag5 := liftRawReport (header 5 5) ctx raw (suc z) shape.accepted
  have tag2 := liftRawReport (header 2 2) ctx raw z (lambdaRejectHeadKey (body := body) (Γ := Γ) true h [ty,k,l,r])
  have checked := zeroBranchElim (onRaw (header 4 2)) C (headPositive s C) (suc result) xs tag4 head
  have guarded := successorBranchElim (onRaw (header 5 5)) N (headPositive s N) (suc result) z xs tag5 checked
  have passed := useHeadGuard s N ctx raw result guarded
  have stored := successorBranchElim (onRaw (header 5 5)) L (numberedTypeGuard s L) (suc result) z xs tag5 passed
  have ok := actualGuardReport K L result xs stored
  have lam := successorBranchElim (normalize K) (constantZero 2) L (suc result) z xs
    (normalizeAccept K xs ok) stored
  exact zeroBranchElim (onRaw (header 2 2)) B (lambdaPositive s B T) (suc result) xs tag2 lam

#print axioms peelOrdinarySelectedBase
#print axioms peelNumberedSelectedBase

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowBasePeelProof
