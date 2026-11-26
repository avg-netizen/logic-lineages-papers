module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundGuardIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundExtraShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundBaseRebuildProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest)
open NumberedWindowInternalCoverLexicalSlotTargets (slotCheck)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalGuard lexicalBoundBase)
open NumberedWindowInternalCoverNamedResultTargets (storedTypeResult namedResultAt namedResultBase namedPositiveResult)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (grammarGuard namedGrammarAt namedGrammarBase)
open NumberedWindowInternalCoverHeadWindowTargets (headBaseAt headPositive grammarHeadBase)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeGuard numberedTypeBase)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverLambdaBoundExtraShapeProof (actualLambdaBoundExtraShape)
open NumberedWindowInternalCoverLambdaBoundGuardIntroProof
  (introduceBoundGrammarGuard introduceBoundLexicalGuard introduceBoundStoredResult)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Reinstall the very same original positive B report in the new callback.
A literal bound key physically rejects ordinary, numbered, and λ headers. -/
private theorem pushOldB (s : Settings) (B : Program 2) (T : Program 1) (ctx ty i v : OTerm α)
    (old : Nonempty (Derivation body Γ (programGraph B (suc v) ![ctx,namedTerm 1 ty i]))) :
    Nonempty (Derivation body Γ (programGraph (grammarHeadBase s (numberedTypeBase s (lambdaLexicalBase s B T)))
      (suc v) ![ctx,namedTerm 1 ty i])) := by
  let raw := namedTerm 1 ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let L := lambdaLexicalBase s B T
  let N := numberedTypeBase s L
  have shape := actualLambdaBoundExtraShape (body := body) (Γ := Γ) ty i
  have tag2 := liftRawReport (header 2 2) ctx raw z shape.lambdaZero
  have tag4 := liftRawReport (header 4 2) ctx raw z shape.ordinaryZero
  have tag5 := liftRawReport (header 5 5) ctx raw z shape.numberedZero
  have intoL := zeroBranchIntro (onRaw (header 2 2)) B (lambdaPositive s B T) (suc v) xs tag2 old
  have intoN := zeroBranchIntro (onRaw (header 5 5)) L (numberedTypeGuard s L) (suc v) xs tag5 intoL
  have intoH := zeroBranchIntro (onRaw (header 5 5)) N (headPositive s N) (suc v) xs tag5 intoN
  exact zeroBranchIntro (onRaw (header 4 2)) (headBaseAt true s N)
    (headPositive s (headBaseAt true s N)) (suc v) xs tag4 intoH

theorem rebuildSelectedBoundBase (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result v : OTerm α)
    (old : Nonempty (Derivation body Γ (programGraph B (suc v) ![ctx,namedTerm 1 ty i])))
    (inK : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (typedSlot : Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty])))
    (same : Nonempty (Derivation body Γ (eqn result ty))) :
    Nonempty (Derivation body Γ (programGraph (precedingBase s (lambdaLexicalBase s B T))
      (suc result) ![ctx,namedTerm 1 ty i])) := by
  let raw := namedTerm 1 ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let H := grammarHeadBase s (numberedTypeBase s (lambdaLexicalBase s B T))
  let N := namedResultBase H
  let L := lexicalBoundBase N
  let C := namedGrammarBase s L
  let G := onRaw (leafTypeTest s)
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
  have tag3 := liftRawReport (header 3 1) ctx raw z shape.2.1
  have tag0 := liftRawReport (header 0 2) ctx raw z (shape.2.2.2.2.2 rfl)
  have tag1 := liftRawReport (header 1 2) ctx raw (suc z) shape.2.2.1
  have original := pushOldB s B T ctx ty i v old
  have value := introduceBoundStoredResult ctx ty i result same
  have chosen := successorBranchIntro H (constantZero 2) storedTypeResult (suc result) v xs original value
  have resultBound := successorBranchIntro (onRaw (header 1 2)) H (namedPositiveResult H)
    (suc result) z xs tag1 chosen
  have resultNamed := zeroBranchIntro (onRaw (header 0 2)) (namedResultAt true H)
    (namedPositiveResult (namedResultAt true H)) (suc result) xs tag0 resultBound
  have slot := introduceBoundLexicalGuard ctx ty i typedSlot
  have memoSlot := successorBranchIntro (normalize lexicalGuard) (constantZero 2) N (suc result) z xs
    (normalizeAccept lexicalGuard xs slot) resultNamed
  have lex := successorBranchIntro (onRaw (header 1 2)) N (branch (normalize lexicalGuard) (constantZero 2) N)
    (suc result) z xs tag1 memoSlot
  have ok := introduceBoundGrammarGuard s ctx ty i inK
  have memberBranch : Nonempty (Derivation body Γ (programGraph (grammarGuard s L) (suc result) xs)) :=
    successorBranchIntro (normalize G) (constantZero 2) L (suc result) z xs (normalizeAccept G xs ok) lex
  have inner := successorBranchIntro (onRaw (header 1 2)) L (grammarGuard s L) (suc result) z xs tag1 memberBranch
  have named := zeroBranchIntro (onRaw (header 0 2)) (namedGrammarAt true s L)
    (grammarGuard s (namedGrammarAt true s L)) (suc result) xs tag0 inner
  exact zeroBranchIntro (onRaw (header 3 1)) C (grammarGuard s C) (suc result) xs tag3 named

#print axioms rebuildSelectedBoundBase

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundBaseRebuildProof
