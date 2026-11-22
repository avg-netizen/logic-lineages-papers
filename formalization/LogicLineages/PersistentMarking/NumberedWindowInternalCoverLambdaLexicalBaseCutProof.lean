module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarAt grammarGuard)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase lexicalGuard)
open NumberedWindowInternalCoverNamedResultTargets (namedResultAt namedResultBase namedPositiveResult)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase headBaseAt headPositive)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase numberedTypeGuard)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem liftRawReport (P : Program 1) (ctx raw out : OTerm α)
    (obs : Nonempty (Derivation body Γ (unary P out raw))) :
    Nonempty (Derivation body Γ (programGraph (onRaw P) out ![ctx,raw])) := by
  apply compositionValue P (fun _ : Fin 1 => Program.projection 1) out ![ctx,raw] ![raw] obs
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 1 ![ctx,raw]

/-- A literal λ bypasses all the previously selected layer constructors to
the original deepest fallback, keeping the same actual positive output. -/
theorem actualAtLambdaBase (s : Settings) (B : Program 2) (ctx ty q result : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (precedingBase s B)
       (suc result) ![ctx,lambdaTerm ty q]))) :
    Nonempty (Derivation body Γ (programGraph B (suc result) ![ctx,lambdaTerm ty q])) := by
  let raw := lambdaTerm ty q
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let H := grammarHeadBase s (numberedTypeBase s B)
  let N := namedResultBase H
  let L := lexicalBoundBase N
  let C := namedGrammarAt false s (namedGrammarAt true s L)
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) ty q
  have tag3 := liftRawReport (header 3 1) ctx raw z shape.typeZero
  have tag0 := liftRawReport (header 0 2) ctx raw z shape.freeZero
  have tag1 := liftRawReport (header 1 2) ctx raw z shape.boundZero
  have tag4 := liftRawReport (header 4 2) ctx raw z shape.ordinaryZero
  have tag5 := liftRawReport (header 5 5) ctx raw z shape.numberedZero
  have noType := zeroBranchElim (onRaw (header 3 1)) C (grammarGuard s C) (suc result) xs tag3 actual
  have noFreeK := zeroBranchElim (onRaw (header 0 2)) (namedGrammarAt true s L)
    (grammarGuard s (namedGrammarAt true s L)) (suc result) xs tag0 noType
  have noBoundK := zeroBranchElim (onRaw (header 1 2)) L (grammarGuard s L) (suc result) xs tag1 noFreeK
  have noLex := zeroBranchElim (onRaw (header 1 2)) N
    (branch (normalize lexicalGuard) (constantZero 2) N) (suc result) xs tag1 noBoundK
  have noFreeResult := zeroBranchElim (onRaw (header 0 2)) (namedResultAt true H)
    (namedPositiveResult (namedResultAt true H)) (suc result) xs tag0 noLex
  have headPath := zeroBranchElim (onRaw (header 1 2)) H (namedPositiveResult H) (suc result) xs tag1 noFreeResult
  have nonOrdinary := zeroBranchElim (onRaw (header 4 2)) (headBaseAt true s (numberedTypeBase s B))
    (headPositive s (headBaseAt true s (numberedTypeBase s B))) (suc result) xs tag4 headPath
  have nonNumbered := zeroBranchElim (onRaw (header 5 5)) (numberedTypeBase s B)
    (headPositive s (numberedTypeBase s B)) (suc result) xs tag5 nonOrdinary
  exact zeroBranchElim (onRaw (header 5 5)) B (numberedTypeGuard s B) (suc result) xs tag5 nonNumbered

theorem actualLambdaPositive (s : Settings) (B : Program 2) (T : Program 1) (ctx ty q result : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (precedingBase s (lambdaLexicalBase s B T))
      (suc result) ![ctx,lambdaTerm ty q]))) :
    Nonempty (Derivation body Γ (programGraph (lambdaPositive s B T) (suc result) ![ctx,lambdaTerm ty q])) := by
  let raw := lambdaTerm ty q
  have selected := actualAtLambdaBase s (lambdaLexicalBase s B T) ctx ty q result actual
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) ty q
  exact successorBranchElim (onRaw (header 2 2)) B (lambdaPositive s B T)
    (suc result) z ![ctx,raw] (liftRawReport (header 2 2) ctx raw (suc z) shape.lambdaYes) selected

#print axioms actualAtLambdaBase
#print axioms actualLambdaPositive

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
