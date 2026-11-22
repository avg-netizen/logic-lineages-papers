module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowBaseOpenProof
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
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm)
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

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem readH (s : Settings) (ctx raw ty : OTerm α)
    (selector : Nonempty (Derivation body Γ (unary (field 0) ty raw)))
    (positive : Nonempty (Derivation body Γ (programGraph (onRaw (storedHeadInGrammar s)) (suc z) ![ctx,raw]))) :
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) ty)) := by
  have test : Nonempty (Derivation body Γ (unary (storedHeadInGrammar s) (suc z) raw)) := by
    apply compositionRecover (storedHeadInGrammar s) (fun _ : Fin 1 => Program.projection 1)
      (suc z) ![ctx,raw] ![raw] positive
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 ![ctx,raw]
  have finite : Nonempty (Derivation body Γ (unary (grammarHeadAt s) (suc z) ty)) := by
    apply compositionRecover (grammarHeadAt s) (fun _ : Fin 1 => field 0) (suc z) ![raw] ![ty] test
    intro i
    obtain rfl := Fin.eq_zero i
    exact selector
  let code := Encodable.encode s.window.2
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

private theorem atBase (b : Bool) (s : Settings) (B : Program 2)
    (ctx h result : OTerm α) (tail : List (OTerm α))
    (shape : HeadKeyReports b body Γ h tail)
    (actual : Nonempty (Derivation body Γ
      (programGraph (grammarHeadBase s B) (suc result) ![ctx,headKey b h tail]))) :
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)) := by
  let raw := headKey b h tail
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let G := onRaw (storedHeadInGrammar s)
  let C := if b then B else headBaseAt true s B
  have checked : Nonempty (Derivation body Γ (programGraph (headPositive s C) (suc result) xs)) := by
    cases b
    · exact successorBranchElim (onRaw (header 4 2)) (headBaseAt true s B)
        (headPositive s (headBaseAt true s B)) (suc result) z xs
        (liftReport (header 4 2) ctx raw (suc z) shape.accepted) actual
    · have numbered := zeroBranchElim (onRaw (header 4 2)) (headBaseAt true s B)
        (headPositive s (headBaseAt true s B)) (suc result) xs
        (liftReport (header 4 2) ctx raw z (shape.notOrdinary rfl)) actual
      exact successorBranchElim (onRaw (header 5 5)) B (headPositive s B) (suc result) z xs
        (liftReport (header 5 5) ctx raw (suc z) shape.accepted) numbered
  let F := programGraph G (suc z) xs
  apply formulaCases F _
  · exact readH s ctx raw h (withHyp shape.fieldHead F) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have rejected := normalizeReject (body := body) (Gamma := F.not :: Γ) G xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := zeroBranchElim (normalize G) (constantZero 2) C
      (suc result) xs rejected (withHyp checked F.not)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc result) z xs zero (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

theorem exact_OpenCoverHeadIntrinsic : ExactOpenCoverHeadIntrinsic := by
  intro b s B body α Γ ctx h result tail length actual
  let raw := headKey b h tail
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let H := grammarHeadBase s B
  let N := namedResultBase H
  let L := lexicalBoundBase N
  let C := namedGrammarAt false s (namedGrammarAt true s L)
  have shape := exact_OpenCoverHeadShape b body α Γ h tail length
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
  have sameHead := zeroBranchElim (onRaw (header 1 2)) H (namedPositiveResult H) (suc result) xs tag1 noFreeResult
  exact atBase b s B ctx h result tail shape sameHead

#print axioms exact_OpenCoverHeadIntrinsic

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowBaseOpenProof
