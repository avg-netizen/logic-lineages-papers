module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileSelfProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (pairFirst outRaw)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D outReport)
open NumberedWindowInternalLiteralAuxProfileLeastProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem leftOf (p : Program 1) (q value : OTerm α)
    (seen : D B Γ (programGraph p value ![q])) :
    D B Γ (programGraph (pairFirst p) value ![q,suc q]) := by
  apply compositionValue p (Fin.cons (.projection 0) Fin.elim0) value ![q,suc q] ![q] seen
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![q,suc q]

private theorem matchSelf (p : Program 1) (q : OTerm α) :
    D B Γ (programGraph (matchCoordinates p) (suc z) ![q,suc q]) := by
  apply programCases p ![q] _
  intro β j Δ a keep seen
  simp only [programRename,pairRename,sucRelabel,zRelabel]
  rw [inputsRename] at seen
  let r := q.relabel j
  let xs : Fin 2 → OTerm β := ![r,suc r]
  have next : D B Δ (programGraph (decodedOutput p) a xs) := by
    apply compositionValue p (Fin.cons outRaw Fin.elim0) a xs ![r] seen
    intro i
    obtain rfl := Fin.eq_zero i
    exact outReport r r
  unfold matchCoordinates
  rw [exact_DispatchControlAST.2.2.2.1]
  apply compositionValue equalityTest (Fin.cons (pairFirst p) (Fin.cons (decodedOutput p) Fin.elim0))
    (suc z) xs (Fin.cons a (Fin.cons a Fin.elim0)) (equalitySelf a)
  exact fun i => Fin.cases (leftOf p r a seen) (Fin.cases next (fun n => Fin.elim0 n)) i

private theorem fieldsSelf (q : OTerm α) :
    D B Γ (programGraph auxFieldsIfPresent (suc z) ![q,suc q]) := by
  apply optionGraphCases (pairFirst termShape) ![q,suc q] _
  · intro β j Δ keep absent
    simp only [programRename,pairRename,sucRelabel,zRelabel]
    simp only [pairRename,sucRelabel] at absent
    let xs : Fin 2 → OTerm β := ![q.relabel j,suc (q.relabel j)]
    exact zeroBranchIntro (pairFirst termShape) (constantOne 2) fieldMatch (suc z) xs absent (oneConstantValue xs)
  · intro β j Δ p keep present
    simp only [programRename,pairRename,sucRelabel,zRelabel]
    simp only [pairRename,sucRelabel] at present
    let r := q.relabel j
    let xs : Fin 2 → OTerm β := ![r,suc r]
    have tail : D B Δ (programGraph (conjunction (matchCoordinates (field 1)) (matchCoordinates functionHead)) (suc z) xs) := conjunctionAccept (matchCoordinates (field 1)) (matchCoordinates functionHead)
      xs (matchSelf (field 1) r) (matchSelf functionHead r)
    have all : D B Δ (programGraph fieldMatch (suc z) xs) := conjunctionAccept (matchCoordinates (field 0))
      (conjunction (matchCoordinates (field 1)) (matchCoordinates functionHead))
      xs (matchSelf (field 0) r) tail
    exact successorBranchIntro (pairFirst termShape) (constantOne 2) fieldMatch (suc z) p xs present all

/-- Reintroduce the actual auxiliary-profile wrapper at a self
representative. Every checked field comparison is literal reflexivity,
including when the open term is not a known numeral. -/
theorem exact_OpenLiteralAuxProfileSelfLeast (L : Program 3) (ctx ty q : OTerm α)
    (held : D B Γ (programGraph L (suc q) ![ctx,ty,q])) :
    D B Γ (programGraph (auxProfileLeast L) (suc q) ![ctx,ty,q]) := by
  let xs : Fin 2 → OTerm α := ![q,suc q]
  have yes : D B Γ (programGraph auxProfileTest (suc z) xs) := conjunctionAccept (matchCoordinates termShape) auxFieldsIfPresent
    xs (matchSelf termShape q) (fieldsSelf q)
  have kept := successorBranchIntro auxProfileTest (constantZero 2) (.projection 1)
    (suc q) z xs yes (projectionValue 1 xs)
  apply compositionValue retainAuxProfile (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))
    (suc q) ![ctx,ty,q] xs kept
  exact fun i => Fin.cases (projectionValue 2 ![ctx,ty,q])
    (Fin.cases held (fun n => Fin.elim0 n)) i

#print axioms exact_OpenLiteralAuxProfileSelfLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileSelfProof
