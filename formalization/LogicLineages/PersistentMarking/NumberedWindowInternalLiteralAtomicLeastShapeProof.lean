module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename packedBody)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm freeReports)
open NumberedWindowInternalLiteralAtomicLeastGuardProof
  (atomicTest pairFirst outRaw outAtom checkAtom checkSame keepAtom atomOutput guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D outReport rejectZeroOutput exact_OpenAtomicLeastReport)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

theorem freeAtom (t n : OTerm α) : D B Γ (unary atomicTest (suc z) (freeTerm t n)) :=
  successorBranchIntro freeTest bottomTest (literal 1 1) (suc z) z ![freeTerm t n]
    (freeReports t n).1 (literalGraph 1 ![freeTerm t n])

theorem bottomAtom (t : OTerm α) : D B Γ (unary atomicTest (suc z) (bottomTerm t)) := by
  let code := bottomTerm t
  have tag : D B Γ (unary (literal 1 3) (numeral 3) (rawCons (numeral 3) (packedBody [t]))) := by
    unfold unary
    exact literalGraph 3 _
  have bottom : D B Γ (programGraph bottomTest (suc z) ![code]) :=
    (packedNode (body := B) (Γ := Γ) (literal 1 3) (numeral 3) [t] tag).1
  change D B Γ (programGraph atomicTest (suc z) ![code])
  apply optionGraphCases freeTest ![code] (programGraph atomicTest (suc z) ![code])
  · intro β j Δ keep free
    rw [programRename,inputsRename,sucRelabel,zRelabel]
    rw [inputsRename] at free
    have held := renameInto bottom j Δ keep
    simp only [programRename,inputsRename,sucRelabel,zRelabel] at held
    exact zeroBranchIntro freeTest bottomTest (literal 1 1) (suc z) ![code.relabel j] free held
  · intro β j Δ pred keep free
    rw [programRename,inputsRename,sucRelabel,zRelabel]
    rw [inputsRename] at free
    exact successorBranchIntro freeTest bottomTest (literal 1 1) (suc z) pred ![code.relabel j] free
      (literalGraph 1 ![code.relabel j])

private theorem firstAtom (q t : OTerm α) (h : D B Γ (unary atomicTest (suc z) q)) :
    D B Γ (programGraph (pairFirst atomicTest) (suc z) ![q,suc t]) := by
  apply compositionValue atomicTest (Fin.cons (.projection 0) Fin.elim0)
    (suc z) ![q,suc t] ![q] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![q,suc t]

theorem queryAtInput (q t : OTerm α) (h : D B Γ (unary atomicTest (suc z) q)) :
    D B Γ (programGraph checkAtom (suc z) ![q,suc t]) :=
  successorBranchIntro (pairFirst atomicTest) outAtom (literal 2 1) (suc z) z ![q,suc t]
    (firstAtom q t h) (literalGraph 1 ![q,suc t])

theorem queryAtOutput (q t : OTerm α) (h : D B Γ (unary atomicTest (suc z) t)) :
    D B Γ (programGraph checkAtom (suc z) ![q,suc t]) := by
  have hit : D B Γ (programGraph outAtom (suc z) ![q,suc t]) := by
    apply compositionValue atomicTest (Fin.cons outRaw Fin.elim0) (suc z) ![q,suc t] ![t] h
    intro i
    obtain rfl := Fin.eq_zero i
    exact outReport q t
  apply optionGraphCases (pairFirst atomicTest) ![q,suc t] (programGraph checkAtom (suc z) ![q,suc t])
  · intro β j Δ keep no
    simp only [programRename,pairRename,sucRelabel,zRelabel]
    simp only [pairRename,sucRelabel] at no
    have held := renameInto hit j Δ keep
    simp only [programRename,pairRename,sucRelabel,zRelabel] at held
    exact zeroBranchIntro (pairFirst atomicTest) outAtom (literal 2 1) (suc z)
      ![q.relabel j,suc (t.relabel j)] no held
  · intro β j Δ pred keep yes
    simp only [programRename,pairRename,sucRelabel,zRelabel]
    simp only [pairRename,sucRelabel] at yes
    exact successorBranchIntro (pairFirst atomicTest) outAtom (literal 2 1) (suc z) pred
      ![q.relabel j,suc (t.relabel j)] yes (literalGraph 1 _)

private theorem nonzeroEquality (q t k : OTerm α)
    (h : D B Γ (programGraph equalityTest (suc k) (Fin.cons q (Fin.cons t Fin.elim0)))) :
    D B Γ (eqn q t) := by
  obtain ⟨held⟩ := h
  obtain ⟨cmp⟩ := actualOriginalComparison B α q t
  have hc := compareView (weakenClosed cmp Γ)
  have hl : D B (ltF q t :: Γ) (eqn q t) := by
    have no := rejectForwardOrder (body := B) (Gamma := ltF q t :: Γ) q t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨bad⟩ := valueUnique equalityTest (suc k) z (Fin.cons q (Fin.cons t Fin.elim0))
      ⟨addHyp held _⟩ no
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  have hr : D B (ltF t q :: Γ) (eqn q t) := by
    have no := rejectBackwardOrder (body := B) (Gamma := ltF t q :: Γ) q t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨bad⟩ := valueUnique equalityTest (suc k) z (Fin.cons q (Fin.cons t Fin.elim0))
      ⟨addHyp held _⟩ no
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  obtain ⟨dl⟩ := hl
  obtain ⟨dr⟩ := hr
  have plain : Derivation B Γ ((eqn q t).imp (eqn q t)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have tail : Derivation B Γ ((eqn q t ⊔ ltF t q).imp (eqn q t)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp plain _) (addHyp (Derivation.implicationIntroduction dr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction dl) tail⟩

private theorem confirmedComparison (q t k : OTerm α)
    (h : D B Γ (programGraph checkSame (suc k) ![q,suc t])) : D B Γ (eqn q t) := by
  unfold checkSame at h
  rw [exact_DispatchControlAST.2.2.2.1] at h
  have actual := compositionRecover equalityTest
    (Fin.cons (.projection (0 : Fin 2)) (Fin.cons outRaw Fin.elim0))
    (suc k) ![q,suc t] (Fin.cons q (Fin.cons t Fin.elim0)) h (fun i =>
      Fin.cases (projectionValue 0 ![q,suc t]) (Fin.cases (outReport q t) (fun e => Fin.elim0 e)) i)
  exact nonzeroEquality q t k actual

/-- A successful guarded least result at an actual tested atom is an
object equality. One may test either the input or the successful
output; the positive comparator is recovered even at arbitrary open
successor values, not treated as a numeral by external calibration. -/
theorem exact_OpenLiteralAtomicGuardedLeastSingleton (L : Program 3) (ctx ty q t : OTerm α)
    (held : D B Γ (programGraph (guardedLeast L) (suc t) ![ctx,ty,q]))
    (atom : D B Γ (programGraph checkAtom (suc z) ![q,suc t])) :
    D B Γ (eqn q t) := by
  obtain ⟨row⟩ := exact_OpenAtomicLeastReport L ctx ty q t held
  have gate := successorBranchElim checkAtom (.projection 1) keepAtom (suc t) z ![q,suc t]
    atom ⟨Derivation.conjunctionRight row⟩
  apply optionGraphCases checkSame ![q,suc t] (eqn q t)
  · intro β j Δ keep no
    simp only [pairRename,sucRelabel] at no
    have retained := renameInto gate j Δ keep
    simp only [programRename,pairRename,sucRelabel] at retained
    exact rejectZeroOutput _ _ _
      (zeroBranchElim checkSame (constantZero 2) (.projection 1) _ _ no retained)
  · intro β j Δ k keep hit
    rw [eqnRelabel]
    simp only [pairRename,sucRelabel] at hit
    exact confirmedComparison (q.relabel j) (t.relabel j) k hit

#print axioms freeAtom
#print axioms bottomAtom
#print axioms exact_OpenLiteralAtomicGuardedLeastSingleton
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastShapeProof
