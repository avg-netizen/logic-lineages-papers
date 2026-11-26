module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue valueUnique outputTransport compositionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (sameHeader allowedOutput headerLeast inputHead outputHead)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (outRaw)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D rejectZeroOutput outReport)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem keepOriginal (q code t : OTerm α)
    (h : D B Γ (programGraph allowedOutput (suc t) ![q,code])) :
    D B Γ (eqn code (suc t)) := by
  apply optionGraphCases sameHeader ![q,code] (eqn code (suc t))
  · intro β j Δ keep no
    rw [pairRename] at no
    have held := renameInto h j Δ keep
    simp only [programRename,pairRename,sucRelabel] at held
    exact rejectZeroOutput _ _ _
      (zeroBranchElim sameHeader (constantZero 2) (.projection 1) _ _ no held)
  · intro β j Δ k keep yes
    rw [eqnRelabel,sucRelabel]
    rw [pairRename] at yes
    let xs : Fin 2 → OTerm β := ![q.relabel j,code.relabel j]
    have held := renameInto h j Δ keep
    simp only [programRename,pairRename,sucRelabel] at held
    have read := successorBranchElim sameHeader (constantZero 2) (.projection 1) (suc (t.relabel j))
      k xs yes held
    exact valueUnique (.projection 1) (code.relabel j) (suc (t.relabel j)) xs
      (projectionValue 1 xs) read

/-- Remove the exact physical top-header guard without changing the
selected least result. The added check also remains available on
the real input and the same successful encoded output. -/
theorem exact_OpenLiteralHeaderLeastReport (L : Program 3) (ctx ty q t : OTerm α)
    (h : D B Γ (programGraph (headerLeast L) (suc t) ![ctx,ty,q])) :
    D B Γ (programGraph L (suc t) ![ctx,ty,q] ⊓ programGraph allowedOutput (suc t) ![q,suc t]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let select : Fin 2 → Program 3 := Fin.cons (.projection 2) (Fin.cons L Fin.elim0)
  have least : D B Γ (programGraph L (suc t) xs) := by
    apply programCases L xs (programGraph L (suc t) xs)
    intro β j Δ code keep chosen
    simp only [xs,programRename,tripleInputsRename,sucRelabel]
    simp only [xs,tripleInputsRename] at chosen
    let x' : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,q.relabel j]
    have edge := renameInto h j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at edge
    have gate : D B Δ (programGraph allowedOutput (suc (t.relabel j)) ![q.relabel j,code]) := by
      apply compositionRecover allowedOutput select (suc (t.relabel j)) x' ![q.relabel j,code] edge
      intro k
      exact Fin.cases (projectionValue 2 x') (Fin.cases chosen (fun e => Fin.elim0 e)) k
    exact outputTransport L code (suc (t.relabel j)) x'
      (keepOriginal (q.relabel j) code (t.relabel j) gate) chosen
  have actual : D B Γ (programGraph allowedOutput (suc t) ![q,suc t]) := by
    apply compositionRecover allowedOutput select (suc t) xs ![q,suc t] h
    intro k
    exact Fin.cases (projectionValue 2 xs) (Fin.cases least (fun e => Fin.elim0 e)) k
  obtain ⟨l⟩ := least
  obtain ⟨g⟩ := actual
  exact ⟨Derivation.conjunctionIntroduction l g⟩

private theorem nonzeroCompare (a b k : OTerm α)
    (held : D B Γ (programGraph equalityTest (suc k) (Fin.cons a (Fin.cons b Fin.elim0)))) :
    D B Γ (eqn a b) := by
  obtain ⟨got⟩ := held
  obtain ⟨base⟩ := actualOriginalComparison B α a b
  have oriented := compareView (weakenClosed base Γ)
  have left : D B (ltF a b :: Γ) (eqn a b) := by
    have no := rejectForwardOrder (body := B) (Gamma := ltF a b :: Γ) a b
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨bad⟩ := valueUnique equalityTest (suc k) z (Fin.cons a (Fin.cons b Fin.elim0))
      ⟨addHyp got _⟩ no
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  have right : D B (ltF b a :: Γ) (eqn a b) := by
    have no := rejectBackwardOrder (body := B) (Gamma := ltF b a :: Γ) a b
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨bad⟩ := valueUnique equalityTest (suc k) z (Fin.cons a (Fin.cons b Fin.elim0))
      ⟨addHyp got _⟩ no
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  have equal : Derivation B Γ ((eqn a b).imp (eqn a b)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have rest : Derivation B Γ ((eqn a b ⊔ ltF b a).imp (eqn a b)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp equal _) (addHyp (Derivation.implicationIntroduction right) _))
  exact ⟨disjunctionElimination oriented (Derivation.implicationIntroduction left) rest⟩

private theorem comparedHeaders (q t a b k : OTerm α)
    (hs : D B Γ (programGraph cellHead a ![q])) (ht : D B Γ (programGraph cellHead b ![t]))
    (held : D B Γ (programGraph sameHeader (suc k) ![q,suc t])) :
    D B Γ (eqn a b) := by
  let xs : Fin 2 → OTerm α := ![q,suc t]
  have fromSource : D B Γ (programGraph inputHead a xs) := by
    apply compositionValue cellHead (Fin.cons (.projection 0) Fin.elim0) a xs ![q] hs
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have fromResult : D B Γ (programGraph outputHead b xs) := by
    apply compositionValue cellHead (Fin.cons outRaw Fin.elim0) b xs ![t] ht
    intro i
    obtain rfl := Fin.eq_zero i
    exact outReport q t
  unfold sameHeader at held
  rw [exact_DispatchControlAST.2.2.2.1] at held
  have hit := compositionRecover equalityTest (Fin.cons inputHead (Fin.cons outputHead Fin.elim0))
    (suc k) xs (Fin.cons a (Fin.cons b Fin.elim0)) held
    (fun i => Fin.cases fromSource (Fin.cases fromResult (fun e => Fin.elim0 e)) i)
  exact nonzeroCompare a b k hit

/-- In the open object calculus, the actual guarded least selector
preserves a reported top header graph from the raw input to the actual
successful output. The exact comparison is recovered through the
physical branch, even though its branch witness need not be a numeral. -/
theorem exact_OpenLiteralHeaderLeastKeeps (L : Program 3) (ctx ty q t a : OTerm α)
    (h : D B Γ (programGraph (headerLeast L) (suc t) ![ctx,ty,q]))
    (known : D B Γ (programGraph cellHead a ![q])) :
    D B Γ (programGraph cellHead a ![t]) := by
  obtain ⟨both⟩ := exact_OpenLiteralHeaderLeastReport L ctx ty q t h
  have gate : D B Γ (programGraph allowedOutput (suc t) ![q,suc t]) :=
    ⟨Derivation.conjunctionRight both⟩
  apply programCases cellHead ![t] (programGraph cellHead a ![t])
  intro β j Δ b keep result
  rw [programRename,inputsRename]
  rw [inputsRename] at result
  let q' := q.relabel j
  let t' := t.relabel j
  let a' := a.relabel j
  let xs : Fin 2 → OTerm β := ![q',suc t']
  have source := renameInto known j Δ keep
  simp only [programRename,inputsRename] at source
  have held := renameInto gate j Δ keep
  simp only [programRename,pairRename,sucRelabel] at held
  apply optionGraphCases sameHeader xs (programGraph cellHead a' ![t'])
  · intro γ l Ω stay no
    simp only [xs,pairRename,sucRelabel] at no
    have atGate := renameInto held l Ω stay
    simp only [programRename,pairRename,sucRelabel] at atGate
    exact rejectZeroOutput _ _ _
      (zeroBranchElim sameHeader (constantZero 2) (.projection 1) _ _ no atGate)
  · intro γ l Ω k stay yes
    rw [programRename,inputsRename]
    simp only [xs,pairRename,sucRelabel] at yes
    have in' := renameInto source l Ω stay
    have out' := renameInto result l Ω stay
    simp only [programRename,inputsRename] at in' out'
    obtain ⟨same⟩ := comparedHeaders (q'.relabel l) (t'.relabel l) (a'.relabel l) (b.relabel l) k
      in' out' yes
    exact outputTransport cellHead (b.relabel l) (a'.relabel l) ![t'.relabel l] ⟨symm same⟩ out'

#print axioms exact_OpenLiteralHeaderLeastKeeps
#print axioms exact_OpenLiteralHeaderLeastReport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
