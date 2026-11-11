module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDropProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open OriginalVariableDecoder OriginalVariableDecoderGraphSupportProof
open OriginalVariableDecoderEqualityProof OriginalVariableDecoderDropProof
open InternalRawListRecursionSyntaxProof InternalRawListRecursionSupportProof
open InternalControlGraphSupportProof InternalControlGraphProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalPositiveUnfoldingSupportProof
open InternalEqualityTestCompositionProof InternalBetaTotalityProof
open InternalRecursionGraphStepSyntaxProof InternalOriginalOrderProof InternalRecursionClosureLogicProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem nilValue (typ index : OTerm alpha) :
    Nonempty (Derivation body Gamma (graph z typ index z)) :=
  zeroBranchIntro rest (InternalAcceptance.constantZero 3) matchesType z
    (inputs typ index z) (restValue typ index z z (dropNil index)) (zeroValueAt _)

theorem actualOriginalVariableDecoderNil :
    OriginalVariableDecoderTargets.ActualOriginalVariableDecoderNil := by
  intro body alpha out typ index
  let g := graph out typ index z
  obtain ⟨hf⟩ := valueUnique check out z (inputs typ index z)
    (show Nonempty (Derivation body [g] g) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (nilValue typ index)
  obtain ⟨hb⟩ := outputTransport check z out (inputs typ index z)
    (show Nonempty (Derivation body [eqn out z] (eqn z out)) from
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩) (nilValue typ index)
  simpa only [Formula.iff,BoundedFormula.iff,equalEqn,g,graph,inputs] using
    (Nonempty.intro (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)))

theorem consZeroValue (out typ code head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (he : Nonempty (Derivation body Gamma (equalityGraph out typ head))) :
    Nonempty (Derivation body Gamma (graph out typ z code)) := by
  obtain ⟨hcons⟩ := consDestruction code head tail hc
  have hn : Nonempty (Derivation body Gamma (eqn code z).not) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hcons)⟩
  exact checkValue out typ z code code head out (dropZero code)
    (consHead code head tail hc) he (conditionalAtNonzero code z out hn)

theorem consZeroElim (out typ code head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hw : Nonempty (Derivation body Gamma (graph out typ z code))) :
    Nonempty (Derivation body Gamma (equalityGraph out typ head)) := by
  apply programCases InternalEqualityTest.equalityTest (Fin.cons typ (Fin.cons head Fin.elim0)) _
  intro beta j Delta value hj he
  rw [equalityGraphRename]
  have hc' := renameInto hc j Delta hj
  have hw' := renameInto hw j Delta hj
  simp only [consGraphRename,graphRename,zRelabel] at hc' hw'
  simp only [consTermRename,emptyRename] at he
  have hs := consZeroValue value (typ.relabel j) (code.relabel j) (head.relabel j)
    (tail.relabel j) hc' he
  obtain ⟨hq⟩ := valueUnique check (out.relabel j) value
    (inputs (typ.relabel j) z (code.relabel j)) hw' hs
  exact outputTransport InternalEqualityTest.equalityTest value (out.relabel j)
    (Fin.cons (typ.relabel j) (Fin.cons (head.relabel j) Fin.elim0)) ⟨symm hq⟩ he

theorem actualOriginalVariableDecoderConsZero :
    OriginalVariableDecoderTargets.ActualOriginalVariableDecoderConsZero := by
  intro body alpha out typ code head tail
  let c := consGraph code head tail
  let g := graph out typ z code
  let s := testSpec out typ head
  obtain ⟨he⟩ := equalityEquation (body := body) out typ head
  have hf : Nonempty (Derivation body [g,c] s) :=
    closedApply ⟨Derivation.conjunctionLeft he⟩
      (consZeroElim out typ code head tail
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hb : Nonempty (Derivation body [s,c] g) :=
    consZeroValue out typ code head tail
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      (closedApply ⟨Derivation.conjunctionRight he⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem consSuccessorForward (out typ index code head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hw : Nonempty (Derivation body Gamma (graph out typ (suc index) code))) :
    Nonempty (Derivation body Gamma (graph out typ index tail)) := by
  apply programCases InternalRawListRecursion.drop (Fin.cons index (Fin.cons tail Fin.elim0)) _
  intro beta j Delta residual hj hd
  rw [graphRename]
  have hc' := renameInto hc j Delta hj
  have hw' := renameInto hw j Delta hj
  simp only [consGraphRename,graphRename,sucRelabel] at hc' hw'
  simp only [consTermRename,emptyRename] at hd
  exact checkTransfer _ _ _ _ _ _ residual
    (dropConsForward residual (index.relabel j) (code.relabel j)
      (head.relabel j) (tail.relabel j) hc' hd) hd hw'

theorem consSuccessorBackward (out typ index code head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hw : Nonempty (Derivation body Gamma (graph out typ index tail))) :
    Nonempty (Derivation body Gamma (graph out typ (suc index) code)) := by
  apply programCases InternalRawListRecursion.drop (Fin.cons index (Fin.cons tail Fin.elim0)) _
  intro beta j Delta residual hj hd
  simp only [graphRename,sucRelabel]
  have hc' := renameInto hc j Delta hj
  have hw' := renameInto hw j Delta hj
  simp only [consGraphRename,graphRename] at hc' hw'
  simp only [consTermRename,emptyRename] at hd
  exact checkTransfer _ _ _ _ _ _ residual hd
    (dropConsForward residual (index.relabel j) (code.relabel j)
      (head.relabel j) (tail.relabel j) hc' hd) hw'

theorem actualOriginalVariableDecoderConsSuccessor :
    OriginalVariableDecoderTargets.ActualOriginalVariableDecoderConsSuccessor := by
  intro body alpha out typ index code head tail
  let c := consGraph code head tail
  let g := graph out typ (suc index) code
  let s := graph out typ index tail
  obtain ⟨hf⟩ := consSuccessorForward (body := body) (Gamma := [g,c]) out typ index code head tail
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := consSuccessorBackward (body := body) (Gamma := [s,c]) out typ index code head tail
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderInternalProof
