module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalEqualityTest
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalControlGraphSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel sucRelabel zRelabel)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof InternalQuotientComparisonProof
open InternalPositiveUnfoldingSupportProof InternalSourceInversionSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem predecessorZero : Nonempty (Derivation body Gamma
    (programGraph predecessor z (Fin.cons z Fin.elim0))) :=
  recursionZeroValue .zero (.projection (0 : Fin 2)) z Fin.elim0 (zeroValue _)

theorem predecessorSuccessor (t : OrdinaryArithmetic.Term α) : Nonempty (Derivation body Gamma
    (programGraph predecessor t (Fin.cons (suc t) Fin.elim0))) := by
  apply recursionSuccessorValue .zero (.projection (0 : Fin 2)) t t Fin.elim0
  intro β j Delta v _
  exact projectionValue (0 : Fin 2) (Fin.cons (t.relabel j) (Fin.cons v
    (fun i => (Fin.elim0 i : OrdinaryArithmetic.Term α).relabel j)))

theorem predecessorForward (out input : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (programGraph predecessor out (Fin.cons input Fin.elim0)))) :
    Nonempty (Derivation body Gamma (predecessorSpec out input)) := by
  apply zeroSuccessorCases Gamma input _
  · have hv := headTransport (body := body) (Gamma := eqn input z :: Gamma) predecessor z z input Fin.elim0
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ predecessorZero
    obtain ⟨h⟩ := h
    obtain ⟨he⟩ := valueUnique predecessor out z (Fin.cons input Fin.elim0)
      ⟨addHyp h _⟩ hv
    simp only [predecessorSpec,equalEqn]
    exact ⟨orLeft (Derivation.conjunctionIntroduction
      (Derivation.hypothesis List.mem_cons_self) he)⟩
  · intro β j Delta v hj ⟨he⟩
    have hr := renameInto h j Delta hj
    simp only [programRename,consTermRename,emptyRename] at hr
    have hv := headTransport predecessor v (suc v) (input.relabel j) Fin.elim0
      ⟨symm he⟩ (predecessorSuccessor v)
    obtain ⟨hu⟩ := valueUnique predecessor (out.relabel j) v
      (Fin.cons (input.relabel j) Fin.elim0) hr hv
    change Nonempty (Derivation body Delta
      ((((equal input z ⊓ equal out z) ⊔ equal input (suc out))).relabel j))
    simp only [equalEqn]
    change Nonempty (Derivation body Delta
      (((eqn input z).relabel j ⊓ (eqn out z).relabel j) ⊔ (eqn input (suc out)).relabel j))
    simp only [eqnRelabel,zRelabel,sucRelabel]
    exact ⟨orRight (trans he (congSuc (symm hu)))⟩

theorem predecessorBackward (out input : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (predecessorSpec out input))) :
    Nonempty (Derivation body Gamma (programGraph predecessor out (Fin.cons input Fin.elim0))) := by
  obtain ⟨h⟩ := h
  simp only [predecessorSpec,equalEqn] at h
  let p := eqn input z ⊓ eqn out z
  let q := eqn input (suc out)
  have hp : Nonempty (Derivation body (p :: Gamma)
      (programGraph predecessor out (Fin.cons input Fin.elim0))) := by
    have hv := headTransport (body := body) (Gamma := p :: Gamma) predecessor z z input Fin.elim0
      ⟨symm (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))⟩ predecessorZero
    exact outputTransport predecessor z out (Fin.cons input Fin.elim0)
      ⟨symm (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩ hv
  have hq : Nonempty (Derivation body (q :: Gamma)
      (programGraph predecessor out (Fin.cons input Fin.elim0))) :=
    headTransport predecessor out (suc out) input Fin.elim0
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (predecessorSuccessor out)
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hp)
    (Derivation.implicationIntroduction hq)⟩

theorem actualOriginalPredecessorGraph : InternalEqualityTestTargets.ActualOriginalPredecessorGraph := by
  intro body α out input
  obtain ⟨hf⟩ := predecessorForward (body := body)
    (Gamma := [programGraph predecessor out (Fin.cons input Fin.elim0)]) out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := predecessorBackward (body := body) (Gamma := [predecessorSpec out input]) out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
