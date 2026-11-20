module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellProgramProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeGuardProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open NumberedWindowInternalSparseDecode (good)
open NumberedWindowInternalSparseDecodeSyntaxProof
open NumberedWindowInternalSparseDecodeGuardProof (guardBinary)
open NumberedWindowInternalSparseFieldCell (cellGood)
open NumberedWindowInternalSparseFieldCellSyntaxProof NumberedWindowInternalSparseFieldCellProgramProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem cellBinary (n : OTerm α) : Nonempty (Derivation body Γ (cellCases n)) := by
  apply zeroSuccessorCases Γ n _
  · let p := eqn n z
    have e : Derivation body (p :: Γ) p := Derivation.hypothesis List.mem_cons_self
    obtain ⟨reject⟩ := moveUnary (Γ := p :: Γ) cellGood z z n ⟨symm e⟩ nilReject
    exact ⟨orLeft reject⟩
  · intro β j Δ k _ ⟨e⟩
    rw [cellCasesRename]
    let nn := n.relabel j
    let a := unary good z k
    let b := unary good (suc z) k
    obtain ⟨states⟩ := guardBinary (body := body) (Γ := Δ) k
    have no := setFlag (body := body) (Γ := a :: Δ) k z ⟨Derivation.hypothesis List.mem_cons_self⟩
    have yes := setFlag (body := body) (Γ := b :: Δ) k (suc z) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨no⟩ := moveUnary cellGood z (suc k) nn ⟨symm (addHyp e a)⟩ no
    obtain ⟨yes⟩ := moveUnary cellGood (suc z) (suc k) nn ⟨symm (addHyp e b)⟩ yes
    exact ⟨disjunctionElimination states
      (Derivation.implicationIntroduction (orLeft no))
      (Derivation.implicationIntroduction (orRight yes))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellCasesProof
