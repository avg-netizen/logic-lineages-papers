module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinMalformedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenConsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellCasesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserRawCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans sucNeZeroApply)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellTargets (certifiedCell)
open NumberedWindowInternalSparseFieldCellCasesProof (cellBinary)
open NumberedWindowInternalSparseFieldCellSuccessProof (cellToCons)
open NumberedWindowInternalSparseFieldCellFailureProof (openFailure)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparseDecodeSyntaxProof (unary unaryRename unaryInputsRename)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph malformed nonzero someCons)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (parserGraph)
open NumberedWindowInternalSparseFieldParserThinOpenConsProof (exact_OriginalSparseParserNil)
open NumberedWindowInternalSparseFieldParserThinMalformedProof (rejectMalformed)
open NumberedWindowInternalSparsePairGraphProof (consEquation)
open NumberedWindowInternalSparsePairOrderProof (consTailDecrease)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (Preserves keepsComp)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem openGoodCell (n : OTerm α) (goal : Formula α)
    (good : Nonempty (Derivation B Γ (unary cellGood (suc z) n)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (h t : OTerm β),
      Preserves Γ j Δ →
      Nonempty (Derivation B Δ (certifiedCell (n.relabel j) h t)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases cellHead ![n] goal
  intro β j Δ h keep head
  rw [unaryInputsRename] at head
  have yes := renameInto good j Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at yes
  apply programCases cellTail ![n.relabel j] _
  intro γ k Ξ t keep' tail
  rw [unaryInputsRename] at tail
  have yes' := renameInto yes k Ξ keep'
  rw [unaryRename,sucRelabel,zRelabel] at yes'
  have head' := renameInto head k Ξ keep'
  rw [unaryRename] at head'
  obtain ⟨one⟩ := yes'
  obtain ⟨first⟩ := head'
  obtain ⟨last⟩ := tail
  have cert : Nonempty (Derivation B Ξ (certifiedCell ((n.relabel j).relabel k) (h.relabel k) t)) :=
    ⟨Derivation.conjunctionIntroduction one (Derivation.conjunctionIntroduction first last)⟩
  have out := next γ (k ∘ j) Ξ (h.relabel k) t (keepsComp Γ Δ Ξ j k keep keep')
    (by simpa only [Term.relabel_relabel] using cert)
  simpa only [formulaRelabelComposition] using out

/-- Open the three actual sparse cases used by #621, now with the original
parser observations. Zero and malformed branches have distinct exact
parser outputs; a real cons only supplies its shape and strict decrease,
not success of its (possibly malformed) tail. -/
theorem exact_OriginalSparseParserRawCases (n : OTerm α) (goal : Formula α)
    (zeroCase :
      Nonempty (Derivation B (eqn n z :: Γ) (parserGraph (suc z) n)) →
      Nonempty (Derivation B (eqn n z :: Γ) goal))
    (gapCase : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      Preserves Γ j Δ →
      Nonempty (Derivation B Δ (malformed (n.relabel j))) →
      Nonempty (Derivation B Δ (parserGraph z (n.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j)))
    (consCase : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (h t : OTerm β),
      Preserves Γ j Δ →
      Nonempty (Derivation B Δ (certifiedCell (n.relabel j) h t)) →
      Nonempty (Derivation B Δ (consGraph (n.relabel j) h t)) →
      Nonempty (Derivation B Δ (eqn (n.relabel j) (rawCons h t))) →
      Nonempty (Derivation B Δ (ltF t (n.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply zeroSuccessorCases Γ n goal
  · let Δ := eqn n z :: Γ
    have e : Derivation B Δ (eqn n z) := Derivation.hypothesis List.mem_cons_self
    have base : Nonempty (Derivation B Δ (parserGraph (suc z) z)) := exact_OriginalSparseParserNil
    exact zeroCase (moveUnary parser (suc z) z n ⟨symm e⟩ base)
  · intro β j Δ i keep ⟨shape⟩
    let nn := n.relabel j
    let bad := unary cellGood z nn
    let good := unary cellGood (suc z) nn
    let rejectedΓ := bad :: Δ
    let acceptedΓ := good :: Δ
    have positive : Derivation B Δ (nonzero nn) := by
      rw [nonzero,equalEqn]
      apply Derivation.implicationIntroduction
      exact sucNeZeroApply
        (trans (symm (addHyp shape _)) (Derivation.hypothesis List.mem_cons_self))
    obtain ⟨flags⟩ := cellBinary (body := B) (Γ := Δ) nn
    change Derivation B Δ (bad ⊔ good) at flags
    have gapBranch : Nonempty (Derivation B rejectedΓ (goal.relabel j)) := by
      have bit : Derivation B rejectedΓ bad := Derivation.hypothesis List.mem_cons_self
      obtain ⟨iffProof⟩ := openFailure B β nn
      obtain ⟨impossibleCons⟩ := closedApply ⟨Derivation.conjunctionLeft iffProof⟩ ⟨bit⟩
      have gap : Nonempty (Derivation B rejectedΓ (malformed nn)) :=
        ⟨Derivation.conjunctionIntroduction (addHyp positive bad) impossibleCons⟩
      exact gapCase β j rejectedΓ (fun f hf => List.mem_cons_of_mem _ (keep f hf))
        gap (rejectMalformed nn gap)
    have consBranch : Nonempty (Derivation B acceptedΓ (goal.relabel j)) := by
      apply openGoodCell nn (goal.relabel j) ⟨Derivation.hypothesis List.mem_cons_self⟩
      intro γ k Ξ h t keep' cert
      have c := cellToCons (nn.relabel k) h t cert
      have e : Nonempty (Derivation B Ξ (eqn (nn.relabel k) (rawCons h t))) :=
        consEquation (nn.relabel k) h t c
      obtain ⟨order⟩ := closedApply (consTailDecrease B γ (nn.relabel k) h t) c
      have smaller : Nonempty (Derivation B Ξ (ltF t (nn.relabel k))) :=
        ⟨Derivation.conjunctionRight order⟩
      have out := consCase γ (k ∘ j) Ξ h t
        (keepsComp Γ acceptedΓ Ξ j k
          (fun f hf => List.mem_cons_of_mem _ (keep f hf)) keep')
        (by simpa only [nn,Term.relabel_relabel] using cert)
        (by simpa only [nn,Term.relabel_relabel] using c)
        (by simpa only [nn,Term.relabel_relabel] using e)
        (by simpa only [nn,Term.relabel_relabel] using smaller)
      simpa only [formulaRelabelComposition] using out
    obtain ⟨gapBranch⟩ := gapBranch
    obtain ⟨consBranch⟩ := consBranch
    exact ⟨disjunctionElimination flags
      (Derivation.implicationIntroduction gapBranch) (Derivation.implicationIntroduction consBranch)⟩

#print axioms exact_OriginalSparseParserRawCases

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserRawCasesProof
