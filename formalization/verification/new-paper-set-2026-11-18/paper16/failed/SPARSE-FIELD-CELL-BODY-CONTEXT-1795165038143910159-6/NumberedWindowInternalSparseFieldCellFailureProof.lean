module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellExistentialProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellCasesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellFailureProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open NumberedWindowInternalSparseFieldInductionTargets (someCons)
open NumberedWindowInternalSparseFieldExistentialProof (someConsCases someConsRename)
open NumberedWindowInternalSparseFieldCellExistentialProof (someConsIntro)
open NumberedWindowInternalSparseDecodeSyntaxProof
open NumberedWindowInternalSparseFieldCell NumberedWindowInternalSparseFieldCellTargets
open NumberedWindowInternalSparseFieldCellSuccessProof NumberedWindowInternalSparseFieldCellCasesProof
open NumberedWindowInternalSparseFieldCellProgramProof (nilReject)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem noConsOfReject (n : OTerm α)
    (r : Nonempty (Derivation body Γ (unary cellGood z n))) :
    Nonempty (Derivation body Γ (someCons n).not) := by
  obtain ⟨r⟩ := r
  let a := someCons n
  have bad : Nonempty (Derivation body (a :: Γ) (⊥ : Formula α)) := by
    apply someConsCases n ⊥ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Δ h t hJ hc
    have reject := renameInto ⟨addHyp r a⟩ j Δ hJ
    rw [unaryRename,zRelabel] at reject
    obtain ⟨good⟩ := consToCell (n.relabel j) h t hc
    obtain ⟨e⟩ := valueUnique cellGood (suc z) z ![n.relabel j]
      ⟨Derivation.conjunctionLeft good⟩ reject
    exact ⟨sucNeZeroApply e⟩
  obtain ⟨bad⟩ := bad
  exact ⟨Derivation.implicationIntroduction bad⟩

private theorem someConsOfGood (n : OTerm α)
    (hg : Nonempty (Derivation body Γ (unary cellGood (suc z) n))) :
    Nonempty (Derivation body Γ (someCons n)) := by
  apply programCases cellHead ![n] (someCons n)
  intro β j Δ h hJ hh
  rw [someConsRename]
  rw [unaryInputsRename] at hh
  let nn := n.relabel j
  have good' := renameInto hg j Δ hJ
  rw [unaryRename,sucRelabel,zRelabel] at good'
  apply programCases cellTail ![nn] (someCons nn)
  intro γ k Θ t hK ht
  rw [someConsRename]
  rw [unaryInputsRename] at ht
  have head' := renameInto hh k Θ hK
  rw [unaryRename] at head'
  have ok := renameInto good' k Θ hK
  rw [unaryRename,sucRelabel,zRelabel] at ok
  let ng := nn.relabel k
  let hd := h.relabel k
  obtain ⟨head'⟩ := head'
  obtain ⟨tail'⟩ := ht
  obtain ⟨ok⟩ := ok
  have cert : Nonempty (Derivation body Θ (certifiedCell ng hd t)) :=
    ⟨Derivation.conjunctionIntroduction ok (Derivation.conjunctionIntroduction head' tail')⟩
  exact someConsIntro ng hd t (cellToCons ng hd t cert)

private theorem rejectOfNoCons (n : OTerm α)
    (p : Nonempty (Derivation body Γ (someCons n).not)) :
    Nonempty (Derivation body Γ (unary cellGood z n)) := by
  obtain ⟨p⟩ := p
  obtain ⟨states⟩ := cellBinary (body := body) (Γ := Γ) n
  let yes := unary cellGood (suc z) n
  obtain ⟨witness⟩ := someConsOfGood (body := body) (Γ := yes :: Γ) n
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have bad := Derivation.implicationElimination (addHyp p yes) witness
  exact ⟨disjunctionElimination states
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Derivation.explosion bad))⟩

theorem openFailure : OpenCellFailure := by
  intro body α n
  let a := unary cellGood z n
  let b := (someCons n).not
  obtain ⟨left⟩ := noConsOfReject (body := body) (Γ := [a]) n ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨right⟩ := rejectOfNoCons (body := body) (Γ := [b]) n ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction left)
    (Derivation.implicationIntroduction right)⟩

theorem openNil : OpenNilCell := by
  intro body α
  obtain ⟨r⟩ := nilReject (body := body) (α := α) (Γ := [])
  obtain ⟨missing⟩ := noConsOfReject (z : OTerm α) ⟨r⟩
  exact ⟨Derivation.conjunctionIntroduction r missing⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellFailureProof
