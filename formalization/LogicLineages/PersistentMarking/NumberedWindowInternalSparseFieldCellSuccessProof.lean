module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellProgramProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSuccessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue successorValue outputTransport valueUnique zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open NumberedWindowInternalSparsePair (fieldCons pairTerm)
open NumberedWindowInternalSparsePairGraphProof (pairGraph consEquation)
open NumberedWindowInternalSparseDecodeSyntaxProof NumberedWindowInternalSparseDecodeSuccessProof
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparseFieldCell NumberedWindowInternalSparseFieldCellTargets
open NumberedWindowInternalSparseFieldCellSyntaxProof NumberedWindowInternalSparseFieldCellProgramProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consAtSucc (k h t : OTerm α)
    (d : Nonempty (Derivation body Γ (binary NumberedWindowInternalSparsePair.pair k h t))) :
    Nonempty (Derivation body Γ (consGraph (suc k) h t)) := by
  apply compositionValue .succ (fun _ : Fin 1 => NumberedWindowInternalSparsePair.pair) (suc k)
    ![h,t] ![k] (successorValue ![k])
  intro i
  obtain rfl := Fin.eq_zero i
  exact d

theorem consToCell (n h t : OTerm α)
    (d : Nonempty (Derivation body Γ (consGraph n h t))) :
    Nonempty (Derivation body Γ (certifiedCell n h t)) := by
  obtain ⟨e⟩ := consEquation n h t d
  let k := pairTerm h t
  have exactCell : Nonempty (Derivation body Γ (certifiedCell (suc k) h t)) :=
    contractCell k h t (pairToSuccess k h t (pairGraph h t))
  exact moveCertifiedCell (suc k) n h t ⟨symm e⟩ exactCell

theorem cellToCons (n h t : OTerm α)
    (d : Nonempty (Derivation body Γ (certifiedCell n h t))) :
    Nonempty (Derivation body Γ (consGraph n h t)) := by
  obtain ⟨c⟩ := d
  apply zeroSuccessorCases Γ n _
  · let p := eqn n z
    have e : Derivation body (p :: Γ) p := Derivation.hypothesis List.mem_cons_self
    have reject := moveUnary (Γ := p :: Γ) cellGood z z n ⟨symm e⟩ nilReject
    obtain ⟨error⟩ := valueUnique cellGood (suc z) z ![n]
      ⟨addHyp (Derivation.conjunctionLeft c) p⟩ reject
    exact ⟨Derivation.explosion (sucNeZeroApply error)⟩
  · intro β j Δ k hJ ⟨e⟩
    rw [consGraphRename]
    have v := renameInto ⟨c⟩ j Δ hJ
    rw [certifiedCellRename] at v
    let hh := h.relabel j
    let tt := t.relabel j
    have got := moveCertifiedCell (n.relabel j) (suc k) hh tt ⟨e⟩ v
    have pair := successToPair k hh tt (expandCell k hh tt got)
    exact outputTransport fieldCons (suc k) (n.relabel j) ![hh,tt] ⟨symm e⟩ (consAtSucc k hh tt pair)

theorem openSuccess : OpenCellSuccess := by
  intro body α n h t
  let a := consGraph n h t
  let b := certifiedCell n h t
  obtain ⟨left⟩ := consToCell (body := body) (Γ := [a]) n h t ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨right⟩ := cellToCons (body := body) (Γ := [b]) n h t ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction left)
    (Derivation.implicationIntroduction right)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof
