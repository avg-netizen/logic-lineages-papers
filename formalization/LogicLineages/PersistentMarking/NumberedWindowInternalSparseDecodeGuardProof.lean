module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeGuardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalLessThan (ltTest constantOne)
open ID1Completion.InternalLessThanSupportProof
open ID1Completion.InternalSquareRoot (root)
open NumberedWindowInternalSparseDecode NumberedWindowInternalSparseDecodeSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem gapGraph (n s x out : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (hx : Nonempty (Derivation body Γ (unary leftCandidate x n)))
    (hc : Nonempty (Derivation body Γ (lessGraph out s x))) :
    Nonempty (Derivation body Γ (unary gap out n)) := by
  apply compositionValue ltTest ![root,leftCandidate] out ![n] ![s,x] hc
  intro i
  exact Fin.cases hs (Fin.cases hx (fun k => Fin.elim0 k)) i

theorem goodYes (n s x : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (hx : Nonempty (Derivation body Γ (unary leftCandidate x n)))
    (hb : Nonempty (Derivation body Γ (ltF s x).not)) :
    Nonempty (Derivation body Γ (unary good (suc z) n)) :=
  zeroBranchIntro gap (constantOne 1) (constantZero 1) (suc z) ![n]
    (gapGraph n s x z hs hx (rejectOfNotLess s x hb)) (oneConstantValue ![n])

theorem goodNo (n s x : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (hx : Nonempty (Derivation body Γ (unary leftCandidate x n)))
    (hb : Nonempty (Derivation body Γ (ltF s x))) :
    Nonempty (Derivation body Γ (unary good z n)) :=
  successorBranchIntro gap (constantOne 1) (constantZero 1) z z ![n]
    (gapGraph n s x (suc z) hs hx (acceptOfLess s x hb)) (zeroConstantValue ![n])

theorem noGapOfGood (n s x : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (hx : Nonempty (Derivation body Γ (unary leftCandidate x n)))
    (hg : Nonempty (Derivation body Γ (unary good (suc z) n))) :
    Nonempty (Derivation body Γ (ltF s x).not) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨hx⟩ := hx
  obtain ⟨hg⟩ := hg
  let p := ltF s x
  have bad := goodNo (Γ := p :: Γ) n s x ⟨addHyp hs p⟩ ⟨addHyp hx p⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨eq⟩ := valueUnique good (suc z) z ![n] ⟨addHyp hg p⟩ bad
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply eq)⟩

abbrev guardCases {α : Type} (n : OTerm α) : Formula α := unary good z n ⊔ unary good (suc z) n

theorem guardCasesRename {α β : Type} (n : OTerm α) (j : α → β) :
    (guardCases n).relabel j = guardCases (n.relabel j) := by
  have relabelOr {p q : Formula α} : (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl
  simp only [guardCases,relabelOr,unaryRename,sucRelabel,zRelabel]

private theorem guardCasesAt (n s x : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (hx : Nonempty (Derivation body Γ (unary leftCandidate x n))) :
    Nonempty (Derivation body Γ (guardCases n)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨hx⟩ := hx
  let p := ltF s x
  obtain ⟨no⟩ := goodNo (Γ := p :: Γ) n s x ⟨addHyp hs p⟩ ⟨addHyp hx p⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨yes⟩ := goodYes (Γ := p.not :: Γ) n s x ⟨addHyp hs p.not⟩ ⟨addHyp hx p.not⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction (orLeft no))
    (Derivation.implicationIntroduction (orRight yes))⟩

theorem guardBinary (n : OTerm α) : Nonempty (Derivation body Γ (guardCases n)) := by
  apply programCases root ![n] (guardCases n)
  intro β j Δ s _ hs
  rw [guardCasesRename]
  rw [unaryInputsRename] at hs
  apply programCases leftCandidate ![n.relabel j] (guardCases (n.relabel j))
  intro γ k Θ x hk hx
  rw [guardCasesRename]
  rw [unaryInputsRename] at hx
  have rootFound := renameInto hs k Θ hk
  rw [unaryRename] at rootFound
  exact guardCasesAt ((n.relabel j).relabel k) (s.relabel k) x rootFound hx

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeGuardProof
