module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDecodeSyntaxProof
open NumberedWindowInternalSparseFieldCell NumberedWindowInternalSparseFieldCellTargets

theorem certifiedCellRename {α β : Type} (n h t : OTerm α) (j : α → β) :
    (certifiedCell n h t).relabel j = certifiedCell (n.relabel j) (h.relabel j) (t.relabel j) := by
  change (unary cellGood (suc z) n ⊓ (unary cellHead h n ⊓ unary cellTail t n)).relabel j =
    (unary cellGood (suc z) (n.relabel j) ⊓
      (unary cellHead (h.relabel j) (n.relabel j) ⊓ unary cellTail (t.relabel j) (n.relabel j)))
  simp only [conjunctionRename,unaryRename,zRelabel,sucRelabel]

theorem moveUnary {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Program 1) (out n m : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn n m)))
    (h : Nonempty (Derivation body Γ (unary p out n))) :
    Nonempty (Derivation body Γ (unary p out m)) :=
  headTransport p out n m Fin.elim0 eq h

theorem moveCertifiedCell {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (n m h t : OTerm α) (e : Nonempty (Derivation body Γ (eqn n m)))
    (c : Nonempty (Derivation body Γ (certifiedCell n h t))) :
    Nonempty (Derivation body Γ (certifiedCell m h t)) := by
  obtain ⟨c⟩ := c
  obtain ⟨a⟩ := moveUnary cellGood (suc z) n m e ⟨Derivation.conjunctionLeft c⟩
  obtain ⟨b⟩ := moveUnary cellHead h n m e ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight c)⟩
  obtain ⟨d⟩ := moveUnary cellTail t n m e ⟨Derivation.conjunctionRight (Derivation.conjunctionRight c)⟩
  exact ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b d)⟩

abbrev cellCases {α : Type} (n : OTerm α) : Formula α :=
  unary cellGood z n ⊔ unary cellGood (suc z) n

theorem cellCasesRename {α β : Type} (n : OTerm α) (j : α → β) :
    (cellCases n).relabel j = cellCases (n.relabel j) := by
  have relabelOr {p q : Formula α} : (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl
  simp only [cellCases,relabelOr,unaryRename,zRelabel,sucRelabel]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
