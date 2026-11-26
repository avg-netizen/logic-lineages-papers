module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (consForward stepCases consValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue valueUnique outputTransport)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (oneRename graph3Rename)
open NumberedWindowInternalSparseScratchMembership
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof
  (missGraph missRename missNotRename splitRename)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A zero head test selects the literal tail-bit branch of the actual
step. The successful step output therefore is the genuine tail bit. -/
private theorem missTail (h tail k previous : OTerm α)
    (miss : Nonempty (Derivation body Γ (missGraph h k)))
    (tailRun : Nonempty (Derivation body Γ (programGraph scratchMember previous ![tail,k])))
    (rowRun : Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,previous,k]))) :
    Nonempty (Derivation body Γ (memberGraph tail k)) := by
  let xs : Fin 3 → OTerm α := ![h,previous,k]
  have rejected : Nonempty (Derivation body Γ (programGraph headMatches z xs)) := by
    apply compositionValue equalityTest (![.projection 0,.projection 2] : Fin 2 → Program 3)
      z xs ![h,k] miss
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs) (fun noIndex => Fin.elim0 noIndex)) i
  have kept := zeroBranchElim headMatches (.projection 1) (constantOne 3) (suc z) xs
    rejected rowRun
  obtain ⟨same⟩ := valueUnique (.projection (1 : Fin 3)) (suc z) previous xs kept
    (projectionValue 1 xs)
  exact outputTransport scratchMember previous (suc z) (![tail,k] : Fin 2 → OTerm α)
    ⟨symm same⟩ tailRun

/-- Classical split on the actual head test at one genuine tail bit. -/
private theorem rowSplit (h tail k previous : OTerm α)
    (tailRun : Nonempty (Derivation body Γ (programGraph scratchMember previous ![tail,k])))
    (rowRun : Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,previous,k]))) :
    Nonempty (Derivation body Γ ((missGraph h k).not ⊔ memberGraph tail k)) := by
  let M := missGraph h k
  obtain ⟨tailRun⟩ := tailRun
  obtain ⟨rowRun⟩ := rowRun
  obtain ⟨inTail⟩ := missTail (body := body) (Γ := M :: Γ) h tail k previous
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp tailRun M⟩ ⟨addHyp rowRun M⟩
  have yes : Derivation body Γ (M.imp (M.not ⊔ memberGraph tail k)) :=
    Derivation.implicationIntroduction (orRight inTail)
  have no : Derivation body Γ (M.not.imp (M.not ⊔ memberGraph tail k)) :=
    Derivation.implicationIntroduction (orLeft (Derivation.hypothesis List.mem_cons_self))
  exact ⟨disjunctionElimination (excludedMiddle M) yes no⟩

/-- Inversion of successful membership at an actual cons: the real head
test is not zero, or the same candidate occurs in the real tail. -/
theorem consInversion (code h tail k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (member : Nonempty (Derivation body Γ (memberGraph code k))) :
    Nonempty (Derivation body Γ ((missGraph h k).not ⊔ memberGraph tail k)) := by
  have step := consForward memberBase memberStep code h tail (suc z)
    (![k] : Fin 1 → OTerm α) input member
  apply stepCases memberBase memberStep (suc z) h tail (![k] : Fin 1 → OTerm α)
    ((missGraph h k).not ⊔ memberGraph tail k) step
  intro β j Δ previous _ tailRun rowRun
  rw [oneRename] at tailRun rowRun
  rw [sucRelabel,zRelabel] at rowRun
  rw [splitRename]
  exact rowSplit (h.relabel j) (tail.relabel j) (k.relabel j) previous tailRun rowRun

/-- A head test that is not zero makes the actual step return one for
every tail bit; the head comparison never reads that slot. -/
private theorem stepHead (h previous k : OTerm α)
    (hit : Nonempty (Derivation body Γ (missGraph h k).not)) :
    Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,previous,k])) := by
  apply optionGraphCases headMatches (![h,previous,k] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    simp only [tripleInputsRename] at zero
    simp only [graph3Rename,sucRelabel,zRelabel]
    let xs : Fin 3 → OTerm β := ![h.relabel j,previous.relabel j,k.relabel j]
    have miss : Nonempty (Derivation body Δ (missGraph (h.relabel j) (k.relabel j))) := by
      apply compositionRecover equalityTest
        (![.projection 0,.projection 2] : Fin 2 → Program 3)
        z xs (![h.relabel j,k.relabel j] : Fin 2 → OTerm β) zero
      intro i
      exact Fin.cases (projectionValue 0 xs)
        (Fin.cases (projectionValue 2 xs) (fun noIndex => Fin.elim0 noIndex)) i
    have no := renameInto hit j Δ keep
    rw [missNotRename] at no
    obtain ⟨miss⟩ := miss
    obtain ⟨no⟩ := no
    exact ⟨Derivation.explosion (Derivation.implicationElimination no miss)⟩
  · intro β j Δ prior _ nonzero
    simp only [tripleInputsRename] at nonzero
    simp only [graph3Rename,sucRelabel,zRelabel]
    let xs : Fin 3 → OTerm β := ![h.relabel j,previous.relabel j,k.relabel j]
    exact successorBranchIntro headMatches (.projection 1) (constantOne 3) (suc z) prior xs
      nonzero (oneConstantValue xs)

/-- The same head on any actual cons, with its own genuine recursive
tail value obtained by original Program totality. -/
theorem headHit (code h tail k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (hit : Nonempty (Derivation body Γ (missGraph h k).not)) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  apply programCases scratchMember ![tail,k] (memberGraph code k)
  intro β j Δ previous keep observed
  rw [graphRename]
  rw [binaryInputsRename] at observed
  have hasCell := renameInto input j Δ keep
  rw [consGraphRename] at hasCell
  have no := renameInto hit j Δ keep
  rw [missNotRename] at no
  let h' := h.relabel j
  let t' := tail.relabel j
  let k' := k.relabel j
  exact consValue memberBase memberStep (code.relabel j) h' t' previous (suc z) ![k']
    hasCell observed (stepHead h' previous k' no)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
