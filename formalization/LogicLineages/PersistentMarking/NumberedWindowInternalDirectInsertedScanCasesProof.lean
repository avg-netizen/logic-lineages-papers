module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanCasesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanCases
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue zeroSuccessorCases programRename outputTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalDirectInsertedRowTargets (parseRemoved poolReady oneTerm)
open NumberedWindowInternalDirectInsertedScanTargets (scan scanAt loopAccept rowAccept)
open NumberedWindowInternalDirectInsertedScanCasesTargets
open NumberedWindowInternalDirectInsertedScan (exactOpenScanParser)
open NumberedWindowInternalDirectInsertedScanMember (exactOpenScanMember)
open NumberedWindowInternalDirectInsertedScanMemberTargets (fromMember)
open NumberedWindowInternalDirectInsertedRowCases (exactOpenInsertedRowCases)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem binaryRename {β : Type} (a b : OrdinaryArithmetic.Term α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OrdinaryArithmetic.Term α) i).relabel j) =
      ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem keepThrough {β γ : Type} {Δ : List (Formula β)} {Ω : List (Formula γ)}
    (j : α → β) (k : β → γ)
    (h : ∀ p ∈ Γ, p.relabel j ∈ Δ) (g : ∀ p ∈ Δ, p.relabel k ∈ Ω) :
    ∀ p ∈ Γ, p.relabel (k ∘ j) ∈ Ω := by
  intro p hp
  rw [← formulaRelabelComposition j k p]
  exact g _ (h p hp)

private theorem rejectZero (inserted removed : OrdinaryArithmetic.Term α)
    (parsed : Nonempty (Derivation B Γ (unary parser z inserted)))
    (ready : Nonempty (Derivation B Γ (programGraph poolReady oneTerm ![inserted,removed]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![inserted,removed]
  have h : Nonempty (Derivation B Γ (programGraph parseRemoved z xs)) := by
    apply compositionValue parser ![.projection 0] z xs ![inserted] parsed
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have zero := zeroBranchElim parseRemoved (constantZero 2) (literal 2 1)
    oneTerm xs h ready
  obtain ⟨bad⟩ := valueUnique (constantZero 2) oneTerm z xs zero (constantZeroValue xs)
  exact ⟨sucNeZeroApply bad⟩

theorem exactOpenScanCases : ExactOpenScanCases := by
  intro r B α Γ inserted removed goal hit next
  apply programCases parser ![inserted] goal
  intro β j Δ out keep report
  rw [inputsRename] at report
  let A := inserted.relabel j
  let R := removed.relabel j
  have saved : Nonempty (Derivation B Δ (programGraph (scan r) oneTerm ![A,R])) := by
    simpa only [A,R,programRename,binaryRename,oneTerm,sucRelabel,zRelabel] using
      renameInto hit j Δ keep
  apply zeroSuccessorCases Δ out (goal.relabel j)
  · let E := eqn out z
    obtain ⟨parts⟩ := conjunctionRecover poolReady (scanAt r) ![A,R] saved
    obtain ⟨present⟩ := report
    have e : Nonempty (Derivation B (E :: Δ) E) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := outputTransport parser out z ![A] e ⟨addHyp present E⟩
    obtain ⟨bad⟩ := rejectZero A R zero ⟨addHyp (Derivation.conjunctionLeft parts) E⟩
    exact ⟨Derivation.explosion bad⟩
  · intro γ k Ω decoded retain e
    have held := renameInto report k Ω retain
    simp only [programRename,inputsRename,Term.relabel_relabel] at held
    have success := outputTransport parser (out.relabel k) (suc decoded)
      ![inserted.relabel (k ∘ j)] e held
    have saved' : Nonempty (Derivation B Ω (programGraph (scan r) oneTerm
        ![inserted.relabel (k ∘ j),removed.relabel (k ∘ j)])) := by
      simpa only [A,R,programRename,binaryRename,oneTerm,sucRelabel,zRelabel,
        Term.relabel_relabel] using renameInto saved k Ω retain
    have loop := exactOpenScanParser r B γ Ω (inserted.relabel (k ∘ j))
      (removed.relabel (k ∘ j)) decoded success saved'
    rw [formulaRelabelComposition]
    exact next γ (k ∘ j) Ω decoded (keepThrough j k keep retain) success loop

private theorem applyMember (r : Program 3) (decoded removed row : OrdinaryArithmetic.Term α)
    (loop : Nonempty (Derivation B Γ (loopAccept r decoded removed)))
    (member : Nonempty (Derivation B Γ (memberGraph decoded row))) :
    Nonempty (Derivation B Γ (rowAccept r row removed)) := by
  obtain ⟨worker⟩ := exactOpenScanMember r B α Γ decoded removed row
  obtain ⟨h⟩ := loop
  obtain ⟨m⟩ := member
  exact ⟨Derivation.implicationElimination worker (Derivation.conjunctionIntroduction h m)⟩

theorem exactOpenScanMemberCases : ExactOpenScanMemberCases := by
  intro r B α Γ inserted removed row goal hit findMember next
  apply exactOpenScanCases r B α Γ inserted removed goal hit
  intro β j Δ decoded keep parsed loop
  have member := findMember β j Δ decoded keep parsed
  have checked := applyMember r decoded (removed.relabel j) (row.relabel j) loop member
  apply exactOpenInsertedRowCases r B β Δ (removed.relabel j) (row.relabel j) (goal.relabel j) checked
  intro γ k Ω removedCode target dom cert retain reports
  have parsed' : Nonempty (Derivation B Ω
      (parseReport (inserted.relabel (k ∘ j)) (decoded.relabel k))) := by
    simpa only [parseReport,unaryRename,sucRelabel,Term.relabel_relabel] using
      renameInto parsed k Ω retain
  have member' : Nonempty (Derivation B Ω (memberGraph (decoded.relabel k) (row.relabel (k ∘ j)))) := by
    change Nonempty (Derivation B Ω (programGraph scratchMember (suc z)
      ![decoded.relabel k,row.relabel (k ∘ j)]))
    change Nonempty (Derivation B Δ (programGraph scratchMember (suc z) ![decoded,row.relabel j])) at member
    simpa only [programRename,binaryRename,sucRelabel,zRelabel,Term.relabel_relabel] using
      renameInto member k Ω retain
  rw [formulaRelabelComposition]
  exact next γ (k ∘ j) Ω (decoded.relabel k) removedCode target dom cert
    (keepThrough j k keep retain) parsed' member'
    (by simpa only [Term.relabel_relabel] using reports)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanCases
