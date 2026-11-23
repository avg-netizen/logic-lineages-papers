module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalControlGraphSupportProof (equalEqn projectionValue valueUnique outputTransport)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (sameOf succOf)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalLiteralCount (entryStep entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountAbsentTargets (absentAt)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem absentHead (code head tail needle : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (no : Nonempty (Derivation B Γ (memberGraph code needle).not)) :
    Nonempty (Derivation B Γ (eqn head needle).not) := by
  let E := eqn head needle
  obtain ⟨c⟩ := cell
  obtain ⟨n⟩ := no
  have e : Derivation B (E :: Γ) E := Derivation.hypothesis List.mem_cons_self
  obtain ⟨yes⟩ := headMember code head tail needle ⟨addHyp c E⟩ ⟨symm e⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp n E) yes)⟩

private theorem absentTail (code head tail needle : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (no : Nonempty (Derivation B Γ (memberGraph code needle).not)) :
    Nonempty (Derivation B Γ (memberGraph tail needle).not) := by
  let H := memberGraph tail needle
  obtain ⟨c⟩ := cell
  obtain ⟨n⟩ := no
  obtain ⟨yes⟩ := tailMember code head tail needle ⟨addHyp c H⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp n H) yes)⟩

private theorem unchanged (head acc needle out : OTerm α)
    (no : Nonempty (Derivation B Γ (eqn head needle).not))
    (run : Nonempty (Derivation B Γ (programGraph entryStep out ![head,acc,needle]))) :
    Nonempty (Derivation B Γ (eqn acc out)) := by
  let xs : Fin 3 → OTerm α := ![head,acc,needle]
  have no' : Nonempty (Derivation B Γ (equal head needle).not) := by
    simpa only [equalEqn] using no
  have q := sameReject (.projection 0) (.projection 2) head needle xs
    (projectionValue 0 xs) (projectionValue 2 xs) no'
  have ret := zeroBranchElim (sameOf (.projection 0) (.projection 2))
    (.projection 1) (succOf (.projection 1)) out xs q run
  exact valueUnique (.projection 1) acc out xs (projectionValue 1 xs) ret

/-- The actual prior count graph is transported to the same output variable
because the real absent-head step leaves its accumulator unchanged. This
keeps the list induction query/output parameters fixed. -/
theorem consAbsent (code head tail needle previous out : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (no : Nonempty (Derivation B Γ (memberGraph code needle).not))
    (prior : Nonempty (Derivation B Γ (counted tail needle previous)))
    (run : Nonempty (Derivation B Γ (programGraph entryStep out ![head,previous,needle])))
    (ih : Nonempty (Derivation B Γ (absentAt tail needle out))) :
    Nonempty (Derivation B Γ (eqn out z)) := by
  have e := unchanged head previous needle out (absentHead code head tail needle cell no) run
  obtain ⟨p⟩ := outputTransport entryCount previous out ![tail,needle] e prior
  obtain ⟨n⟩ := absentTail code head tail needle cell no
  obtain ⟨h⟩ := ih
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction n p)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentConsProof
