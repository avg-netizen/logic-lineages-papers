module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (contextOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow contextPresent ownSeed)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rawProjection (ctx ty seed : OTerm α) (i : Fin 1) :
    Nonempty (Derivation B Γ
      (programGraph (Program.projection 2) ((![seed] : Fin 1 → OTerm α) i) ![ctx,ty,seed])) := by
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,seed]

/-- The actual installed syntax-refined base callback is introduced from its
two genuine reports on exactly the original input tape. -/
theorem exact_OpenUnrestrictedSyntaxWindowIntro (baseW : Program 3) (V : Program 1) (ctx ty seed : OTerm α)
    (base : Nonempty (Derivation B Γ (windowAt baseW ctx ty seed)))
    (valid : Nonempty (Derivation B Γ (unary V (suc z) seed))) :
    Nonempty (Derivation B Γ (windowAt (syntaxWindow baseW V) ctx ty seed)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  let selected : Program 3 := .composition V (fun _ : Fin 1 => .projection 2)
  have raw : Nonempty (Derivation B Γ (programGraph selected (suc z) xs)) :=
    compositionValue V (fun _ : Fin 1 => .projection 2) (suc z) xs ![seed] valid (rawProjection ctx ty seed)
  exact conjunctionAccept baseW selected xs base raw

/-- From the same actual coupled window extract its base, syntax, and context
checks, without interpreting an opaque acceptance numerically. -/
theorem exact_OpenUnrestrictedWindowReports (C : Program 3) (s : Settings) (baseW : Program 3)
    (V : Program 1) (ctx ty seed : OTerm α)
    (held : Nonempty (Derivation B Γ (windowAt (window C s baseW V) ctx ty seed))) :
    Nonempty (Derivation B Γ (windowAt baseW ctx ty seed ⊓
      (unary V (suc z) seed ⊓ windowAt contextPresent ctx ty seed))) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  obtain ⟨outer⟩ := conjunctionRecover (syntaxWindow baseW V) (conjunction contextPresent (ownSeed C s)) xs held
  obtain ⟨inner⟩ := conjunctionRecover baseW (.composition V (fun _ : Fin 1 => .projection 2)) xs
    ⟨Derivation.conjunctionLeft outer⟩
  obtain ⟨guards⟩ := conjunctionRecover contextPresent (ownSeed C s) xs ⟨Derivation.conjunctionRight outer⟩
  obtain ⟨syntaxBit⟩ := compositionRecover V (fun _ : Fin 1 => .projection 2) (suc z) xs ![seed]
    ⟨Derivation.conjunctionRight inner⟩ (rawProjection ctx ty seed)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft inner)
    (Derivation.conjunctionIntroduction syntaxBit (Derivation.conjunctionLeft guards))⟩

/-- Open the actual context Option from the physical context-present bit.
The zero result contradicts that bit; the successful payload stays exact. -/
theorem exact_OpenUnrestrictedContextPresentCases (ctx ty seed : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (windowAt contextPresent ctx ty seed)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (programGraph contextOption (suc payload)
        ![ctx.relabel j,ty.relabel j,seed.relabel j])) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  let h : Nonempty (Derivation B Γ (programGraph contextPresent (suc z) ![ctx,ty,seed])) := held
  apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α) goal
  · intro β j Δ keep zero
    rw [tripleInputsRename] at zero
    have yes := renameInto h j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at yes
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have impossible := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs zero yes
    obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc z) z xs impossible (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename] at parsed
    exact next β j Δ payload keep parsed

#print axioms exact_OpenUnrestrictedSyntaxWindowIntro
#print axioms exact_OpenUnrestrictedWindowReports
#print axioms exact_OpenUnrestrictedContextPresentCases
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
