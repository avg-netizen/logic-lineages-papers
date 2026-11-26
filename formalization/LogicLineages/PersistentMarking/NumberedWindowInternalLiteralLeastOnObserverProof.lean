module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverInductionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedLeastOnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnObserverProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover programCompositionCases)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseScratchMembershipOpenChecks (exact_OpenScratchMinimumOccurs)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves inputs)
open NumberedWindowInternalLiteralRoundObserverInductionProof (exact_OpenRoundObserver)
open NumberedWindowInternalLiteralRoundObserverSyntaxProof (observeRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

private theorem atLength (E : Program 4)
    (O : Program 3) (paid : Preserves E O) (ctx ty seed m v vertices pool : OTerm α)
    (observed : Nonempty (Derivation body Γ (observe O ctx ty seed v)))
    (hit : Nonempty (Derivation body Γ (memberGraph pool m)))
    (computed : Nonempty (Derivation body Γ (programGraph (members E) pool (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (observe O ctx ty m v)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep length
  rw [observeRename O]
  rw [unaryInputsRename] at length
  have value := renameInto observed j Δ keep
  rw [observeRename O] at value
  have g := renameInto hit j Δ keep
  rw [graphRename] at g
  have ss := renameInto computed j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at ss
  obtain ⟨atLen⟩ := exact_OpenMembersAtLength E body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨l⟩ := length
  obtain ⟨computedValue⟩ := ss
  obtain ⟨g⟩ := g
  obtain ⟨value⟩ := value
  have run := Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) computedValue
  exact exact_OpenRoundObserver E O paid fuel (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (pool.relabel j) (m.relabel j) (v.relabel j)
    ⟨Derivation.conjunctionIntroduction value (Derivation.conjunctionIntroduction run g)⟩


/-- Recover the actual cover bound and its directed rounds from the
physical pool reported by the original minimum. -/
private theorem fromMembers (C : Program 3) (E : Program 4) (s : Settings)
    (O : Program 3) (paid : Preserves E O) (ctx ty seed m v pool : OTerm α)
    (observed : D body Γ (observe O ctx ty seed v))
    (hit : D body Γ (memberGraph pool m))
    (computed : D body Γ (programGraph (membersAtSeedOn C E s) pool ![ctx,ty,seed])) :
    D body Γ (observe O ctx ty m v) := by
  apply programCases (poolAtSeed C s) ![ctx,ty,seed] _
  intro β j Δ vertices keep vv
  rw [observeRename O]
  rw [tripleInputsRename] at vv
  have old := renameInto observed j Δ keep
  rw [observeRename O] at old
  have selected := renameInto hit j Δ keep
  rw [graphRename] at selected
  have ss := renameInto computed j Δ keep
  rw [programRename,tripleInputsRename] at ss
  let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  apply atLength E O paid (ctx.relabel j) (ty.relabel j) (seed.relabel j) (m.relabel j)
    (v.relabel j) vertices (pool.relabel j) old selected
  apply compositionRecover (members E) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    (pool.relabel j) xs (membersTape vertices (ctx.relabel j) (ty.relabel j) (seed.relabel j)) ss
  intro k
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · exact vv
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 2 xs
/-- The success of the physically selected minimum transports any
observer preserved by the same edge checker. This uses the original
context test and the actual scratch minimum, not a numeric comparison. -/
theorem exact_OpenLiteralSelectedObserverOn (C : Program 3) (E : Program 4) (s : Settings)
    (O : Program 3) (paid : Preserves E O) (ctx ty seed m v : OTerm α)
    (least : D body Γ (leastOnGraph C E s ctx ty seed m))
    (observed : D body Γ (observe O ctx ty seed v)) :
    D body Γ (observe O ctx ty m v) := by
  apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α) _
  · intro β j Δ keep missing
    rw [observeRename] 
    rw [tripleInputsRename] at missing
    have h := renameInto least j Δ keep
    simp only [leastOnGraph,programRename,sucRelabel,tripleInputsRename] at h
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have lost := zeroBranchElim contextOption (constantZero 3) (minimumAtMembersOn C E s)
      (suc (m.relabel j)) xs missing h
    obtain ⟨no⟩ := valueUnique (constantZero 3) (suc (m.relabel j)) z xs lost (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply no)⟩
  · intro β j Δ payload keep known
    rw [observeRename]
    rw [tripleInputsRename] at known
    have h := renameInto least j Δ keep
    simp only [leastOnGraph,programRename,sucRelabel,tripleInputsRename] at h
    have old := renameInto observed j Δ keep
    rw [observeRename] at old
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have chosen := successorBranchElim contextOption (constantZero 3)
      (minimumAtMembersOn C E s) (suc (m.relabel j)) payload xs known h
    apply programCompositionCases scratchMinimum (fun _ : Fin 1 => membersAtSeedOn C E s)
      (suc (m.relabel j)) xs (observe O (ctx.relabel j) (ty.relabel j) (m.relabel j) (v.relabel j)) chosen
    intro γ k ys Θ keep' minimum pooled
    rw [observeRename]
    rw [sucRelabel] at minimum
    have old' := renameInto old k Θ keep'
    rw [observeRename] at old'
    have pooled' := pooled 0
    change D body Θ (programGraph (membersAtSeedOn C E s) (ys 0)
      (fun i => ((![ctx.relabel j,ty.relabel j,seed.relabel j] : Fin 3 → OTerm β) i).relabel k)) at pooled'
    rw [tripleInputsRename] at pooled'
    have tuple : (![ys 0] : Fin 1 → OTerm γ) = ys := by
      funext i
      obtain rfl := Fin.eq_zero i
      rfl
    obtain ⟨occurs⟩ := exact_OpenScratchMinimumOccurs body γ Θ (ys 0) ((m.relabel j).relabel k)
    change Derivation body Θ ((programGraph scratchMinimum (suc ((m.relabel j).relabel k))
      (![ys 0] : Fin 1 → OTerm γ)).imp (memberGraph (ys 0) ((m.relabel j).relabel k))) at occurs
    rw [tuple] at occurs
    obtain ⟨small⟩ := minimum
    exact fromMembers C E s O paid ((ctx.relabel j).relabel k) ((ty.relabel j).relabel k)
      ((seed.relabel j).relabel k) ((m.relabel j).relabel k) ((v.relabel j).relabel k) (ys 0)
      old' ⟨Derivation.implicationElimination occurs small⟩ pooled'

#print axioms exact_OpenLiteralSelectedObserverOn
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnObserverProof
