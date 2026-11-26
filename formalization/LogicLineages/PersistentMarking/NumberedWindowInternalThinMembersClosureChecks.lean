module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFuelBudgetChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape poolLength members membersTape)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseRoundReachChecks (exact_RoundEdgeExtension)
open NumberedWindowInternalThinFuelBudgetChecks (exact_LengthStability)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinMembersClosureTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_LengthStableFromPredecessor : ExactLengthStableFromPredecessor := by
  intro bound pred strict
  exact exact_LengthStability bound pred strict

private theorem atLength (bound : CountLengthBound) (pred : ExactRetainedPredecessor)
    (strict : NumberedWindowInternalThinUncoveredCountTargets.InternalStrictDecrease) (E : Program 4)
    (vertices ctx ty seed size pool source target : OTerm α)
    (len : Nonempty (Derivation body Γ (unary poolLength size vertices)))
    (out : Nonempty (Derivation body Γ (roundGraph E pool size vertices ctx ty seed)))
    (edge : Nonempty (Derivation body Γ ((memberGraph pool source ⊓ acceptEdge E ctx ty source target) ⊓
      memberGraph vertices target))) : Nonempty (Derivation body Γ (memberGraph pool target)) := by
  apply programCases (rounds E) (roundsTape (suc size) vertices ctx ty seed) _
  intro β j Δ next keep nextOut
  rw [graphRename]
  have l := renameInto len j Δ keep
  rw [unaryRename] at l
  have o := renameInto out j Δ keep
  rw [roundRename] at o
  have e := renameInto edge j Δ keep
  simp only [conjunctionRename,graphRename,acceptEdge,programRename,edgeTape,quadInputsRename,
    sucRelabel,zRelabel] at e
  have tape : (fun k => (roundsTape (suc size) vertices ctx ty seed k).relabel j) =
      roundsTape (suc (size.relabel j)) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
    funext k
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
      Fin.cases ?_ (fun d => Fin.cases ?_ (fun u => Fin.elim0 u) d) c) b) a) k <;> first | rfl | exact sucRelabel size j
  rw [tape] at nextOut
  obtain ⟨nextD⟩ := nextOut
  obtain ⟨o⟩ := o
  obtain ⟨e⟩ := e
  obtain ⟨l⟩ := l
  have stages := Derivation.conjunctionIntroduction o nextD
  obtain ⟨persist⟩ := exact_LengthStableFromPredecessor bound pred strict E body β Δ (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) (size.relabel j) (pool.relabel j) next
  obtain ⟨extend⟩ := exact_RoundEdgeExtension E body β Δ (pool.relabel j) next (size.relabel j)
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (source.relabel j) (target.relabel j)
  exact NumberedWindowInternalScratchInclusionThinProof.eliminate next (pool.relabel j) (target.relabel j)
    ⟨Derivation.implicationElimination persist (Derivation.conjunctionIntroduction l stages)⟩
    ⟨Derivation.implicationElimination extend (Derivation.conjunctionIntroduction stages e)⟩

theorem exact_MembersEdgeClosure : ExactMembersEdgeClosure := by
  intro bound pred strict E body α Γ vertices ctx ty seed pool source target
  let A := programGraph (members E) pool (membersTape vertices ctx ty seed) ⊓
    ((memberGraph pool source ⊓ acceptEdge E ctx ty source target) ⊓ memberGraph vertices target)
  let Δ := A :: Γ
  have d : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have closure : Nonempty (Derivation body Δ (memberGraph pool target)) := by
    apply programCases poolLength ![vertices] _
    intro β j Θ size keep len
    rw [graphRename]
    rw [unaryInputsRename] at len
    have h := renameInto ⟨d⟩ j Θ keep
    simp only [A,conjunctionRename,graphRename,acceptEdge,programRename,membersTape,edgeTape,
      quadInputsRename,sucRelabel,zRelabel] at h
    obtain ⟨h⟩ := h
    obtain ⟨l⟩ := len
    obtain ⟨atLen⟩ := exact_OpenMembersAtLength E body β Θ (pool.relabel j) size (vertices.relabel j)
      (ctx.relabel j) (ty.relabel j) (seed.relabel j)
    have r := Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination atLen l)) (Derivation.conjunctionLeft h)
    exact atLength bound pred strict E (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) size
      (pool.relabel j) (source.relabel j) (target.relabel j) ⟨l⟩ ⟨r⟩ ⟨Derivation.conjunctionRight h⟩
  obtain ⟨closed⟩ := closure
  exact ⟨Derivation.implicationIntroduction closed⟩

#print axioms exact_LengthStableFromPredecessor
#print axioms exact_MembersEdgeClosure
end LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureChecks
