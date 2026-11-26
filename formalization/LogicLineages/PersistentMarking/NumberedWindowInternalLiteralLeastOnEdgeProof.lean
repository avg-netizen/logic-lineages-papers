module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnAtPoolsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnMembersProof (leastOnRename)
open NumberedWindowInternalLiteralLeastOnAtPoolsProof
open NumberedWindowInternalLiteralEdgeOnCoverProof (KeepsCover)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse edgeRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalThinPackedPairState

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Choose the actual original cover and members outputs at a genuine
held least, without imposing any equality of different raw seeds. -/
theorem exact_OpenLeastOnSeedReport (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed least : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (leastOnGraph C E s ctx ty seed least)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (vertices pool : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (seedOn C E s (ctx.relabel j) (ty.relabel j)
        (seed.relabel j) vertices pool (least.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases (scratchVertices C s) ![seed] goal
  intro β j Δ verts keep cover
  rw [unaryInputsRename] at cover
  have min := renameInto held j Δ keep
  rw [leastOnRename] at min
  apply programCases (membersAtSeedOn C E s) ![ctx.relabel j,ty.relabel j,seed.relabel j] (goal.relabel j)
  intro γ k Θ pool keep' chosen
  rw [tripleInputsRename] at chosen
  have l := renameInto min k Θ keep'
  have r := renameInto (phi := NumberedWindowInternalSparsePathEnvelopeTargets.unary (scratchVertices C s) verts (seed.relabel j)) cover k Θ keep'
  simp only [leastOnRename,Term.relabel_relabel] at l
  simp only [unaryRename,Term.relabel_relabel] at r
  simp only [Term.relabel_relabel] at chosen
  have together (f : Formula α) (mem : f ∈ Γ) : f.relabel (k ∘ j) ∈ Θ := by
    rw [← formulaRelabelComposition j k f]
    exact keep' _ (keep f mem)
  obtain ⟨l⟩ := l
  obtain ⟨r⟩ := r
  obtain ⟨p⟩ := chosen
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Θ (verts.relabel k) pool together
    ⟨Derivation.conjunctionIntroduction l (Derivation.conjunctionIntroduction r p)⟩

/-- Actual paired same-cover edges yield equal selected least values
for the same physical, possibly enriched, round program. -/
theorem exact_OpenLeastOnEdge (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (E : Program 4) (s : Settings) (reverses : CanReverse E)
    (coverLaw : KeepsCover C s E) (ctx ty a b x y : OTerm α)
    (left : Nonempty (Derivation B Γ (leastOnGraph C E s ctx ty a x)))
    (right : Nonempty (Derivation B Γ (leastOnGraph C E s ctx ty b y)))
    (edge : Nonempty (Derivation B Γ (acceptEdge E ctx ty a b))) :
    Nonempty (Derivation B Γ (eqn x y)) := by
  apply exact_OpenLeastOnSeedReport C E s ctx ty a x (eqn x y) left
  intro β j Δ va pa keep ra
  rw [eqnRelabel]
  have right' := renameInto right j Δ keep
  rw [leastOnRename] at right'
  have edge' := renameInto edge j Δ keep
  rw [edgeRename] at edge'
  apply exact_OpenLeastOnSeedReport C E s (ctx.relabel j) (ty.relabel j) (b.relabel j) (y.relabel j)
    (eqn (x.relabel j) (y.relabel j)) right'
  intro γ k Θ vb pb keep' rb
  rw [eqnRelabel]
  have ee := renameInto edge' k Θ keep'
  rw [edgeRename] at ee
  have ll := renameInto ra k Θ keep'
  rw [seedOnRename] at ll
  obtain ⟨ee⟩ := ee
  obtain ⟨ll⟩ := ll
  obtain ⟨rr⟩ := rb
  let p : PairPlan γ := ⟨(ctx.relabel j).relabel k,(ty.relabel j).relabel k,
    (a.relabel j).relabel k,(b.relabel j).relabel k,va.relabel k,vb,pa.relabel k,pb,
    (x.relabel j).relabel k,(y.relabel j).relabel k⟩
  exact exact_OpenLeastOnAtPools bound strict C E s reverses coverLaw p
    ⟨Derivation.conjunctionIntroduction ll (Derivation.conjunctionIntroduction rr ee)⟩

#print axioms exact_OpenLeastOnSeedReport
#print axioms exact_OpenLeastOnEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnEdgeProof
