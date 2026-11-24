module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedPackedLeastAtPoolsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedSeedReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedPackedLeastProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinPackedPairState
open NumberedWindowInternalThinPackedSeedReportProof
open NumberedWindowInternalThinPairedPackedLeastAtPoolsProof

private theorem edgeRename {α β : Type} (E : Program 4) (ctx ty a b : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty a b).relabel j = acceptEdge E (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Two original actual least reports on a genuine guarded paired edge
agree, with each physical cover, pool, length, and pass chosen internally.
Only the actual original occurrence-count laws remain as supplied rules. -/
theorem exact_OpenThinPairedPackedLeast (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (base : Program 2) (W : Program 3) (s : Settings)
    (ctx ty a b x y : OTerm α) :
    let X := guardedExchange C s (pairedExchange base)
    Nonempty (Derivation B Γ (leastGraph C X W s ctx ty a x)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx ty b y)) →
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx ty a b)) →
    Nonempty (Derivation B Γ (eqn x y)) := by
  intro X left right edge
  apply exact_OpenThinPackedSeedReport C X W s ctx ty a x (eqn x y) left
  intro β j Δ va pa keep ra
  rw [eqnRelabel]
  have right' := renameInto right j Δ keep
  rw [leastRename] at right'
  have edge' := renameInto edge j Δ keep
  rw [edgeRename] at edge'
  apply exact_OpenThinPackedSeedReport C X W s (ctx.relabel j) (ty.relabel j) (b.relabel j) (y.relabel j)
    (eqn (x.relabel j) (y.relabel j)) right'
  intro γ k Θ vb pb keep' rb
  rw [eqnRelabel]
  have ee := renameInto edge' k Θ keep'
  rw [edgeRename] at ee
  have ll := renameInto ra k Θ keep'
  rw [seedRename] at ll
  obtain ⟨ee⟩ := ee
  obtain ⟨ll⟩ := ll
  obtain ⟨rr⟩ := rb
  let p : PairPlan γ := ⟨(ctx.relabel j).relabel k,(ty.relabel j).relabel k,
    (a.relabel j).relabel k,(b.relabel j).relabel k,va.relabel k,vb,pa.relabel k,pb,
    (x.relabel j).relabel k,(y.relabel j).relabel k⟩
  exact exact_OpenThinPairedPackedLeastAtPools bound strict C base W s p
    ⟨Derivation.conjunctionIntroduction ll (Derivation.conjunctionIntroduction rr ee)⟩

#print axioms exact_OpenThinPairedPackedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedPackedLeastProof
