module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityCountProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchFactsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenChecks (exact_OpenScratchAppendMembership)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralMemberReverse)
open NumberedWindowInternalLiteralSingletonScratchFactsProof (exact_LiteralSingletonCount exact_LiteralSingletonMember)
open NumberedWindowInternalLiteralSingletonCapacityCountProof (exact_LiteralSingletonCapacityAtNeedle)
open NumberedWindowInternalLiteralSingletonCapacityTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem keyMove (xs left right : OTerm α)
    (he : Nonempty (Derivation B Γ (eqn left right)))
    (hm : Nonempty (Derivation B Γ (memberGraph xs left))) :
    Nonempty (Derivation B Γ (memberGraph xs right)) := by
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula scratchMember) (suc z)
    ![xs,left] ![xs,right] _ hm
  intro j
  refine Fin.cases ?_ (fun l => ?_) j
  · rw [onEquality]
    exact ⟨refl xs⟩
  · obtain rfl := Fin.eq_zero l
    rw [onEquality]
    exact he

private theorem singletonOrigin (src head out key : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph src head z)))
    (tested : Nonempty (Derivation B Γ (observed src out)))
    (occurred : Nonempty (Derivation B Γ (memberGraph out key))) :
    Nonempty (Derivation B Γ (eqn key head)) := by
  have atSrc := exact_LiteralMemberReverse B α Γ src out key tested occurred
  obtain ⟨same⟩ := exact_LiteralSingletonMember B α Γ src head key cell atSrc
  exact ⟨symm same⟩

theorem exact_LiteralSingletonKeptAbsent : ExactLiteralSingletonKeptAbsent := by
  intro B α Γ src q kept removed joined removedKey keptKey hc hr ap perm
  let P := memberGraph kept keptKey
  let Δ := P :: Γ
  obtain ⟨cell⟩ := hc
  obtain ⟨rightOne⟩ := hr
  obtain ⟨appended⟩ := ap
  obtain ⟨checked⟩ := perm
  have cell' : Nonempty (Derivation B Δ (consGraph src q z)) := ⟨addHyp cell P⟩
  have lr : Derivation B Δ (memberGraph kept keptKey) := Derivation.hypothesis List.mem_cons_self
  have rr : Derivation B Δ (memberGraph removed removedKey) := addHyp rightOne P
  have ap' : Nonempty (Derivation B Δ (appendGraph joined kept removed)) := ⟨addHyp appended P⟩
  have obs : Nonempty (Derivation B Δ (observed src joined)) := ⟨addHyp checked P⟩
  have leftInJoin := exact_OpenScratchAppendMembership B α Δ kept removed joined keptKey ap' ⟨orLeft lr⟩
  have rightInJoin := exact_OpenScratchAppendMembership B α Δ kept removed joined removedKey ap' ⟨orRight rr⟩
  have leftEq := singletonOrigin src q joined keptKey cell' obs leftInJoin
  have rightEq := singletonOrigin src q joined removedKey cell' obs rightInJoin
  have leftSame := keyMove kept keptKey q leftEq ⟨lr⟩
  have rightSame := keyMove removed removedKey q rightEq ⟨rr⟩
  have h : Held B Δ src q kept removed joined :=
    ⟨exact_LiteralSingletonCount B α Δ src q cell',ap',obs⟩
  obtain ⟨bad⟩ := exact_LiteralSingletonCapacityAtNeedle src q kept removed joined h leftSame rightSame
  exact ⟨Derivation.implicationIntroduction bad⟩

#print axioms exact_LiteralSingletonKeptAbsent
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityProof
