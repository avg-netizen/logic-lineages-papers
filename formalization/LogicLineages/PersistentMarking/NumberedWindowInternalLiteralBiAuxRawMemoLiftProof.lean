module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoVaryingParentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoLiftProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralTypedAuxEdgesReversalProof (exact_OpenReverseTypedChildCases)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralTypedDualMemoProof
open NumberedWindowInternalLiteralBiAuxRawMemoStageProof (rawAuxMemoStage)
open NumberedWindowInternalLiteralBiAuxRawMemoOpenProof
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof (varyAuxiliary)
open NumberedWindowInternalLiteralMemoVaryingParentProof (varyingOperandType)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange swapExchange)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPairedRawReports (X : Program 2) (q r : OTerm α) :
    D B Γ (programGraph (pairedExchange X) (suc z) ![q,r]) ↔
      D B Γ (programGraph X (suc z) ![q,r]) ∧ D B Γ (programGraph X (suc z) ![r,q]) := by
  let xs : Fin 2 → OTerm α := ![q,r]
  let ps : Fin 2 → Program 2 := ![.projection 1,.projection 0]
  have tape : ∀ i, D B Γ (programGraph (ps i) (![r,q] i) xs) := fun i =>
    Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 0 xs) (fun n => Fin.elim0 n)) i
  constructor
  · intro h
    obtain ⟨both⟩ := conjunctionRecover X (swapExchange X) xs h
    exact ⟨⟨Derivation.conjunctionLeft both⟩,
      compositionRecover X ps (suc z) xs ![r,q] ⟨Derivation.conjunctionRight both⟩ tape⟩
  · rintro ⟨f,b⟩
    exact conjunctionAccept X (swapExchange X) xs f (compositionValue X ps (suc z) xs ![r,q] b tape)

private theorem childAsMemo (X : Program 2) (V : Program 1) (ty q r : OTerm α)
    (held : D B Γ (programGraph (pairedExchange (biAuxRawMemo X V)) (suc z) ![q,r])) :
    D B Γ (acceptEdge (dualContextMemo (constantOne 4) (rawAuxMemoStage X V)) z ty q r) := by
  obtain ⟨f,b⟩ := (exact_OpenPairedRawReports (biAuxRawMemo X V) q r).mp held
  exact (exact_OpenDualContextMemo (constantOne 4) (rawAuxMemoStage X V) z ty q r).mpr
    ⟨oneConstantValue ![z,ty,q,r],(exact_OpenBiAuxRawMemoSelected X V q r).mp f,
      (exact_OpenBiAuxRawMemoSelected X V r q).mp b⟩

private theorem parentAsPair (X : Program 2) (V : Program 1) (a b : AuxRow α)
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (left : D B Γ (unary V (suc z) a.term)) (right : D B Γ (unary V (suc z) b.term))
    (child : D B Γ (childAlternatives (dualContextMemo (constantOne 4) (rawAuxMemoStage X V)) z a b)) :
    D B Γ (programGraph (pairedExchange (biAuxRawMemo X V)) (suc z) ![a.term,b.term]) := by
  have trivialReverse : CanReverse (constantOne 4) := by
    intro B α Γ ctx ty q r _
    exact oneConstantValue ![ctx,ty,r,q]
  have back := exact_OpenDualContextMemoReverse (constantOne 4) (rawAuxMemoStage X V) trivialReverse
  have reverse := exact_OpenReverseTypedChildCases _ back z a b dom cod child
  have f := exact_OpenBiAuxRawParentMemo X V a b dom cod left right child
  obtain ⟨dom⟩ := dom
  obtain ⟨cod⟩ := cod
  have r := exact_OpenBiAuxRawParentMemo X V b a ⟨symm dom⟩ ⟨symm cod⟩ right left reverse
  exact (exact_OpenPairedRawReports (biAuxRawMemo X V) a.term b.term).mpr
    ⟨(exact_OpenBiAuxRawMemoSelected X V a.term b.term).mpr f,
      (exact_OpenBiAuxRawMemoSelected X V b.term a.term).mpr r⟩

/-- Enclose either actual paired raw child exchange in the corresponding
literal auxiliary parent. The fixed operand does not change, and both
parent syntax checks are still paid by their actual graphs. -/
theorem exact_OpenBiAuxRawExchangeLifts (X : Program 2) (V : Program 1) (v : Bool)
    (d c q r fixed : OTerm α)
    (arc : D B Γ (programGraph (pairedExchange (biAuxRawMemo X V)) (suc z) ![q,r]))
    (left : D B Γ (unary V (suc z) (varyAuxiliary v d c q fixed)))
    (right : D B Γ (unary V (suc z) (varyAuxiliary v d c r fixed))) :
    D B Γ (programGraph (pairedExchange (biAuxRawMemo X V)) (suc z)
      ![varyAuxiliary v d c q fixed,varyAuxiliary v d c r fixed]) := by
  have actual := childAsMemo X V (varyingOperandType v d c) q r arc
  obtain ⟨step⟩ := actual
  cases v
  · exact parentAsPair X V ⟨d,c,q,fixed⟩ ⟨d,c,r,fixed⟩ ⟨refl d⟩ ⟨refl c⟩ left right
      ⟨orLeft (Derivation.conjunctionIntroduction step (refl fixed))⟩
  · exact parentAsPair X V ⟨d,c,fixed,q⟩ ⟨d,c,fixed,r⟩ ⟨refl d⟩ ⟨refl c⟩ left right
      ⟨orRight (Derivation.conjunctionIntroduction (refl fixed) step)⟩

#print axioms exact_OpenPairedRawReports
#print axioms exact_OpenBiAuxRawExchangeLifts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoLiftProof
