module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedDownwardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierObjectProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDropProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankBothUnrankedDownwardProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalNeutralRankGuard (rankApplication)
open NumberedWindowInternalRankUniversalCarrier (completeRankEven alwaysCarried)
open NumberedWindowInternalNeutralRankGuardDropProof (exact_OpenRankGuardDrop)
open NumberedWindowInternalNeutralRankGuardApplicationProof (exact_OpenRankGuardedApplication)
open NumberedWindowInternalRankUniversalCarrierObjectProof (exact_OpenCompleteRankEdgeCarrier)
open NumberedWindowInternalNeutralBothUnrankedDownwardTargets (BothUnrankedApplicationEdgeMatching)
open NumberedWindowInternalNeutralBothUnrankedDownwardProof (exact_BothUnrankedComputabilityDownward)

theorem exact_CompleteRankBothUnrankedComputabilityDownward
    (i j g : Program 1) (r d p : Program 3) (c : Nat)
    (matchEdge : BothUnrankedApplicationEdgeMatching
      (data i j (completeRankEven i g r) d) g (rankApplication i g p) c) :
    ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (f f' : OTerm α),
      let S := data i j (completeRankEven i g r) d
      let P := rankApplication i g p
      let B := sourceBody S c
      Nonempty (Derivation B Γ (formula P τ f)) →
      Nonempty (Derivation B Γ (edge S false c f f')) →
      Nonempty (Derivation B Γ (formula P τ f')) :=
  exact_BothUnrankedComputabilityDownward (data i j (completeRankEven i g r) d)
    g (rankApplication i g p) c (exact_OpenRankGuardDrop i j g (alwaysCarried i r) d c)
    (exact_OpenCompleteRankEdgeCarrier i j g r d c)
    (exact_OpenRankGuardedApplication i j g (completeRankEven i g r) d p c) matchEdge

#print axioms exact_CompleteRankBothUnrankedComputabilityDownward
end LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankBothUnrankedDownwardProof
