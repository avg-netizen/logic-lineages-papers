module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardOrderProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc trans symm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalOriginalOrderProof (orderCases actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalAdditionLawsProof (leftSuccessor)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanProof (lessOfAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalNeutralRankGuard (lowersRank)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Cancel the two positive shifts using the genuine additive gap in
the original object order. This is not a reflection of a host inequality. -/
theorem exact_OpenRankCancelOrder (j k : OTerm α)
    (lt : Nonempty (Derivation B Γ (ltF (suc j) (suc k)))) :
    Nonempty (Derivation B Γ (ltF j k)) := by
  apply orderCases Γ (suc j) (suc k) _ lt
  intro β ρ Δ gap _ ⟨e⟩
  rw [orderRename]
  simp only [sucRelabel] at e
  apply actualOriginalOrderIntroduction B β Δ (j.relabel ρ) (k.relabel ρ) gap
  rw [onEquality]
  exact ⟨cancelSuc (trans (symm (leftSuccessor (j.relabel ρ) (suc gap))) e)⟩

theorem exact_OpenRankGuardOrder (g : Program 1) (x w y j k : OTerm α)
    (tgt : Nonempty (Derivation B Γ (programGraph (atTarget g) (suc j) ![x,w,y])))
    (src : Nonempty (Derivation B Γ (programGraph (atSource g) (suc k) ![x,w,y])))
    (held : Nonempty (Derivation B Γ (programGraph (lowersRank g) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (ltF j k)) := by
  have checked := compositionRecover ltTest ![atTarget g,atSource g] (suc z)
    ![x,w,y] ![suc j,suc k] held (fun n => Fin.cases tgt
      (fun m => Fin.cases src (fun h => Fin.elim0 h) m) n)
  exact exact_OpenRankCancelOrder j k (lessOfAcceptance (suc j) (suc k) checked)

#print axioms exact_OpenRankCancelOrder
#print axioms exact_OpenRankGuardOrder
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardOrderProof
