module
public import LogicLineages.CartierObserverCurrent.HigherPolesResidueTargets
public import LogicLineages.CartierObserverCurrent.NaturalityProof
public import LogicLineages.CartierObserverCurrent.HigherPolesWordProof
public import LogicLineages.CartierObserverCurrent.PeriodLaurentGenericProof
public meta import LogicLineages.Audit
@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.HigherPolesResidue
theorem extensionResidue : Targets.ExtensionResidue.{u,v} := by
  intro K L _ _ _ _ _ _ σ f a j z
  have natural (j : Nat) (g : RatFunc K) :
      Naturality.rationalMap σ ((Basic.actualDifferentialCartier (K := K))^[j] g) =
        (Basic.actualDifferentialCartier (K := L))^[j] (Naturality.rationalMap σ g) := by
    simpa only [HigherPolesWord.repeatedWord K] using
      Naturality.extensionWord K L σ (List.replicate j true) g
  rw [Nat.add_comm a j, Function.iterate_add_apply, natural]
  exact PeriodLaurentGeneric.iteratedResidue L z
    (Naturality.rationalMap σ ((Basic.actualDifferentialCartier (K := K))^[a] f)) j

#audit_namespace LogicLineages.CartierObserverCurrent.HigherPolesResidue
end LogicLineages.CartierObserverCurrent.HigherPolesResidue
