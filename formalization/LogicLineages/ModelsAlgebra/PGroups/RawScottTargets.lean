module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupRawAdditiveIsomorphism : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H], (G ≃+ H) →
    Nonempty (RawIsomorphism (RawGroupStructure.ofGroup G) (RawGroupStructure.ofGroup H))

def groupRawActualGroupLaws : Prop :=
  ∀ (G : Type u) [AddCommGroup G], (RawGroupStructure.ofGroup G).AbelianLaws

def groupRawGuardScottTransfer : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (φ : Formula 0), GroupScottSentence G φ →
    RawScottSentence (RawGroupStructure.ofGroup G) (guardPi φ)

def groupRawGuardDifferenceScottTransfer : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (d : DifferenceFormula 0), DifferenceScottSentence G d →
    RawDifferenceScottSentence (RawGroupStructure.ofGroup G) (guardDifference d)

end LogicLineages.ModelsAlgebra.PGroups.Targets
