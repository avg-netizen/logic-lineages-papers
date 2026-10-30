module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupRawIsomorphismAdditive : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H],
    RawIsomorphism (RawGroupStructure.ofGroup G) (RawGroupStructure.ofGroup H) → Nonempty (G ≃+ H)

def groupRawScottRestriction : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (φ : Formula 0),
    RawScottSentence (RawGroupStructure.ofGroup G) φ → GroupScottSentence G φ

def groupRawDifferenceScottRestriction : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (d : DifferenceFormula 0),
    RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d → DifferenceScottSentence G d

end LogicLineages.ModelsAlgebra.PGroups.Targets
