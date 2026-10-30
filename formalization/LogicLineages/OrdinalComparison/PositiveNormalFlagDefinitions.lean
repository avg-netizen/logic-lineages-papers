module
public import LogicLineages.OrdinalComparison.EncodedCollectedNormalizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

noncomputable def encodedPositiveNormalFormsEqual (n m : Nat) : Bool :=
  encodedCollectedNormalize n == encodedCollectedNormalize m

end LogicLineages.OrdinalComparison
