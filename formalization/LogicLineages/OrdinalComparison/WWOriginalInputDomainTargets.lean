module
public import LogicLineages.OrdinalComparison.WWOriginalInputDomainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

def OriginalInputCodecCorrect : Prop :=
  (∀ q : OriginalInput.Query, OriginalInput.decode (Encodable.encode q) = q) ∧
    Primrec OriginalInput.decode

def OriginalInputUniversalTupleEquivalence : Prop :=
  ∀ q : OriginalInput.Query, OriginalInput.Good q ↔
    ∀ xs : List Nat, xs.length = q.1 → OriginalInput.Point q xs
end LogicLineages.OrdinalComparison.Source.Targets
