module
public import LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixTargets
open Turing PredictionFiniteAlphabet PredictionNumericPrefix

def EffectiveNumericAssembly : Prop := Primrec (fun z : Table × Nat × List Nat => code z.1 z.2.1 z.2.2)

def ExactBodyLookup : Prop :=
  ∀ (p : Table) (q : Nat) (word : List Nat), p.2.2.length ≤ q * width p →
    ∀ s a : Nat, s < q → lookup (assembled p q word) s a = lookup p s a

def ExactPrefixLookup : Prop :=
  ∀ (p : Table) (q : Nat) (word : List Nat), p.2.2.length ≤ q * width p →
    ∀ r a : Nat, r < 2 * word.length →
      lookup (assembled p q word) (q + r) a = some (prefixEntry p q word r)

def ExactBodyStep : Prop :=
  ∀ (p : Table) (q : Nat) (word : List Nat), p.2.2.length ≤ q * width p →
    ∀ x : TM0.Cfg (Fin (width p)) Nat, x.q < q →
      TM0.step (PredictionNumericPrefix.machine p q word) x =
        TM0.step (PredictionFiniteAlphabet.machine p) x

end LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixTargets
