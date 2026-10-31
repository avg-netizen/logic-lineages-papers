module
public import LogicLineages.ComputabilityKnowledge.PredictionFixedUniversalDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFixedUniversal.Targets

def UniversalPartialRecursive : Prop := Partrec₂ run

def FixedVectorUniversal : Prop := ∃ U : Turing.ToPartrec.Code,
  ∀ v : List.Vector Nat 2, U.eval v.val = (fun n : Nat => [n]) <$> vectorRun v

/-- A single finite sequential program works for every ordinary predictor index
and every binary history, preserving partiality and arbitrary natural outputs. -/
def FixedUniversal : Prop := ∃ U : Turing.ToPartrec.Code,
  ∀ (e : Nat) (xs : List Bool),
    U.eval [PredictionBinarySentinel.inputNat xs, e] =
      (fun v : Nat => [v]) <$> (Nat.Partrec.Code.ofNatCode e).eval (Encodable.encode xs)
end LogicLineages.ComputabilityKnowledge.PredictionFixedUniversal.Targets
