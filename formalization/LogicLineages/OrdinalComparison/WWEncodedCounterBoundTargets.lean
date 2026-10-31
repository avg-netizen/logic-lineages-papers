module
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

def EncodedQueryCodecCorrect : Prop :=
  (∀ q : ArityQuery, decodeArityQuery (Encodable.encode q) = q) ∧
    Computable queryArity ∧ Computable₂ codedQueryAt

def EncodedQueryCounterEnumerable : Prop := REPred (fun n => ¬ CodedQueryGood n)

def EncodedQueryDecisionIffCoordinateBound : Prop :=
  ComputablePred CodedQueryGood ↔ CodedCoordinateBound
end LogicLineages.OrdinalComparison.Source.Targets
