module

public import LogicLineages.ComputabilityKnowledge.PredictionLearning

@[expose] public section
/-! Paper 14 lines 261–269. Literal reconstruction from shorter evasion
prefixes; this states no efficiency or source tape-runtime bound. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionSelfHistory
open PredictionGame

abbrev PairedRule := List Bool → List Bool → Bool

def reconstructStep (R : PairedRule) (h : List Bool × List Bool) (x : Bool) :
    List Bool × List Bool :=
  (h.1 ++ [x], h.2 ++ [R h.1 h.2])

def reconstruct (R : PairedRule) (xs : List Bool) : List Bool × List Bool :=
  xs.foldl (reconstructStep R) ([], [])

def selfPolicy (R : PairedRule) : Policy :=
  fun xs => R xs (reconstruct R xs).2

end LogicLineages.ComputabilityKnowledge.PredictionSelfHistory
