module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionDefinitions
public import Mathlib.Computability.Reduce
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBlankHaltingUniversality
def specialize (c : Nat.Partrec.Code) (n : Nat) : Nat.Partrec.Code :=
  .comp c (Nat.Partrec.Code.const n)
def output (U : Turing.ToPartrec.Code) (c : Nat.Partrec.Code) (n : Nat) : Nat :=
  SourceBlankHaltingReduction.translate U (Encodable.encode (specialize c n))
end LogicLineages.OrdinalComparison.Source.SourceBlankHaltingUniversality
