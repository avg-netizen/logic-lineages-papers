module
public import LogicLineages.OrdinalComparison.RawNotationCodeDefinitions
public import Mathlib.Data.List.GetD

@[expose] public section

/-! A finite-table algorithm for the additive tree norm on raw natural codes.
The table at n contains the results at codes 0 through n. At successor code,
both child codes lie in the prior table. Only structural natural recursion,
finite-list append and total indexed lookup are used. Computation certificates
are separate obligations, not inferred from this executable definition.
-/

namespace LogicLineages.OrdinalComparison

def rawNormTable : Nat → List Nat
  | 0 => [0]
  | n + 1 =>
      let table := rawNormTable n
      table ++ [(n.unpair.2.unpair.1 + 1) * (1 + table.getD n.unpair.1 0) +
        table.getD n.unpair.2.unpair.2 0]

def rawNormCode (n : Nat) : Nat := (rawNormTable n).getD n 0

end LogicLineages.OrdinalComparison
