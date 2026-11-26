module
public import LogicLineages.PermittedControl.RelativeNormDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Course-of-values profile computation. All raw codes have a total result;
normality is required only for the actual-ordinal interpretation. -/
def rawProfileTable (e : Nat) : Nat → List Nat
  | 0 => [0]
  | n+1 => rawProfileTable e n ++ [
      (if rawComparisonCode e n.unpair.1 = 2 then 0
       else (n.unpair.2.unpair.1+1)*(1+rawNormCode n.unpair.1)) +
      (rawProfileTable e n).getD n.unpair.2.unpair.2 0]

def rawProfileCode (mu e : Nat) : Nat := (rawProfileTable e mu).getD mu 0

/-- The finite actual CNF breakpoint list of the two profiles, without
silently restricting to unabsorbed suffixes. Duplicates are harmless. -/
noncomputable def jointProfileBreakpoints (mu nu : Ordinal.{0}) : List Ordinal :=
  (Ordinal.CNF Ordinal.omega0 mu).map Prod.fst ++
  (Ordinal.CNF Ordinal.omega0 nu).map Prod.fst

/-- Exact common-piece relation, retaining the right endpoint at every
breakpoint. The clipped [2,E) domain is imposed separately. -/
def SameProfilePiece (mu nu x y : Ordinal.{0}) : Prop :=
  ∀ b ∈ jointProfileBreakpoints mu nu, (x ≤ b ↔ y ≤ b)

/-- Finite representatives for all pieces on [2,E): included breakpoints,
2, and the immediate successor of each lower edge when still below E.
Unlike the final source highest-piece selector this supporting cover need
not select the maximum exponent in each piece. -/
noncomputable def jointProfileRepresentatives (mu nu E : Ordinal.{0}) : List Ordinal :=
  (2 :: jointProfileBreakpoints mu nu ++
    (jointProfileBreakpoints mu nu).map (fun b => b+1)).filter (fun e => 2 ≤ e ∧ e < E)

end LogicLineages.PermittedControl
