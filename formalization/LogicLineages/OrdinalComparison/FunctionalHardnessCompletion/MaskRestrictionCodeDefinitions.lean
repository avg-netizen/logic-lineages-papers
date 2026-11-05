module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode

def maskCode {n : Nat} (z : Mask n) : List Bool := List.ofFn z
def extendMasks (zs : List (List Bool)) : List (List Bool) :=
  zs.flatMap (fun z => [false :: z, true :: z])
def masksCode : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => extendMasks (masksCode n)

/-- Exact syntactic zero restriction with one shared indexed boolean list.
Original variable names are retained; no renumbering or independent occurrence
choices are allowed. Out-of-range mask lookups default to false. -/
def restrictCode (z : List Bool) : Nat → Nat
  | e =>
    if e % 6 = 1 then
      if z.getD (e / 6) false then SeededInputCode.variableCode (e / 6)
      else SeededInputCode.zeroCode
    else if h : e % 6 = 2 ∨ e % 6 = 3 ∨ e % 6 = 4 then
      have hd : e / 6 < e := Nat.div_lt_self (by omega) (by decide)
      if e % 6 = 2 then
        have hl : (e / 6).unpair.1 < e := (Nat.unpair_left_le _).trans_lt hd
        have hr : (e / 6).unpair.2 < e := (Nat.unpair_right_le _).trans_lt hd
        SeededInputCode.addCode (restrictCode z (e / 6).unpair.1)
          (restrictCode z (e / 6).unpair.2)
      else if e % 6 = 3 then SeededInputCode.negateCode (restrictCode z (e / 6))
      else SeededInputCode.shiftCode (restrictCode z (e / 6))
    else 0
termination_by e => e
decreasing_by all_goals assumption

def restrictRows (z : List Bool) (rows : List Nat) : List Nat := rows.map (restrictCode z)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode
