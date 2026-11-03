module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedKeyDefinitions
public import LogicLineages.OrdinalComparison.RawNotationCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection

/-- A key records the ACTUAL normal head code and the COMPLETE shared-basis input. -/
noncomputable def key (basis : List Nat) (a : Atom) : Nat :=
  Nat.pair (rawNoteEncode a.head.1) (input basis a)

noncomputable def keys (basis : List Nat) (row : Row) : List Nat :=
  (row.atoms.map (fun a => key basis a.2)).dedup

noncomputable def blockCoefficient (basis : List Nat) (row : Row) (k : Nat) : Int :=
  (row.atoms.map (fun a => if key basis a.2=k then a.1 else 0)).sum

/-- First literal original representative; no new atom or independent basis value. -/
noncomputable def representative (basis : List Nat) (row : Row) (k : Nat) : Option Atom :=
  (row.atoms.find? (fun a => key basis a.2=k)).map Prod.snd

noncomputable def collect (basis : List Nat) (row : Row) : Row :=
  { constant := row.constant
    remainder := row.remainder
    atoms := (keys basis row).filterMap (fun k =>
      let c := blockCoefficient basis row k
      if c=0 then none else (representative basis row k).map (fun a => (c,a))) }
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection
