module
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode
open SourceAnnotationCode

/-- Literal whole-free-first ground partial on encoded annotation data.
trackedIndex refers to the INPUT context, before deleting ground slot zero. -/
def groundPartialCode (trackedIndex : Nat) : Nat → Option Nat
  | n =>
    if OrdinalSyntax.headFree (eraseCode trackedIndex n) then
      some (4*Nat.pair (closeCode n) 4+2)
    else if h0 : n%4=0 then
      (OrdinalSyntax.partialRun 0 0 (n/4)).map (fun v => 4*v.getD 0 0)
    else if h1 : n%4=1 then none
    else
      have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/4).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%4=2 then do
        let a ← groundPartialCode trackedIndex p.1
        let b ← groundPartialCode trackedIndex p.2
        pure (4*Nat.pair (4*Nat.pair a b+2) 4+2)
      else (groundPartialCode trackedIndex p.2).map (fun tail =>
        4*Nat.pair (closeOperatorCode p.1) tail+3)
termination_by n => n
decreasing_by all_goals assumption
end LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode
