module
public import LogicLineages.OrdinalComparison.SourceGammaRestrictedReductionDefinitions
public import Mathlib.Computability.Primrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker
def fragmentCode (n : Nat) : Bool :=
  if n%8=0 then true else if n=1 ∨ n=2 then true else
  if h : n%8=5 ∨ n%8=6 then
    have hn : 0<n := by omega
    have hd : n/8<n := Nat.div_lt_self hn (by decide)
    have hl : (n/8).unpair.1<n := (Nat.unpair_left_le _).trans_lt hd
    have hr : (n/8).unpair.2<n := (Nat.unpair_right_le _).trans_lt hd
    if n%8=5 then fragmentCode (n/8).unpair.1 && fragmentCode (n/8).unpair.2
    else decide ((n/8).unpair.1=SyntaxCode.typeCode Ty.ground) && fragmentCode (n/8).unpair.2
  else false
termination_by n
decreasing_by all_goals assumption

def groundCode (n code : Nat) : Bool := decide
  (SyntaxCode.check (List.replicate n (SyntaxCode.typeCode Ty.ground)) code=some (SyntaxCode.typeCode Ty.ground))
def restrictedCode (code : Nat) : Bool :=
  match SourceMachineQueryCode.unpack code with
  | none => false
  | some (n,left,right) => groundCode n left && groundCode n right && fragmentCode left && fragmentCode right
end LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker
