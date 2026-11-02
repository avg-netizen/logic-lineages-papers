module
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeDefinitions
public import LogicLineages.OrdinalComparison.WWUnaryCarrierDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode

/-- Protect all locally bound prefix slots, close exactly free ground slots
of Γ, and retain every free functional name with its actual identity. -/
def protectedMap (Θ Γ : List Ty) : GroundClosing.GroundMap (Θ++Γ) (Θ++Γ) :=
  match Θ with
  | [] => UnaryCarrier.groundMap Γ
  | _ :: Θ => GroundClosing.GroundMap.lift (protectedMap Θ Γ)

def variableCode (Γ : List Nat) (depth i : Nat) : Nat :=
  if i < depth then 8*i else if Γ.getD (i-depth) 1 = 0 then 1 else 8*i

/-- Out-of-range context lookup defaults to functional type code1; calibration
uses actual typed indices and proves that this default is never misused. -/
def sourceCode (Γ : List Nat) (depth : Nat) : Nat → Nat
  | n =>
    if n%8=0 then variableCode Γ depth (n/8)
    else if n%8=1 then 1
    else if n%8=2 then if n/8=0 then 2 else 1
    else if n%8=3 then n
    else if n%8=4 then n
    else if h : n%8=5 ∨ n%8=6 then
      have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then 8*Nat.pair (sourceCode Γ depth p.1) (sourceCode Γ depth p.2)+5
      else 8*Nat.pair p.1 (sourceCode Γ (depth+1) p.2)+6
    else 1
termination_by n => n
decreasing_by all_goals assumption

def ordinalLeaf (Γ : List Nat) (n : Nat) : Nat :=
  if n%8=3 then if Γ.getD (n/8).unpair.1 1 = 0 then 1 else n else n

def ordinalCode (Γ : List Nat) (n : Nat) : Nat :=
  OrdinalSyntax.fold (ordinalLeaf Γ) (fun tag a b => 8*Nat.pair a b+tag) n

def vectorCode (Γ : List Nat) (v : List Nat) : List Nat := v.map (ordinalCode Γ)
end LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode
