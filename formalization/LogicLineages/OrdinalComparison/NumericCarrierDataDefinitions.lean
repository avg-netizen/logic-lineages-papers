module
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeDefinitions
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericCarrierData

/-- Keep tracked slot zero; insert the fresh functional slot immediately after it.
Every component coordinate is retained. -/
def freshLeaf (n : Nat) : Nat :=
  if n%8=3 then
    let p := (n/8).unpair
    8*Nat.pair (if p.1=0 then 0 else p.1+1) p.2+3
  else n

def freshOrdinal (n : Nat) : Nat :=
  OrdinalSyntax.fold freshLeaf (fun tag a b => 8*Nat.pair a b+tag) n

def freshVector (v : List Nat) : List Nat := v.map freshOrdinal

/-- Literal repeated applications to source zero, not a head surrogate. -/
def saturateSource : Nat → Nat → Nat
  | 0,n => n
  | r+1,n => saturateSource r (8*Nat.pair n 1+5)

/-- Every intermediate result is still functional (level one). Source zero's
actual assigned vector is [one], and no scalar field is replaced. -/
def saturateVector : Nat → List Nat → List Nat
  | 0,v => v
  | r+1,v => saturateVector r (OrdinalSyntax.defaultApplicationCode 1 0 v [1])

def carrierCode (Γ : List Nat) (op : Nat) : Nat :=
  let Δ := Γ.getD 0 0 :: Γ
  let r := SourceAnnotationCode.operatorArity op
  let src := GroundCaptureClosingCode.sourceCode Δ 0
    (saturateSource r (SourceCarrierMapCode.mapCode true 0 (SourceAnnotationCode.operatorSource op)))
  let vec := GroundCaptureClosingCode.vectorCode Δ
    (saturateVector r (freshVector (SourceAnnotationCode.operatorVector op)))
  Nat.pair 0 (Nat.pair src (Encodable.encode vec))
end LogicLineages.OrdinalComparison.Source.NumericCarrierData
