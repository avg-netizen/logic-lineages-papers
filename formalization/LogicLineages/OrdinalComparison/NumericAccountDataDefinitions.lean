module
public import LogicLineages.OrdinalComparison.NumericCarrierDataDefinitions
public import LogicLineages.OrdinalComparison.DeterministicAccountDataDefinitions
public import LogicLineages.OrdinalComparison.UnitHeadCodeDefinitions
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericAccountData

/-- Actual whole-free-first surplus, simultaneous with head freeness. -/
def surplusData (n : Nat) : Bool×Nat :=
  OrdinalSyntax.fold
    (fun k => (OrdinalSyntax.headLeafFree k, if OrdinalSyntax.headLeafFree k then 1 else 0))
    (fun tag a b => (a.1 && b.1, if a.1 && b.1 then 1 else if tag=4 then a.2+b.2+1 else 0)) n

def surplusCode (n : Nat) : Nat := (surplusData n).2

def recordCode {Γ} (r : DeterministicAccountData.UnaryRecord Γ) : Nat :=
  Nat.pair 0 (Nat.pair (SyntaxCode.encodeTerm r.source) (Encodable.encode (OrdinalSyntax.vectorCode r.vector)))

/-- Literal numeric accounting; only actual extraction failure yields none.
The free stop has priority over all recursive branch classification. -/
def accountCode (Γ : List Nat) : Nat → Option (List Nat×Nat)
  | n =>
    if OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 n) then some ([],1)
    else if n%4=0 then none
    else if n%4=1 then some ([],1)
    else if h : n%4=2 ∨ n%4=3 then
      have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/4).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%4=2 then do
        let (xs,c) ← accountCode Γ p.1
        let (ys,e) ← accountCode Γ p.2
        pure (xs++ys,c+e+1)
      else do
        let (_,finite,value) ← UnitHeadCode.classify (SourceAnnotationCode.operatorHead p.1)
        let (xs,c) ← accountCode Γ p.2
        if finite then pure (xs,c+value+surplusCode (SourceAnnotationCode.operatorHead p.1))
        else pure (xs++[NumericCarrierData.carrierCode Γ p.1],c+surplusCode (SourceAnnotationCode.operatorHead p.1))
    else none
termination_by n => n
decreasing_by all_goals assumption

/-- Canonical raw-source composition, not the ambiguous old Expr builder. -/
def sourceAccountCode (Γ : List Nat) (n : Nat) : Option (List Nat×List Nat×Nat) := do
  let (u,d) ← CanonicalAnnotationBuilderCode.buildCode Γ 0 n
  let (rs,c) ← accountCode Γ d
  pure (u,rs,c)
end LogicLineages.OrdinalComparison.Source.NumericAccountData
