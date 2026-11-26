module
public import LogicLineages.PermittedControl.MixedRankNamedResidueRowTargets
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankNamedResidueRow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open RankResidueChoices (Cell Digit)

private theorem atomCodePrimitive : Primrec (fun p : Nat × Nat × Nat => atomCode p.1 p.2.1 p.2.2) := by
  let Input := Nat × Nat × Nat
  have m : Primrec (fun p : Input => p.1) := Primrec.fst
  have name : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have j : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have modulus := Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) m) (Primrec.const 1)
  have offset := negate_primitive.comp (ofNat_primitive.comp j)
  have variableData : Primrec (fun p : Input => (0,p.2.1,0,0)) :=
    (Primrec.const 0).pair (name.pair (Primrec.const (0,0)))
  have term := (Primrec.const (1 : Int)).pair variableData
  have terms := Primrec.list_cons.comp term (Primrec.const [])
  have atomData : Primrec (fun p : Input =>
      ((1,2*p.1-1,-(p.2.2 : Int),[(1,(0,p.2.1,0,0))]) : NormalForm.Code.AtomData)) :=
    (Primrec.const 1).pair (modulus.pair (offset.pair terms))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.encode.comp atomData)) (Primrec.const 2)

private theorem atomCodeLiteral (m name j : Nat) : atomCode m name j = (atom m name j).encode := rfl

theorem clauseCodePrimitive : Primrec₂ clauseCode := by
  let Input := Nat × Cell
  let Step := Input × (Digit × Nat)
  have m : Primrec (fun p : Step => p.1.1) := Primrec.fst.comp Primrec.fst
  have digit : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have name : Primrec (fun p : Step => p.2.1.1) := Primrec.fst.comp digit
  have residue : Primrec (fun p : Step => p.2.1.2.2) := Primrec.snd.comp (Primrec.snd.comp digit)
  have tail : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have head := atomCodePrimitive.comp (m.pair (name.pair residue))
  have clausePair := Primrec₂.natPair.comp head tail
  have cons := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) clausePair) (Primrec.const 4)
  exact (Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : Input → Cell))
    (Primrec.const 0) cons.to₂).to₂

theorem clauseCodeLiteral (m : Nat) (cell : Cell) : clauseCode m cell = (clause m cell).encode := by
  induction cell with
  | nil => rfl
  | cons e tail ih =>
    change 6 * Nat.pair (atomCode m e.1 e.2.2) (clauseCode m tail) + 4 =
      6 * Nat.pair (atom m e.1 e.2.2).encode (clause m tail).encode + 4
    rw [atomCodeLiteral,ih]

end LogicLineages.PermittedControl.MixedRankNamedResidueRow
