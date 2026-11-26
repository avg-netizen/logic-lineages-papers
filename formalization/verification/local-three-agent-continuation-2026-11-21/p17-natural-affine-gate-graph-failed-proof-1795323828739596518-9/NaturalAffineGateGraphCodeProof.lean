module
public import LogicLineages.PermittedControl.NaturalAffineGateGraphTargets
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.NaturalAffineGateGraph
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof

private abbrev WeightedCode := Int × NormalForm.Code.ItemData

private theorem variablePrimitive : Primrec (fun n : Nat => ((0,n,0,0) : NormalForm.Code.ItemData)) :=
  (Primrec.const 0).pair (Primrec.id.pair (Primrec.const (0,0)))

private theorem atomPrimitive : Primrec₂ (fun (c : Int) (terms : List WeightedCode) =>
    6 * Encodable.encode ((0,0,c,terms) : NormalForm.Code.AtomData) + 2) := by
  let Args := Int × List WeightedCode
  have data : Primrec (fun p : Args => ((0,0,p.1,p.2) : NormalForm.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.encode.comp data)) (Primrec.const 2)

private theorem graphPrimitive : Primrec₂ graphCode := by
  let Args := Nat × Expression
  let Map := Args × Input
  have name : Primrec (Prod.fst : Args → Nat) := Primrec.fst
  have c : Primrec (fun p : Args => p.2.1) := Primrec.fst.comp Primrec.snd
  have terms : Primrec (fun p : Args => p.2.2) := Primrec.snd.comp Primrec.snd
  have occurrence : Primrec (Prod.snd : Map → Input) := Primrec.snd
  have coefficient := Primrec.fst.comp occurrence
  have varCode := variablePrimitive.comp (Primrec.snd.comp occurrence)
  have lowTerms := Primrec.list_map terms (coefficient.pair varCode).to₂
  have highTerms := Primrec.list_map terms ((negate_primitive.comp coefficient).pair varCode).to₂
  have outCode := variablePrimitive.comp name
  have lows := Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair outCode) lowTerms
  have highs := Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair outCode) highTerms
  have lower := atomPrimitive.comp c lows
  have upper := atomPrimitive.comp (negate_primitive.comp c) highs
  have pair := Primrec₂.natPair.comp lower upper
  have result := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) pair) (Primrec.const 4)
  exact (result.of_eq (fun p : Args => show _ = graphCode p.1 p.2 from rfl)).to₂

theorem codeExact : CodeExact := by
  refine ⟨graphPrimitive,?_⟩
  intro output e
  simp only [graphCode,graph,lowerData,upperData,lowerRow,upperRow,NormalForm.Formula.encode,
    NormalForm.Atom.data,NormalForm.rowData,List.map_cons,List.map_map,Function.comp_apply,
    NormalForm.Summand.data]

end LogicLineages.PermittedControl.NaturalAffineGateGraph
