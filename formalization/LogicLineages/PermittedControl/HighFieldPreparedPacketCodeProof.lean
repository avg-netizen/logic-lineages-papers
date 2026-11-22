module
public import LogicLineages.PermittedControl.HighFieldPreparedPacketTargets
import LogicLineages.PermittedControl.InverseComparisonPreparedRowsCodeProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.HighFieldPreparedPacket
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

private theorem reversePrimitive : Primrec reverseComparisonCode :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const 0) (Primrec.const 1))

theorem postprocessEffective : PostprocessEffective := by
  have orientation : Primrec (fun p : PostArgs => p.1.1) := Primrec.fst.comp Primrec.fst
  have raw : Primrec (fun p : PostArgs => p.1.2) := Primrec.snd.comp Primrec.fst
  have tag : Primrec (fun p : PostArgs => p.1.2.1) := Primrec.fst.comp raw
  have answer : Primrec (fun p : PostArgs => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp raw)
  have field : Primrec (fun p : PostArgs => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp raw)
  have rankF : Primrec (fun p : PostArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have rankG : Primrec (fun p : PostArgs => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have wanted : Primrec (fun p : PostArgs => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have forward : PrimrecPred (fun p : PostArgs => p.1.1 = 0) :=
    Primrec.eq.comp orientation (Primrec.const 0)
  have flipped : Primrec (fun p : PostArgs =>
      flipHighComparisonAnswer p.1.1 p.1.2.2.1) :=
    Primrec.ite forward answer (reversePrimitive.comp answer)
  have lower : Primrec (fun p : PostArgs => lowerRank p.1.1 p.2.1 p.2.2.1) :=
    Primrec.ite forward rankF rankG
  have sorted : Primrec (fun p : PostArgs => sortedWanted p.1.1 p.2.2.2) :=
    Primrec.ite forward wanted (reversePrimitive.comp wanted)
  have constant : Primrec (fun p : PostArgs =>
      (constantFormula p.1.1 p.1.2.2.1 p.2.2.2).encode) :=
    (Primrec.ite (Primrec.eq.comp flipped wanted) (Primrec.const NormalForm.Formula.truth.encode)
      (Primrec.const NormalForm.Formula.falsity.encode)).of_eq (fun p => show _ =
        (constantFormula p.1.1 p.1.2.2.1 p.2.2.2).encode from by
      unfold constantFormula
      split_ifs <;> rfl)
  have lowerCode : Primrec (fun p : PostArgs =>
      ((1,lowerRank p.1.1 p.2.1 p.2.2.1,p.1.2.2.2) : LowerOperandCode)) :=
    (Primrec.const 1).pair (lower.pair field)
  have table := Primrec.encode.comp (Primrec.list_cons.comp lowerCode (Primrec.const []))
  have linear := InverseComparisonPreparedRows.codeExact.1.comp answer sorted
  have compiled := Primrec.ite (Primrec.nat_le.comp wanted (Primrec.const 2))
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 0))
      ((Primrec.const (preparedTableBytes [])).pair constant) (table.pair linear))
    (Primrec.const (preparedPacketCode [] .falsity))
  exact compiled.of_eq (fun p => show _ = postprocess p from by
    rcases p with ⟨⟨o,t,c,H⟩,first,second,w⟩
    by_cases admitted : w ≤ 2 <;> by_cases isConstant : t = 0 <;>
      simp [postprocess,preparedPacketCode,admitted,isConstant])

end LogicLineages.PermittedControl.HighFieldPreparedPacket
