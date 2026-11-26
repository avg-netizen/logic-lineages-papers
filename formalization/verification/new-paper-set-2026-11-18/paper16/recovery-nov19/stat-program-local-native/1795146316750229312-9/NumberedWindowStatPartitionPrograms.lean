module

public import LogicLineages.PersistentMarking.NumberedWindowStatMarkPrograms
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowDirectListsPrimrec

public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatPartitionPrograms
open NumberedWindowStatAlgorithm NumberedWindowStatMarkPrograms
open NumberedWindowPositivePathParserPrograms (fieldsPrim)
open NumberedWindowDirectListsPrimrec (allScalar)

private theorem termCodesPrim : Primrec termCodes :=
  (Primrec.option_bind₁
    (Primrec.ite (Primrec.eq.comp (allScalar (Primrec.fst.comp NumberedWindowSyntaxProgramProof.bits))
      (Primrec.const true)) Primrec.option_some (Primrec.const none))).comp fieldsPrim

theorem argsViewPrim : Primrec argsView :=
  Primrec.ite (Primrec.eq.comp (Primrec.snd.comp NumberedWindowSyntaxProgramProof.bits)
    (Primrec.const true)) fieldsPrim (Primrec.const none)

private def assemble (p : Node) : Option Partition :=
  if p.1 = 0 ∧ p.2.length = 3 then do
    let ks ← termCodes (p.2.getD 0 0)
    let rs ← termCodes (p.2.getD 1 0)
    let as ← termCodes (p.2.getD 2 0)
    pure (ks,rs,as)
  else none

private theorem assemblePrim : Primrec assemble := by
  have field (i : Nat) : Primrec (fun p : Node => termCodes (p.2.getD i 0)) :=
    termCodesPrim.comp ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const i))
  let State := (Node × List Nat) × List Nat
  have extra : Primrec (fun p : State => termCodes (p.1.1.2.getD 2 0)) :=
    (field 2).comp (Primrec.fst.comp Primrec.fst)
  have fields : Primrec (fun p : State × List Nat => (p.1.1.2,p.1.2,p.2)) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have next := Primrec.option_bind ((field 1).comp (Primrec.fst : Primrec (Prod.fst : Node × List Nat → Node)))
    (Primrec.option_map extra fields.to₂).to₂
  have shaped : PrimrecPred (fun p : Node => p.1 = 0 ∧ p.2.length = 3) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).and
      (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 3))
  apply (Primrec.ite shaped (Primrec.option_bind (field 0) next.to₂) (Primrec.const none)).of_eq
  rintro ⟨tag,fs⟩
  by_cases h : tag = 0 ∧ fs.length = 3
  · cases hk : termCodes (fs.getD 0 0) <;> cases hr : termCodes (fs.getD 1 0) <;>
      cases ha : termCodes (fs.getD 2 0) <;>
      simp only [assemble,h,if_true,Option.bind_eq_bind,hk,hr,ha,
        Option.bind_none,Option.bind_some,Option.map_none,Option.map_some,Option.pure_def]
  · simp [assemble,h]

theorem partitionPrim : Primrec readPartition := by
  apply ((Primrec.option_bind₁ assemblePrim).comp nodesPrim).of_eq
  intro n
  cases h : NumberedWindowFieldAlgorithm.unpackNode n with
  | none => simp [readPartition,h]
  | some p =>
    rcases p with ⟨tag,fs⟩
    rcases tag with _ | tag <;>
      rcases fs with _ | ⟨x,_ | ⟨y,_ | ⟨z,_ | ⟨v,tail⟩⟩⟩⟩ <;>
      simp [readPartition,h,assemble,List.getD_eq_getElem?_getD]

end LogicLineages.PersistentMarking.NumberedWindowStatPartitionPrograms
