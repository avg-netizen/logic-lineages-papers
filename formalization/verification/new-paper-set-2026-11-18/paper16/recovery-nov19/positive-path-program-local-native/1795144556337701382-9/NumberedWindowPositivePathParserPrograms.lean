module

public import LogicLineages.PersistentMarking.NumberedWindowPositivePathProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
open LogicLineages.ComputabilityKnowledge NumberedWindowPositivePathAlgorithm
open NumberedWindowFieldAlgorithm (unpack unpackNode)

theorem fieldsPrim : Primrec unpack := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.2)

private theorem nodesPrim : Primrec unpackNode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

theorem equalPrim {α} [Primcodable α] [BEq α] [LawfulBEq α] [DecidableEq α] :
    Primrec₂ (fun (a b : α) => a == b) := by
  apply ((Primrec.eq : PrimrecRel (Eq : α → α → Prop)).decide).of_eq
  intro a b
  apply Bool.eq_iff_iff.mpr
  simp

abbrev Node := Nat × List Nat

private theorem slot (i : Nat) : Primrec (fun p : Node => p.2.getD i 0) :=
  (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)

private theorem shape (tag arity : Nat) :
    PrimrecPred (fun p : Node => p.1 = tag ∧ p.2.length = arity) :=
  (Primrec.eq.comp Primrec.fst (Primrec.const tag)).and
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const arity))

private def edgeParts (p : Node) : Option RawEdge :=
  if p.1 = 1 ∧ p.2.length = 3 then some (p.2.getD 0 0,p.2.getD 2 0,p.2.getD 1 0)
  else none

private theorem edgePartsPrim : Primrec edgeParts :=
  Primrec.ite (shape 1 3) (Primrec.option_some.comp ((slot 0).pair ((slot 2).pair (slot 1))))
    (Primrec.const none)

theorem edgePrim : Primrec edgeView := by
  apply ((Primrec.option_bind₁ edgePartsPrim).comp nodesPrim).of_eq
  intro n
  cases h : unpackNode n with
  | none => simp [edgeView,h]
  | some row =>
    rcases row with ⟨tag,fs⟩
    rcases tag with _ | _ | tag <;>
      rcases fs with _ | ⟨q,_ | ⟨r,_ | ⟨w,_ | ⟨x,tail⟩⟩⟩⟩ <;>
      simp [edgeView,h,edgeParts,List.getD_eq_getElem?_getD]

private def hopParts (p : Node) : Option ClassHop :=
  if p.1 = 2 ∧ p.2.length = 2 then (edgeView (p.2.getD 1 0)).map (fun row => (p.2.getD 0 0,row))
  else none

private theorem hopPartsPrim : Primrec hopParts :=
  Primrec.ite (shape 2 2)
    (Primrec.option_map (edgePrim.comp (slot 1)) (((slot 0).comp Primrec.fst).pair Primrec.snd).to₂)
    (Primrec.const none)

theorem hopPrim : Primrec hopView := by
  apply ((Primrec.option_bind₁ hopPartsPrim).comp nodesPrim).of_eq
  intro n
  cases h : unpackNode n with
  | none => simp [hopView,h]
  | some row =>
    rcases row with ⟨tag,fs⟩
    rcases tag with _ | _ | _ | tag <;>
      rcases fs with _ | ⟨c,_ | ⟨e,_ | ⟨x,tail⟩⟩⟩ <;>
      simp [hopView,h,hopParts,List.getD_eq_getElem?_getD]
    cases edgeView e <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
