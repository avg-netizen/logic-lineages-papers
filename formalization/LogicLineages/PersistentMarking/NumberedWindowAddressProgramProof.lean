module

public import LogicLineages.PersistentMarking.NumberedWindowAddressProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowProgramKernelChecks
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowDirectListsPrimrec
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
open LogicLineages.ComputabilityKnowledge List.Vector NumberedWindowAddressProgramTargets
open NumberedWindowAddressAlgorithm NumberedWindowFieldAlgorithm

private theorem pairs : Primrec NumberedWindowPairAlgorithm.decode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowProgramKernelChecks.completeDecoding)

private theorem nextPrim : Primrec₂ nextType := by
  let test (p : List Bool × Nat) :=
    ((NumberedWindowPairAlgorithm.decode p.2).map (fun ab => p.1.getD ab.1 false && p.1.getD ab.2 false)).getD false
  have left : Primrec (fun p : (List Bool × Nat) × Nat × Nat => p.1.1.getD p.2.1 false) :=
    (Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have right : Primrec (fun p : (List Bool × Nat) × Nat × Nat => p.1.1.getD p.2.2 false) :=
    (Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have ht : Primrec test := Primrec.option_getD.comp (Primrec.option_map (pairs.comp Primrec.snd)
    (Primrec.and.comp left right).to₂) (Primrec.const false)
  apply (Primrec.nat_casesOn Primrec.fst (Primrec.const true)
    (ht.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
  rintro ⟨n,table⟩
  cases n with
  | zero => rfl
  | succ k => cases h : NumberedWindowPairAlgorithm.decode k <;> simp [test, nextType, h]

theorem validType : Primrec typeBit := by
  have step : Primrec₂ (fun n (table : List Bool) => table ++ [nextType n table]) :=
    Primrec.list_append.comp Primrec.snd
      (Primrec.list_cons.comp nextPrim (Primrec.const []))
  have table : Primrec typeTable := (Primrec.nat_rec₁ [] step).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ k ih => simp [typeTable,ih])
  exact nextPrim.comp Primrec.id table

private theorem fields : Primrec unpack := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.2)
private theorem nodes : Primrec unpackNode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

theorem contextPrim : Primrec contextView := by
  have keep : Primrec (fun xs : List Nat => if xs.all typeBit then some xs else none) :=
    Primrec.ite (Primrec.eq.comp (NumberedWindowDirectListsPrimrec.allScalar validType) (Primrec.const true))
      Primrec.option_some (Primrec.const none)
  exact (Primrec.option_bind₁ keep).comp fields

private def body (p : Nat × List Nat) : Option Address :=
  let t := p.2.getD 1 0
  if p.1 = 3 ∧ p.2.length = 3 ∧ typeBit t = true then
    (contextView (p.2.getD 0 0)).map (fun xs => (xs,t,p.2.getD 2 0))
  else none

private theorem bodyPrim : Primrec body := by
  have atSlot (i : Nat) : Primrec (fun p : Nat × List Nat => p.2.getD i 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)
  have good := (Primrec.eq.comp Primrec.fst (Primrec.const 3)).and
    ((Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 3)).and
      (Primrec.eq.comp (validType.comp (atSlot 1)) (Primrec.const true)))
  exact Primrec.ite good (Primrec.option_map (contextPrim.comp (atSlot 0))
    (Primrec.snd.pair (((atSlot 1).comp Primrec.fst).pair ((atSlot 2).comp Primrec.fst))).to₂) (Primrec.const none)

theorem addressPrim : Primrec addressView := by
  apply ((Primrec.option_bind₁ bodyPrim).comp nodes).of_eq
  intro n
  cases h : unpackNode n with
  | none => simp [addressView,h]
  | some p =>
    obtain ⟨tag,xs⟩ := p
    simp only [addressView,h,Option.bind_eq_bind,Option.bind_some]
    by_cases ht : tag = 3
    · subst tag
      rcases xs with _ | ⟨c,xs⟩
      · simp [body]
      rcases xs with _ | ⟨t,xs⟩
      · simp [body]
      rcases xs with _ | ⟨k,xs⟩
      · simp [body]
      cases xs with
      | cons => simp [body]
      | nil =>
        cases hc : contextView c <;> cases hv : typeBit t <;> simp [body, hc, hv, List.getD_eq_getElem?_getD]
    · simp only [body, ht, false_and, if_false]
      split <;> grind

theorem typeProgram : TypeCodeProgram := (GorbowPRProgram.Proof.unaryCorrespondence _).mp
  ((Primrec.cond validType (Primrec.const 1) (Primrec.const 0)).of_eq
    (fun n => by cases h : typeBit n <;> simp [h]))
theorem contextProgram : ContextCodeProgram := (GorbowPRProgram.Proof.unaryCorrespondence _).mp
  (Primrec.encode.comp contextPrim)
theorem addressProgram : AddressCodeProgram := (GorbowPRProgram.Proof.unaryCorrespondence _).mp
  (Primrec.encode.comp addressPrim)
end LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
