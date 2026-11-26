module

public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowStatPartitionPrograms
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRootDispatchStepPrograms
open NumberedWindowRootDispatchAlgorithm NumberedWindowRootDispatchProgramTargets
open NumberedWindowHeadDeclarationPrograms (choose)
open NumberedWindowSyntaxShapePrograms (anyOption)

abbrev PartsInput := (Nat × Nat) × Nat × List Nat

private theorem flagPrim : Primrec flagView := by
  let next := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const (some true)) (Primrec.const none)
  apply (Primrec.nat_casesOn₁ (some false) next).of_eq
  intro n
  rcases n with _ | _ | n <;> rfl

private theorem field (i : Nat) : Primrec (fun p : PartsInput => p.2.2.getD i 0) :=
  (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) (Primrec.const i)

private theorem selectionPrim {rules : Rules} (hr : PrimitiveRules rules) :
    Primrec (fun p : PartsInput => (flagView (p.2.2.getD 0 0)).any (fun extra =>
      (NumberedWindowAddressAlgorithm.contextView (p.2.2.getD 2 0)).any (fun domains =>
        rules.select extra (p.2.2.getD 1 0) domains p.1.1 p.1.2))) := by
  let P := PartsInput × Bool
  let E := P × List Nat
  have dom : Primrec (fun p : P => NumberedWindowAddressAlgorithm.contextView (p.1.2.2.getD 2 0)) :=
    NumberedWindowAddressProgramProof.contextPrim.comp ((field 2).comp Primrec.fst)
  have flag : Primrec (fun p : E => p.1.2) := Primrec.snd.comp Primrec.fst
  have num : Primrec (fun p : E => p.1.1.2.2.getD 1 0) :=
    (field 1).comp (Primrec.fst.comp Primrec.fst)
  have endpoints : Primrec (fun p : E => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have test := hr.select.comp (flag.pair (num.pair (Primrec.snd.pair endpoints)))
  exact anyOption (flagPrim.comp (field 0)) (anyOption dom test.to₂).to₂

theorem partsPrim {rules : Rules} (hr : PrimitiveRules rules) :
    Primrec (fun p : PartsInput => parts rules p.1.1 p.1.2 p.2.1 p.2.2) := by
  have endpoints : Primrec (Prod.fst : PartsInput → Nat × Nat) := Primrec.fst
  have tag : Primrec (fun p : PartsInput => p.2.1) := Primrec.fst.comp Primrec.snd
  have len : Primrec (fun p : PartsInput => p.2.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  let arity (n : Nat) {f : PartsInput → Bool} (h : Primrec f) :=
    Primrec.ite (Primrec.eq.comp len (Primrec.const n)) h (Primrec.const false)
  let packed := (field 0).pair endpoints
  have mark := arity 1 (hr.mark.comp packed)
  have lower := arity 0 (hr.lower.comp (Primrec.fst.comp endpoints) (Primrec.snd.comp endpoints))
  have select := arity 3 (selectionPrim hr)
  have copy := arity 0 (hr.copy.comp (Primrec.fst.comp endpoints) (Primrec.snd.comp endpoints))
  have stat := arity 1 (Primrec.and.comp
    (Primrec.option_isSome.comp (NumberedWindowStatPartitionPrograms.partitionPrim.comp (field 0)))
    (hr.stat.comp packed))
  have fabs := arity 0 (hr.fabs.comp (Primrec.fst.comp endpoints) (Primrec.snd.comp endpoints))
  have beta := arity 0 (hr.beta.comp (Primrec.fst.comp endpoints) (Primrec.snd.comp endpoints))
  have bottom := arity 0 (hr.bottom.comp (Primrec.fst.comp endpoints) (Primrec.snd.comp endpoints))
  apply (choose tag 0 mark (choose tag 1 lower (choose tag 2 select (choose tag 3 copy
    (choose tag 4 stat (choose tag 5 fabs (choose tag 6 beta
      (choose tag 7 bottom (Primrec.const false))))))))).of_eq
  rintro ⟨⟨q,r⟩,tag,fs⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    rcases fs with _ | ⟨k,_ | ⟨i,_ | ⟨dom,_ | ⟨extra,tail⟩⟩⟩⟩ <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowRootDispatchStepPrograms
