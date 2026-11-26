module

public import LogicLineages.PersistentMarking.NumberedWindowShiftProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms

public section
namespace LogicLineages.PersistentMarking.NumberedWindowShiftStepPrograms
open NumberedWindowShiftAlgorithm
open NumberedWindowMarkRootProgramProof (nodePrim readPrim)
open NumberedWindowHeadDeclarationPrograms (choose arrowPrim)
open NumberedWindowSyntaxShapePrograms (pairs)

theorem earlierPrim : Primrec (fun p : Table × Nat × Nat => earlier p.1 p.2.1 p.2.2) :=
  (Primrec.list_getD (0,0)).comp
    ((Primrec.list_getD ([] : List Row)).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

abbrev Env := Nat × Nat × Nat × Table
abbrev Node := Nat × List Nat

theorem termPartsPrim : Primrec (fun p : Env × Node =>
    termParts p.1.2.2.2 p.1.1 p.1.2.1 p.1.2.2.1 p.2.1 p.2.2) := by
  let P := Env × Node
  have fs : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have tag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  let value (i : Nat) := (Primrec.list_getD 0).comp fs (Primrec.const i)
  have tab : Primrec (fun p : P => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have amount : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have cutoff : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have offset : Primrec (fun p : P => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let row (i : Nat) := earlierPrim.comp (tab.pair ((value i).pair offset))
  let tm (i : Nat) := Primrec.fst.comp (row i)
  let ar (i : Nat) := Primrec.snd.comp (row i)
  let nil : Primrec (fun (_ : P) => ([] : List Nat)) := Primrec.const []
  let mk (k : Nat) {f : P → List Nat} (h : Primrec f) := nodePrim.comp (Primrec.const k) h
  let boundValue := Primrec.ite (Primrec.nat_lt.comp (value 1) (Primrec.nat_add.comp cutoff offset))
    (value 1) (Primrec.nat_add.comp (value 1) amount)
  let boundNode := mk 1 (Primrec.list_cons.comp (value 0) (Primrec.list_cons.comp boundValue nil))
  let body := Primrec.fst.comp (earlierPrim.comp (tab.pair ((value 1).pair (Primrec.succ.comp offset))))
  let lam := mk 2 (Primrec.list_cons.comp (value 0) (Primrec.list_cons.comp body nil))
  let ord := mk 4 (Primrec.list_cons.comp (value 0) (Primrec.list_cons.comp (ar 1) nil))
  let num := mk 5 (Primrec.list_cons.comp (value 0) (Primrec.list_cons.comp (value 1)
    (Primrec.list_cons.comp (value 2) (Primrec.list_cons.comp (ar 3) (Primrec.list_cons.comp (ar 4) nil)))))
  let aux := mk 6 (Primrec.list_cons.comp (value 0) (Primrec.list_cons.comp (value 1)
    (Primrec.list_cons.comp (tm 2) (Primrec.list_cons.comp (tm 3) nil))))
  apply (choose tag 0 (mk 0 fs) (choose tag 1 boundNode (choose tag 2 lam (choose tag 3 (mk 3 fs)
    (choose tag 4 ord (choose tag 5 num (choose tag 6 aux (Primrec.const 0)))))))).of_eq
  rintro ⟨⟨a,c,d,table⟩,tag,fs⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | n <;> rfl

abbrev StepInput := Nat × Nat × Nat × Nat × Table

theorem termNextPrim : Primrec (fun p : StepInput => termNext p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let E := StepInput × Node
  have amt : Primrec (fun p : E => p.1.1) := Primrec.fst.comp Primrec.fst
  have cut : Primrec (fun p : E => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have off : Primrec (fun p : E => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have tab : Primrec (fun p : E => p.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have env := amt.pair (cut.pair (off.pair tab))
  have code : Primrec (fun p : StepInput => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_getD.comp (Primrec.option_map (readPrim.comp code)
    (termPartsPrim.comp (env.pair Primrec.snd)).to₂) (Primrec.const 0)

theorem argsNextPrim : Primrec (fun p : Nat × Nat × Table => argsNext p.1 p.2.1 p.2.2) := by
  let P := (Nat × Nat × Table) × Nat
  let E := P × Nat × Nat
  have off : Primrec (fun p : E => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have tab : Primrec (fun p : E => p.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have q : Primrec (fun p : E => p.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun p : E => p.2.2) := Primrec.snd.comp Primrec.snd
  have qm := Primrec.fst.comp (earlierPrim.comp (tab.pair (q.pair off)))
  have rm := Primrec.snd.comp (earlierPrim.comp (tab.pair (r.pair off)))
  have tail := Primrec.option_getD.comp (Primrec.option_map (pairs.comp (Primrec.snd : Primrec (Prod.snd : P → Nat)))
    (arrowPrim.comp qm rm).to₂) (Primrec.const 0)
  apply (Primrec.nat_casesOn (Primrec.fst.comp Primrec.snd) (Primrec.const 0) tail.to₂).of_eq
  rintro ⟨d,n,t⟩
  cases n <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowShiftStepPrograms
