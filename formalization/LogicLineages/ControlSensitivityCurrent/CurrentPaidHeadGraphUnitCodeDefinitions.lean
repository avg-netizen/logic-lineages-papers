module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixCodeDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitRawDefinitions
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
open LogicLineages.OrdinalComparison.Source
open AdmissibleSum CurrentPaidHeadGraph CurrentOneUnit
open RawSourceDAG (Code)
open MatrixCode

/-- An encoded current437 open graph: literal prefix width and quantifier-free
matrix over width, result, and the surviving shared ground names. -/
abbrev Block := Nat × Nat

def bitCtx (n : Nat) : List Nat := List.replicate n 0

def rawRow (row : LinearCode) (l l' r : Nat) : Nat :=
  eq (add (times row.1 l) (lit row.2.1))
    (add (add (times row.2.2.1 l') (times row.2.2.2.1 r)) (lit row.2.2.2.2))

def shiftEraser (d : Code) : Code :=
  RawSourceDAG.Operations.renameCode (0::d.1) (0::1::
    ((List.range (d.1.length-2)).map (fun i => i+3))) d

def originalEraser (d : Code) : Code :=
  shiftEraser (CurrentProbeCode.probeRaw (CurrentDecisionEmitter.liftCode 2 d) 0)

def closedEraser (d : Code) : Code :=
  shiftEraser (CurrentProbeCode.probeRaw
    (RawSourceDAG.Operations.renameCode (0::0::d.1) [] (CurrentProbeCode.closeRaw d)) 1)

noncomputable def groundBlock (p : Policy) (f : Nat → Nat) (d : Code) : Block :=
  let c := CurrentAbsolute.anchor p f d
  let D := 2*(SyntaxCode.typeLevel d.2.2.2+1)+1
  (2,both (eq (observe (originalEraser d)) (observe (closedEraser d)))
    (eq (add (times D (raw 2)) (raw 0)) (add (lit (D*c)) (raw 1))))

/-- Child result is reassigned to exactly the fresh wire at 0; the old
same ground slots remain in their original order after the new prefix. -/
def freeBlock (g : Nat) (row : LinearCode) (q : Block) : Block :=
  let width := q.1+1
  let table := (List.range (q.1+1+g)).map (fun i => if i=q.1 then 0 else i+1)
  let a := renameFormula (bitCtx (width+1+g)) table q.2
  (width,both a (rawRow row (raw 0) (lit 0) (raw width)))

/-- Child results are at 0 and 1; all old ground positions are shared,
not duplicated even when both subderivations contain them. -/
def activeBlock (g : Nat) (row : LinearCode) (q r : Block) : Block :=
  let width := q.1+r.1+2
  let ctx := bitCtx (width+1+g)
  let ltable := (List.range (q.1+1+g)).map (fun i =>
    if i<q.1 then i+2 else if i=q.1 then 0 else i+r.1+2)
  let rtable := (List.range (r.1+1+g)).map (fun i =>
    if i=r.1 then 1 else i+q.1+2)
  (width,both (both (renameFormula ctx ltable q.2) (renameFormula ctx rtable r.2))
    (rawRow row (raw 0) (raw 1) (raw width)))

/-- Same fuel, first original functional slot and literal selected policy
packets as typed 437. Each recursive child deletes that same actual slot. -/
noncomputable def blockFuel (p : Policy) (f : Nat → Nat) : Nat → List Nat → Nat → Option Block
  | 0,_,_ => none
  | k+1,Γ,src => do
    match UnitContextSelectionCode.selectCode Γ with
    | none =>
      let d ← CurrentTreeInputCoverage.compile Γ src
      pure (groundBlock p f d)
    | some (left,_,right) =>
      let packet ← compileSelected p (left.length,Γ,src)
      let q ← blockFuel p f k (left++right) packet.1
      match packet.2.1 with
      | none => pure (freeBlock (groundCount Γ) packet.2.2.2 q)
      | some second =>
        let r ← blockFuel p f k (left++right) second
        pure (activeBlock (groundCount Γ) packet.2.2.2 q r)

noncomputable def block (p : Policy) (f : Nat → Nat) (Γ : List Nat) (src : Nat) :=
  blockFuel p f (Γ.length+1) Γ src

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
