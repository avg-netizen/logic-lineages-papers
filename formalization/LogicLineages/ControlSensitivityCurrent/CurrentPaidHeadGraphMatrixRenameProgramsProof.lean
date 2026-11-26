module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixWidthProgramsProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode

open LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof (exactDecreasingGraph)
open CurrentGroundAnnotationPrograms (chooseProgram)
open RawSourceDAG (Code)

theorem tagPayloadProgram : Primrec₂ (fun (k n : Nat) => 8*n+k) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.snd) Primrec.fst

theorem atomProgram : Primrec (fun q : Nat×Nat×Nat => atom q.1 q.2.1 q.2.2) :=
  tagPayloadProgram.comp Primrec.fst (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd))

theorem varProgram : Primrec var := (Primrec.nat_mul.comp (Primrec.const 8) Primrec.id)
theorem litProgram : Primrec lit := tagPayloadProgram.comp (Primrec.const 1) Primrec.id
theorem addProgram : Primrec₂ add := atomProgram.comp ((Primrec.const 2).pair Primrec.id)
theorem observeProgram : Primrec observe := tagPayloadProgram.comp (Primrec.const 3) Primrec.encode
theorem unaryProgram : Primrec₂ unary := tagPayloadProgram.comp (Primrec.const 4)
  (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd)
theorem payloadProgram : Primrec payload := Primrec.option_getD.comp Primrec.decode (Primrec.const blank)

private abbrev R := List Nat × List Nat × Nat
private abbrev P := R × List Nat

def liftRenameChildren (children : Nat → List Nat)
    (q : List Nat × List Nat × Nat) : List (List Nat × List Nat × Nat) :=
  (children q.2.2).map (fun n => (q.1,q.2.1,n))

private theorem liftProgram {children : Nat → List Nat} (h : Primrec children) :
    Primrec (liftRenameChildren children) := by
  have g : Primrec (fun q : R => q.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_map (h.comp g) ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to₂

private theorem decreases {children : Nat → List Nat}
    (h : ∀ s t, t∈children s → t<s) (q z : R) (hz : z∈liftRenameChildren children q) : z.2.2<q.2.2 := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
  exact h _ _ hx

private def assembleTerm (q : R) (cs : List Nat) : Nat :=
  let n := q.2.2/8
  let k := q.2.2%8
  if k=0 then var (q.2.1.getD n 0)
  else if k=2 then add (cs.getD 0 0) (cs.getD 1 0)
  else if k=4 then unary (payload n.unpair.1) (cs.getD 0 0)
  else if k=3 then observe (RawSourceDAG.Operations.renameCode q.1 q.2.1 (payload n))
  else lit n

private theorem termParts : Primrec₂ assembleTerm := by
  have ctx : Primrec (fun q : P => q.1.1) := Primrec.fst.comp Primrec.fst
  have tab : Primrec (fun q : P => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have code : Primrec (fun q : P => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have cs (i : Nat) : Primrec (fun q : P => q.2.getD i 0) := (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)
  have n := digitProgram.comp code
  have left := leftProgram.comp code
  have ob := observeProgram.comp (RawSourceDAG.Operations.primitive.2.2.2.comp
    (ctx.pair (tab.pair (payloadProgram.comp n))))
  exact Primrec.ite ((isTag 0).comp code) (varProgram.comp ((Primrec.list_getD 0).comp tab n))
    (Primrec.ite ((isTag 2).comp code) (addProgram.comp (cs 0) (cs 1))
      (Primrec.ite ((isTag 4).comp code) (unaryProgram.comp (payloadProgram.comp left) (cs 0))
        (Primrec.ite ((isTag 3).comp code) ob (litProgram.comp n))))

private theorem eqTerm (q : R) : renameTerm q.1 q.2.1 q.2.2 =
    assembleTerm q ((liftRenameChildren childTerm q).map (fun s => renameTerm s.1 s.2.1 s.2.2)) := by
  rw [renameTerm]
  by_cases h0 : q.2.2%8=0 <;> by_cases h2 : q.2.2%8=2 <;> by_cases h4 : q.2.2%8=4 <;>
    by_cases h3 : q.2.2%8=3 <;> simp [assembleTerm,liftRenameChildren,childTerm,h0,h2,h3,h4]

theorem renameTermProgram : Computable (fun q : List Nat×List Nat×Nat => renameTerm q.1 q.2.1 q.2.2) :=
  (exactDecreasingGraph R Nat (liftRenameChildren childTerm) assembleTerm (fun q => q.2.2)
    (liftProgram termChildProgram).to_comp termParts.to_comp (Computable.snd.comp Computable.snd) _
    (decreases termChildDecrease) eqTerm).2

private def assembleFormula (q : R) (cs : List Nat) : Nat :=
  let n := q.2.2/8
  let k := q.2.2%8
  if 5≤k then
    if k=5 then neg (cs.getD 0 0) else atom k (cs.getD 0 0) (cs.getD 1 0)
  else if 2≤k then atom k (renameTerm q.1 q.2.1 n.unpair.1) (renameTerm q.1 q.2.1 n.unpair.2)
  else k

private theorem formulaParts : Computable₂ assembleFormula := by
  have ctx : Primrec (fun q : P => q.1.1) := Primrec.fst.comp Primrec.fst
  have tab : Primrec (fun q : P => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have code : Primrec (fun q : P => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have cs (i : Nat) : Primrec (fun q : P => q.2.getD i 0) := (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)
  have k := tagProgram.comp code
  have hren {f : Nat → Nat} (hf : Primrec f) :
      Computable (fun q : P => renameTerm q.1.1 q.1.2.1 (f q.1.2.2)) :=
    renameTermProgram.comp (ctx.pair (tab.pair (hf.comp code))).to_comp
  have l := hren leftProgram
  have r := hren rightProgram
  exact chooseProgram ((clusteredTag).comp code)
    (chooseProgram ((isTag 5).comp code) (tagPayloadProgram.comp (Primrec.const 5) (cs 0)).to_comp
      (atomProgram.comp (k.pair ((cs 0).pair (cs 1)))).to_comp)
    (chooseProgram (Primrec.nat_le.comp (Primrec.const 2) k)
      (atomProgram.to_comp.comp (k.to_comp.pair (l.pair r))) k.to_comp)

private theorem eqForm (q : R) : renameFormula q.1 q.2.1 q.2.2 =
    assembleFormula q ((liftRenameChildren childFormula q).map (fun s => renameFormula s.1 s.2.1 s.2.2)) := by
  rw [renameFormula]
  by_cases h : 5≤q.2.2%8 <;> by_cases h5 : q.2.2%8=5 <;>
    simp [assembleFormula,liftRenameChildren,childFormula,h,h5]

theorem renameFormulaProgram : Computable (fun q : List Nat×List Nat×Nat => renameFormula q.1 q.2.1 q.2.2) :=
  (exactDecreasingGraph R Nat (liftRenameChildren childFormula) assembleFormula (fun q => q.2.2)
    (liftProgram formulaChildProgram).to_comp formulaParts (Computable.snd.comp Computable.snd) _
    (decreases formulaChildDecrease) eqForm).2

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
