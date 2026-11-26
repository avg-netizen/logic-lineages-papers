"""Recover previously independently reviewed exact paper19 proof-only bytes."""
from pathlib import Path
import hashlib, json, subprocess, sys, tempfile, difflib
D=Path("verification/new-paper-set-2026-11-18/paper19")
N=Path("LogicLineages/ControlSensitivityCurrent")
P="CURRENT-PAID-HEAD-GRAPH"
A="CurrentPaidHeadGraph"
ordered=[]
def add(tag, file, prev, result, diff, receipt, man, presha, aftersha, replacements=None):
    ordered.append(locals())
def digest(data):
    return hashlib.sha256(data).hexdigest()
def compute_text(old,replacements):
    for src,dst in replacements:
        assert old.count(src)==1,(src,old.count(src))
        old=old.replace(src,dst)
    return old
add('INSERTED-FIBER-SLOTS','InsertedFiberProof',
    'a6e2a44aa0309b200c357a99c33bf75b17132c7e7ecaecee3163448a5da751a2',
    'd36821fe4e967b8531b2897d7853d733a69860427d62da49efcccae77354236d',
    '8e3e1dbc6338e45b92286c2af6de46fa909803600bfc002a3402927923ac8388',
    '1795099727687182952-6','', 'ade8ad0a9d62c30a4838a8addcc8e2bf1240b9d26e9dee007fb5df8ef235132c',
    '2d14304658e8ab666e64f990d2f81ae918033fd74f473cdfef275705c1a9578d')
add('UNIT-BUILD-SELECTED-LITERAL','UnitBuildCodeProof',
    'bcbf0d09a612831a067a55162cfa7aaaf45bc9c9bf5c36a271d70e0f3e657fc0',
    '1299548ee9bc42d7216e59eb372ad2330ade589654395879907712d23a432e30',
    '2eea7e62ac48931bdbf141dd206efe5ee721fb21da97c87b1749d454c4169e1f',
    '1795099793288477045-6','-UNIT-CODE','f8b6877a2e9b0b819588657ba774305130bcbdd0398f38a98e4e444659651c76',
    '0d33c15859479bd285edf36fd0c1f71badc467d06c9d131984ab26b15642d613',
    [['      simp only [UnitContextSelectionCode.selectionCode,CurrentUnitElimination.step,hc,hd,bind,\n        Option.bind_some,pure,literalPacket,hg]',
      '''      have hc' : compileSelected p (left.length,(left++σ::right).map SyntaxCode.typeCode,
          SyntaxCode.encodeTerm a)=some (literalPacket b d) := hc
      simp only [UnitContextSelectionCode.selectionCode,CurrentUnitElimination.step,List.length_map,bind]
      change (compileSelected p (left.length,(left++σ::right).map SyntaxCode.typeCode,
          SyntaxCode.encodeTerm a)).bind _ =
        Option.map (Targets.codeUnitRender p f) ((typedCoefficients p b).bind _)
      rw [hc',hd]
      simp only [Option.bind_some,pure,literalPacket,hg]''']])
add('INSERTED-LITERAL-TAPE','InsertedProof',
    '7ffadea8f92b62003bbedad2e03914ec482c28e7648b97fa875b146ebc9a66ae',
    '9b29c23c928a70d55b322f8f806bf5e4216bd00730db70cdbeb560636732f816',
    'e5aed09cf469752ef535da94ee0c522c78fc092031b457e742ee4c88dc6ee23f',
    '1795099953830006877-6','', '2d14304658e8ab666e64f990d2f81ae918033fd74f473cdfef275705c1a9578d',
    'ddae4844fa510683817ed97183aa626c881141aefa30526208184dbfd04f363a',
    [["  unfold spliceTape operandEnd\n  repeat' apply And.intro","  unfold spliceTape operandEnd\n  dsimp only\n  repeat' apply And.intro"],
     ["  unfold spliceTape insertedWidth operandEnd\n  repeat' first | split | rfl | omega\n  congr 1\n  omega","  unfold spliceTape insertedWidth operandEnd\n  dsimp only\n  repeat' first | split | rfl | omega\n  all_goals congr 1 <;> omega"],
     ["      unfold B₀ C₀\n      omega","      unfold B₀ C₀\n      change w (e+2)=nξ+level+2+w e+w (e+1) at hsplice\n      omega"],
     ["  have hnew := tapeNew rB rC rG old bb cc gg nb nc t","  have hnew : a e=nb ∧ a (e+1)=nc ∧ a (e+2)=t :=\n    tapeNew rB rC rG old bb cc gg nb nc t"],
     ["      | here => simpa only [variableIndex,Nat.add_zero,bResult,hb₀] using hnew.1","      | here =>\n        simp only [variableIndex,Nat.add_zero,bResult]\n        exact hnew.1.trans hb₀.symm"],
     ["      | here => simpa only [variableIndex,Nat.add_zero,cResult,hc₀] using hnew.2.1","      | here =>\n        simp only [variableIndex,Nat.add_zero,cResult]\n        exact hnew.2.1.trans hc₀.symm"],
     ["      | here => simpa only [variableIndex,Nat.add_zero,gInput,hgg,endValues,t] using hnew.2.2","      | here =>\n        simp only [variableIndex,Nat.add_zero,gInput]\n        have ht : νg (shift gg (.here : Variable DirectCtx .ground))=t := hgg .here\n        exact hnew.2.2.trans ht.symm"],
     ["          simp only [variableIndex,Nat.zero_add,gOutput,hgg,endValues]\n          change a w=y\n          simpa only [Nat.add_zero,old,slot,RawSourceDAG.getVariable,↓reduceDIte,Option.getD_some,resultValues]\n            using hold 0",
      "          simp only [variableIndex,Nat.zero_add,gOutput]\n          have hy' : νg (shift gg (.there .here : Variable DirectCtx .ground))=y := hgg (.there .here)\n          have hOld : old 0=y := congrArg (resultValues ρ y)\n            (slotAt (.here : Variable (.ground::Γ) .ground) .here)\n          have hw : a w=old 0 := by simpa only [Nat.add_zero] using hold 0\n          exact hw.trans (hOld.trans hy'.symm)"]])
add('MATRIX-EMIT-PROGRAM-CAL','MatrixEmitProgramsProof',
    '48834d06091264486b51ba68871eb96b696d3cf7432d2bc5cf357730c9d98117',
    '7a2cf8c39cbe2a6130f9029165fbc0eba2a7bff8b531035223f21d5ad1f4772b',
    '9270df2602c04ac0f3e869fb31c14a9a6dee37013fcb9a370b31aa17b86666a7',
    '1795100050852444726-6','-UNIT-CODE','0d33c15859479bd285edf36fd0c1f71badc467d06c9d131984ab26b15642d613',
    '82859e2606175c5d8385276e47576ccc609ec1f1d8ca8b33e71609d1f58a12e6',
    [["    · simp only [h2,h4,if_false,if_true,List.mem_singleton] at hz","    · simp only [h4,Nat.reduceEqDiff,if_false,if_true,List.mem_singleton] at hz"],
     ["    · simp only [h,h5,if_true,List.mem_singleton] at hz","    · simp only [h5,le_refl,if_true,List.mem_singleton] at hz"],
     ["  have s := (sourceRow 9 0).comp (payloadProgram.comp (leftProgram.comp Primrec.fst))","  have c : Primrec (fun q : D => q.1) := Primrec.fst\n  have s := (sourceRow 9 0).comp (payloadProgram.comp (leftProgram.comp c))"],
     ["CurrentDecisionEmitter.liftCodePrimitive.comp","CurrentDecision.liftCodePrimitive.comp"],
     ["private theorem boolUnitProgram : Primrec boolUnit :=\n  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const _) (Primrec.const _)",
      "private theorem boolUnitProgram : Primrec boolUnit := by\n  have h : Primrec (fun j : Nat => if j=0 then (([noneStep 0 0 0],0,1) : Emit)\n      else ([noneStep 2 0 0],0,1)) :=\n    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const _) (Primrec.const _)\n  exact h.of_eq (fun j => by by_cases hj : j=0 <;> simp only [boolUnit,hj,if_true,if_false])"]])
add('UNIT-LOCAL-TYPED-PROGRAMS','UnitLocalProgramsProof',
    'aa8ba0494f20f4ba06702e734b567238a985551153d0b3f105ebbb6459715597',
    '5a33e639fc55be6f24a14b1b0175dcb84209f083045fb4bb9d9334caddd1823f',
    '55f535dc96ff9b6e62640c52ba00b6d91ff64f32c885d717938a9e28e138e1fc',
    '1795100234759149135-6','-UNIT-CODE','82859e2606175c5d8385276e47576ccc609ec1f1d8ca8b33e71609d1f58a12e6',
    '783f9486fcb97f211605904fbe875e10d5647b35fda597eb7ef569b0c1db437e',
    [["public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixEmitProgramsProof","public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixEmitProgramsProof\npublic import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeDefinitions"],
     ["private theorem timesProgram : Primrec₂ MatrixCode.times := by\n  let P := Nat×Nat\n  let S := P×Nat×Nat\n  have a : Primrec (fun q : S => q.1.2) := Primrec.snd.comp Primrec.fst\n  have x : Primrec (fun q : S => q.2.2) := Primrec.snd.comp Primrec.snd\n  exact Primrec.nat_rec (Primrec.fst : Primrec fun q : P => q.1) (Primrec.const (lit 0)) (addProgram.comp a x).to₂",
      "private theorem timesProgram : Primrec₂ MatrixCode.times := by\n  let S := Nat×Nat×Nat\n  have a : Primrec (fun q : S => q.1) := Primrec.fst\n  have x : Primrec (fun q : S => q.2.2) := Primrec.snd.comp Primrec.snd\n  have step : Primrec₂ (fun a (q : Nat×Nat) => MatrixCode.add a q.2) :=\n    (addProgram.comp a x).to₂\n  have rec := Primrec.nat_rec (Primrec.const (lit 0) : Primrec (fun _ : Nat => lit 0)) step\n  exact rec.comp Primrec.snd Primrec.fst"],
     ["  exact (binaryNode 2).comp (addProgram.comp (timesProgram.comp (Primrec.fst.comp row) l) (litProgram.comp b))\n    (addProgram.comp (addProgram.comp (timesProgram.comp c m) (timesProgram.comp d r)) (litProgram.comp e))",
      "  have left : Primrec (fun q : P => add (times q.1.1 q.2.1) (lit q.1.2.1)) :=\n    addProgram.comp (timesProgram.comp (Primrec.fst.comp row) l) (litProgram.comp b)\n  have middle : Primrec (fun q : P => add (times q.1.2.2.1 q.2.2.1)\n      (times q.1.2.2.2.1 q.2.2.2)) := addProgram.comp (timesProgram.comp c m) (timesProgram.comp d r)\n  have right : Primrec (fun q : P => add (add (times q.1.2.2.1 q.2.2.1)\n      (times q.1.2.2.2.1 q.2.2.2)) (lit q.1.2.2.2.2)) := addProgram.comp middle (litProgram.comp e)\n  exact (binaryNode 2).comp left right"],
     ["  have t := Primrec.list_map (Primrec.list_range.comp l)","  have t : Primrec (fun q : Code => (List.range (q.1.length-2)).map (fun i => i+3)) :=\n    Primrec.list_map (Primrec.list_range.comp l)"],
     ["    (Primrec.nat_add.comp (Primrec.snd : Primrec (fun q : Code×Nat => q.2)) (Primrec.const 3)).to₂\n  have table := Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 1) t)\n  exact RawSourceDAG.Operations.primitive.2.2.2.comp",
      "      (Primrec.nat_add.comp (Primrec.snd : Primrec (fun q : Code×Nat => q.2)) (Primrec.const 3)).to₂\n  have table : Primrec (fun q : Code => 0::1::(List.range (q.1.length-2)).map (fun i => i+3)) :=\n    Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 1) t)\n  exact RawSourceDAG.Operations.rename_code_primitive.comp"],
     ["CurrentDecisionEmitter.liftCodePrimitive.comp","CurrentDecision.liftCodePrimitive.comp"],
     ["  have r := RawSourceDAG.Operations.primitive.2.2.2.comp\n    (g.pair ((Primrec.const []).pair CurrentProbeCode.effective.1))",
      "  have args : Primrec (fun q : Code => (0::0::q.1,([] : List Nat),CurrentProbeCode.closeRaw q)) :=\n    g.pair ((Primrec.const []).pair CurrentProbeCode.effective.1)\n  have r := RawSourceDAG.Operations.rename_code_primitive.comp args"],
     ["  have d := CurrentDecisionEmitter.factorCodePrimitive.comp v","  have d : Primrec (fun q : P => CurrentDecisionEmitter.factorCode q.1) :=\n    CurrentDecision.factorCodePrimitive.comp v"]])
add('TEMPLATE-TYPED-ROUTES','TemplateCodeProof',
    'a246b07b2f106bc7db610562b10288c252022866358405d58bc96d780e1dd4bd',
    '14b2494dade7377af08b22f2162bc455c7012a1d142376d092600d9ecf670260',
    '5c1fd18a7f876b508e1a40c2e546ccb3476f82f0e70254d2e59666d734e6ac8f',
    '1795100417148646507-6','', 'ddae4844fa510683817ed97183aa626c881141aefa30526208184dbfd04f363a',
    '3b835263de74adae7500dd9b94d3b33c594c51bac1a45701c0707a80e7c42adf',
    [["  let plan := route hr z (rayPlacement wr)","  let plan : Renaming Γr Ξ := route hr z (rayPlacement wr)"],
     ["  let rB := route hB z (placeB wb wc wg)","  let rB : Renaming (WireCtx wb (.ground::Γ)) Ξ := route hB z (placeB wb wc wg)"],
     ["  let rC := route hC z (placeC wb wc wg)","  let rC : Renaming (WireCtx wc (.ground::Γ)) Ξ := route hC z (placeC wb wc wg)"],
     ["  let rG := route hG z (placeGraph wb wc wg)","  let rG : Renaming (WireCtx wg DirectCtx) Ξ := route hG z (placeGraph wb wc wg)"]])
def low_footprint(s):
    a=s.index('theorem activeBlockProgram')
    b=s.index('\nend LogicLineages',a)
    new='''/-- Exact active frame components are checked independently so the final
packing proof need not unfold the recursive renamer to infer any type. -/
private abbrev ActiveArgs := Nat×LinearCode×Block×Block

private def activeW (q : ActiveArgs) := q.2.2.1.1+q.2.2.2.1+2
private theorem activeLeftWidth : Primrec (fun q : ActiveArgs => q.2.2.1.1) :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem activeRightWidth : Primrec (fun q : ActiveArgs => q.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
private theorem activeWProgram : Primrec activeW :=
  Primrec.nat_add.comp (Primrec.nat_add.comp activeLeftWidth activeRightWidth) (Primrec.const 2)

private def activeCtx (q : ActiveArgs) := bitCtx (activeW q+1+q.1)
private theorem activeCtxProgram : Primrec activeCtx :=
  replicateZero.comp (Primrec.nat_add.comp (Primrec.succ.comp activeWProgram) Primrec.fst)

private def activeLIndex (q : ActiveArgs) (i : Nat) : Nat :=
  if i<q.2.2.1.1 then i+2 else if i=q.2.2.1.1 then 0 else i+q.2.2.2.1+2
private def activeRIndex (q : ActiveArgs) (i : Nat) : Nat :=
  if i=q.2.2.2.1 then 1 else i+q.2.2.1.1+2

private theorem activeOffset {h : ActiveArgs→Nat} (hh : Primrec h) :
    Primrec (fun q : ActiveArgs×Nat => q.2+h q.1+2) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd (hh.comp Primrec.fst)) (Primrec.const 2)

private theorem activeLIndexProgram : Primrec₂ activeLIndex := by
  let P := ActiveArgs×Nat
  have i : Primrec (fun q : P => q.2) := Primrec.snd
  have a : Primrec (fun q : P => q.1.2.2.1.1) := activeLeftWidth.comp Primrec.fst
  exact Primrec.ite (Primrec.nat_lt.comp i a) (Primrec.nat_add.comp i (Primrec.const 2))
    (Primrec.ite (Primrec.eq.comp i a) (Primrec.const 0) (activeOffset activeRightWidth))

private theorem activeRIndexProgram : Primrec₂ activeRIndex := by
  let P := ActiveArgs×Nat
  have i : Primrec (fun q : P => q.2) := Primrec.snd
  have b : Primrec (fun q : P => q.1.2.2.2.1) := activeRightWidth.comp Primrec.fst
  exact Primrec.ite (Primrec.eq.comp i b) (Primrec.const 1) (activeOffset activeLeftWidth)

private theorem activeRange {h : ActiveArgs→Nat} (hh : Primrec h) :
    Primrec (fun q => List.range (h q+1+q.1)) :=
  Primrec.list_range.comp (Primrec.nat_add.comp (Primrec.succ.comp hh) Primrec.fst)

private def activeLeft (q : ActiveArgs) : Nat :=
  MatrixCode.renameFormula (activeCtx q)
    ((List.range (q.2.2.1.1+1+q.1)).map (activeLIndex q)) q.2.2.1.2
private def activeRight (q : ActiveArgs) : Nat :=
  MatrixCode.renameFormula (activeCtx q)
    ((List.range (q.2.2.2.1+1+q.1)).map (activeRIndex q)) q.2.2.2.2

private theorem activeLeftProgram : Computable activeLeft := by
  have src : Primrec (fun q : ActiveArgs => q.2.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have table : Primrec (fun q : ActiveArgs => (List.range (q.2.2.1.1+1+q.1)).map (activeLIndex q)) :=
    Primrec.list_map (activeRange activeLeftWidth) activeLIndexProgram
  exact renamePart activeCtxProgram table src

private theorem activeRightProgram : Computable activeRight := by
  have src : Primrec (fun q : ActiveArgs => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have table : Primrec (fun q : ActiveArgs => (List.range (q.2.2.2.1+1+q.1)).map (activeRIndex q)) :=
    Primrec.list_map (activeRange activeRightWidth) activeRIndexProgram
  exact renamePart activeCtxProgram table src

private def activeRow (q : ActiveArgs) : Nat :=
  rawRow q.2.1 (MatrixCode.raw 0) (MatrixCode.raw 1) (MatrixCode.raw (activeW q))
private theorem activeRowProgram : Primrec activeRow := by
  have row : Primrec (fun q : ActiveArgs => q.2.1) := Primrec.fst.comp Primrec.snd
  have z : Primrec (fun _ : ActiveArgs => MatrixCode.raw 0) := Primrec.const _
  have o : Primrec (fun _ : ActiveArgs => MatrixCode.raw 1) := Primrec.const _
  have w : Primrec (fun q : ActiveArgs => MatrixCode.raw (activeW q)) := rawProgram.comp activeWProgram
  exact rowProgram.comp (row.pair (z.pair (o.pair w)))

private def activeOutput (q : ActiveArgs) : Block :=
  (activeW q,MatrixCode.both (MatrixCode.both (activeLeft q) (activeRight q)) (activeRow q))

section
attribute [local irreducible] activeLeft activeRight activeRow activeW activeOutput
private theorem activeOutputProgram : Computable activeOutput := by
  have inner : Computable (fun q : ActiveArgs => MatrixCode.both (activeLeft q) (activeRight q)) :=
    (binaryNode 6).to_comp.comp activeLeftProgram activeRightProgram
  have outer : Computable (fun q : ActiveArgs =>
      MatrixCode.both (MatrixCode.both (activeLeft q) (activeRight q)) (activeRow q)) :=
    (binaryNode 6).to_comp.comp inner activeRowProgram.to_comp
  unfold activeOutput
  exact activeWProgram.to_comp.pair outer

theorem activeBlockProgram : Computable (fun q : Nat×LinearCode×Block×Block => activeBlock q.1 q.2.1 q.2.2.1 q.2.2.2) :=
  activeOutputProgram.of_eq (fun q => by
    unfold activeOutput activeLeft activeRight activeCtx activeLIndex activeRIndex activeRow activeW activeBlock
    rfl)
end
'''
    old=s[s.index('theorem groundBlockProgram'):s.index('private theorem renamePart')].rstrip('\n')
    ground='''section
attribute [local irreducible] groundOutput CurrentAbsolute.anchor groundBlock
theorem groundBlockProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable (groundBlock p f) := by
  have C : Computable (CurrentAbsolute.anchor p f) := CurrentAbsolute.anchorEffective p hp f hc hf
  have pack : Computable (fun d : Code => (d,CurrentAbsolute.anchor p f d)) :=
    (Computable.id : Computable (id : Code→Code)).pair C
  have H : Computable (fun d : Code => groundOutput (d,CurrentAbsolute.anchor p f d)) :=
    groundOutputProgram.to_comp.comp pack
  exact H.of_eq (fun d => by unfold groundOutput groundBlock; rfl)
end'''
    return [('  have rec := Primrec.nat_rec', '  have recurse := Primrec.nat_rec'),
       ('  exact rec.comp Primrec.snd Primrec.fst','  exact recurse.comp Primrec.snd Primrec.fst'),
       ('CurrentDecisionEmitter.factorCode q.1','CurrentDecision.factorCode q.1'),
       (old,ground),(s[a:b],new)]
add('UNIT-LOCAL-SPLIT-COMPUTABLE','UnitLocalProgramsProof',
    '5a33e639fc55be6f24a14b1b0175dcb84209f083045fb4bb9d9334caddd1823f',
    '9046aaa88295bb9bdd2691659ddd1e25659a4d702c9fa55bcc3bcfad08c9d8ce',
    '893cc4297ee46d5342358ca853e1bea377c8c3d0934d4346b76807aee054681d',
    '1795100512350053980-6','-UNIT-CODE',
    '783f9486fcb97f211605904fbe875e10d5647b35fda597eb7ef569b0c1db437e',
    'b780f9b46872e46b2792383db5baba5067a129f7df6763e7b5a83a6c4d836966', low_footprint)
add('TEMPLATE-INSERT-LITERAL-PROJECT','TemplateCodeProof',
    '14b2494dade7377af08b22f2162bc455c7012a1d142376d092600d9ecf670260',
    '9b280901c26a0363870d79d97a21cf463207d2906b95165bbb4d30045283e113',
    '9d3e3688a0a5662a61afa1b766a068130d074dfa56cad58d06985dc4c8c3de35',
    '1795100687441070665-6','', '3b835263de74adae7500dd9b94d3b33c594c51bac1a45701c0707a80e7c42adf',
    '860114515449b9f64ed9be9cca9dccb69bc679a6713e230f0b91c4e3f7bbedf4',
    [["    unfold placeB w insertedWidth operandEnd\n    split <;> try split <;> omega",
      "    unfold placeB w insertedWidth operandEnd\n    split\n    · omega\n    · split <;> omega"],
     ["    unfold placeC w insertedWidth operandEnd\n    split <;> try split <;> omega",
      "    unfold placeC w insertedWidth operandEnd\n    split\n    · omega\n    · split <;> omega"],
     ["  change (w,insertedBody rawLayout wb wc wg nξ level _ _ _) =",
      "  change (w,insertedBody rawLayout wb wc wg nξ level\n    (MatrixCode.renameFormula (UnitCode.bitCtx (w+1+Γ.length))\n      ((List.range (wb+1+Γ.length)).map (placeB wb wc wg)) (MatrixCode.formula b.matrix))\n    (MatrixCode.renameFormula (UnitCode.bitCtx (w+1+Γ.length))\n      ((List.range (wc+1+Γ.length)).map (placeC wb wc wg)) (MatrixCode.formula c.matrix))\n    (MatrixCode.renameFormula (UnitCode.bitCtx (w+1+Γ.length))\n      ((List.range (wg+2)).map (placeGraph wb wc wg)) (MatrixCode.formula g.matrix))) ="]])
def read(f,overlay): return overlay[f] if f in overlay else f.read_bytes()
def require(data, value, label):
    assert digest(data)==value, (label,digest(data),value)
overlay={}
original={}
records=[]
memory=[]
for item in ordered:
    mf=D/(P+item['man']+'-AUTHOR-MANIFEST.json')
    sf=N/(A+item['file']+'.lean')
    old=read(sf,overlay)
    prev_manifest=read(mf,overlay)
    require(old,item['prev'],sf)
    require(prev_manifest,item['presha'],mf)
    meta=json.loads(prev_manifest)
    assert meta['sources'][str(sf)]==item['prev']
    fp=Path(meta['freeze'])
    require(fp.read_bytes(),meta['freeze_sha256'],fp)
    for f,h in json.loads(fp.read_text())['sources'].items(): require(Path(f).read_bytes(),h,f)
    prediff=D/(P+'-'+item['tag']+'-PROPOSED.diff')
    reps=item['replacements']
    if reps is None:
        d=prediff.read_bytes()
        require(d,item['diff'],prediff)
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/sf.name
            p.write_bytes(old)
            subprocess.run(['patch',str(p),str(prediff.resolve())],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
            new=p.read_bytes()
    else:
        if callable(reps): reps=reps(old.decode())
        new=compute_text(old.decode(),reps).encode()
        d=''.join(difflib.unified_diff(old.decode().splitlines(True),new.decode().splitlines(True),'a/'+str(sf),'b/'+str(sf))).encode()
    require(d,item['diff'],prediff)
    require(new,item['result'],sf)
    meta['sources'][str(sf)]=item['result']
    next_manifest=(json.dumps(meta,indent=2)+'\n').encode()
    require(next_manifest,item['aftersha'],mf)
    original.setdefault(sf,old)
    original.setdefault(mf,prev_manifest)
    overlay[sf]=new
    overlay[mf]=next_manifest
    archive=D/'current-paid-head-graph-failures'/item['receipt']
    receipt_preserved=(archive/(item['receipt']+'.json')).is_file()
    record={k:v for k,v in item.items() if k!='replacements'}
    record.update(source=str(sf),author_manifest=str(mf),original_native_receipt_available=receipt_preserved,
                  evidence_class="byte-identical proof edit reconstructed from reviewed tool transcript; no current native validation")
    records.append(record)
    memory.append((sf,old,new,d,prev_manifest,next_manifest,record))
    print(item['tag'],item['diff'][:8],item['result'][:8],item['aftersha'][:8], 'receipt-retained='+str(receipt_preserved))
for stage in ('-FOUNDATION','-UNIT-CODE',''):
    f=D/(P+stage+'-AUTHOR-MANIFEST.json')
    data=read(f,overlay)
    j=json.loads(data)
    fz=Path(j['freeze']); require(fz.read_bytes(),j['freeze_sha256'],fz)
    for p,h in {**json.loads(fz.read_text())['sources'],**j['sources']}.items():require(read(Path(p),overlay),h,p)
    print(stage or 'whole','pins',len(json.loads(fz.read_text())['sources']),len(j['sources']),digest(data),flush=True)
if sys.argv[1:] == ['--write']:
    root=D/'current-paid-head-graph-recovery-editions'
    summary=D/(P+'-RECOVERED-PROOF-EDITIONS-NOV19.json')
    assert not root.exists() and not summary.exists()
    for f,old in original.items(): assert f.read_bytes()==old
    root.mkdir()
    for sf,old,new,d,mp,mn,rec in memory:
        sub=root/rec['tag']
        sub.mkdir()
        (sub/'prior.lean').write_bytes(old)
        (sub/'reviewed.diff').write_bytes(d)
        (sub/'prior-manifest.json').write_bytes(mp)
        (sub/'reviewed-manifest.json').write_bytes(mn)
        (sub/'provenance.json').write_text(json.dumps(rec,indent=2)+'\n')
    for f,new in overlay.items(): f.write_bytes(new)
    final={
        'status':'source bytes restored after execution-environment reset; no native rerun; thm:head-graph pending',
        'recovery_base':'e8a4341e source snapshot',
        'immaterial_intermediate_native_output':'the 1643 original failure archive survives; other listed original local receipts unavailable, not fabricated',
        'frozen_comparator_or_target_changed':False,
        'untested_final_proof_candidate':['TemplateCodeProof after exact projected-rows edit; 1725 never launched'],
        'prior_not_current_native_observations':[
           '1674 observed successful InsertedProof, old output no longer present:1795100180965546991-6',
           '1680 observed MatrixEmitProgramsProof pass before UnitLocal failure:1795100234759149135-6',
           '1714 own UnitLocal exact current approved source observed deterministic heartbeat stops on activeLIndex, activeRIndex and activeRow; no unchanged retry permitted:1795100795774455760-6'],
        'edits':records,
        'restored_active':{str(p):digest(v) for p,v in overlay.items()},
    }
    summary.write_text(json.dumps(final,indent=2)+'\n')
    for f,new in overlay.items():assert f.read_bytes()==new
    print('Recovered source editions and exact active files:',len(records),len(overlay),digest(summary.read_bytes()))
else:
    assert not sys.argv[1:]
    print('DRY verification only; no checkout writes')
