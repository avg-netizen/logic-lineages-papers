module
public import LogicLineages.OrdinalComparison.OriginalHeadWireCodeTargets
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeComputableProof
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodePrimitiveProof
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Proof
open ArithmeticCode ForwardTranslation
attribute [local irreducible] Nat.sqrt Nat.unpair
private theorem num_pr : Primrec numeralCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.1
private theorem add_pr : Primrec₂ addCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.1
private theorem lift_pr : Primrec₂ liftCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.1
private theorem exists_pr : Primrec existsCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.1
private theorem conjunction_pr : Primrec conjunctionCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.2.1
private theorem wire_pr : Primrec₂ wireCode :=
  add_pr.comp (add_pr.comp (add_pr.comp (num_pr.comp Primrec.fst)
    (Primrec.const (variableCode 1))) (Primrec.const (variableCode 0))) (num_pr.comp Primrec.snd)
private theorem combine_pr : Primrec (fun p : Nat×Nat×Nat=>combineCode p.1 p.2.1 p.2.2) :=
  exists_pr.comp (exists_pr.comp (conjunction_pr.comp (Primrec.list_cons.comp Primrec.fst
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))))))
private theorem shifted_pr : Primrec₂ GraphCode.shiftedNormCode :=
  Primrec.nat_add.comp (((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp encodedClosedHeadPrimitiveRecursive).comp Primrec.fst)
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
private theorem shift_inputs_pr : Primrec (fun xs : List Nat=>xs.map (liftCode 2)) :=
  Primrec.list_map Primrec.id (lift_pr.comp (Primrec.const 2) Primrec.snd).to₂
attribute [local irreducible] GraphCode.graphCode GraphCode.shiftedNormCode GraphCode.constantsCode
  UnitArithmeticFormulaCode.sourceFormulaCode wireCode combineCode
private abbrev S₁ := RawInput×Nat
private abbrev S₂ := S₁×(Nat×Nat×Nat)
private abbrev S₃ := S₂×Nat
private abbrev S₄ := S₃×Nat
private noncomputable def finish (p : S₄) : Option Nat := some (combineCode p.1.2 p.2
  (GraphCode.graphCode p.1.1.1.1.2.2.2.1.length p.1.1.2.1 p.1.1.2.2.1 p.1.1.1.1.2.2.2.2.2.1 p.1.1.2.2.2
    (wireCode (GraphCode.shiftedNormCode p.1.1.2.1 p.1.1.1.1.2.2.2.2.2.1) (SyntaxCode.typeLevel p.1.1.1.2))
    (liftCode 2 p.1.1.1.1.2.2.2.2.2.2.2)))
private theorem finish_comp : Computable finish := by
  have h0 : Computable (fun p : S₄=>p.1.1.1.2) := Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))
  have h1 : Computable (fun p : S₄=>p.1.1.1.1.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))))))
  have h2 : Computable (fun p : S₄=>List.length (p.1.1.1.1.2.2.2.1)) := Computable.list_length.comp (h1)
  have h3 : Computable (fun p : S₄=>p.1.1.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))
  have h4 : Computable (fun p : S₄=>p.1.1.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.id)))))
  have h5 : Computable (fun p : S₄=>p.1.1.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.id)))))
  have h6 : Computable (fun p : S₄=>p.1.1.1.1.2.2.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))))))))
  have h7 : Computable (fun p : S₄=>GraphCode.shiftedNormCode (p.1.1.2.1) (p.1.1.1.1.2.2.2.2.2.1)) := shifted_pr.to_comp.comp (h3) (h6)
  have h8 : Computable (fun p : S₄=>SyntaxCode.typeLevel (p.1.1.1.2)) := SyntaxCode.Proof.typeLevelPrimitiveRecursive.to_comp.comp (h0)
  have h9 : Computable (fun p : S₄=>wireCode (GraphCode.shiftedNormCode (p.1.1.2.1) (p.1.1.1.1.2.2.2.2.2.1)) (SyntaxCode.typeLevel (p.1.1.1.2))) := wire_pr.to_comp.comp (h7) (h8)
  have h10 : Computable (fun p : S₄=>p.1.1.1.1.2.2.2.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id)))))))))))
  have h11 : Computable (fun p : S₄=>liftCode (2) (p.1.1.1.1.2.2.2.2.2.2.2)) := lift_pr.to_comp.comp ((Computable.const (2))) (h10)
  have h12 : Computable (fun p : S₄=>GraphCode.graphCode (List.length (p.1.1.1.1.2.2.2.1)) (p.1.1.2.1) (p.1.1.2.2.1) (p.1.1.1.1.2.2.2.2.2.1) (p.1.1.2.2.2) (wireCode (GraphCode.shiftedNormCode (p.1.1.2.1) (p.1.1.1.1.2.2.2.2.2.1)) (SyntaxCode.typeLevel (p.1.1.1.2))) (liftCode (2) (p.1.1.1.1.2.2.2.2.2.2.2))) := GraphCode.Proof.effectiveAlgorithms.2.2.1.comp ((h2).pair ((h3).pair ((h4).pair ((h6).pair ((h5).pair ((h9).pair (h11)))))))
  have h13 : Computable (fun p : S₄=>p.1.2) := Computable.snd.comp (Computable.fst.comp (Computable.id))
  have h14 : Computable (fun p : S₄=>p.2) := Computable.snd.comp (Computable.id)
  exact Computable.option_some.comp (combine_pr.to_comp.comp ((h13).pair ((h14).pair (h12))))
private noncomputable def afterB (p : S₃) : Option Nat :=
  (UnitArithmeticFormulaCode.sourceFormulaCode (p.1.1.1.1) (p.1.1.1.2.2.1) ((fun xs=>xs.map (liftCode 2)) (p.1.1.1.2.2.2.2.2.2.1)) (variableCode 0)).bind (fun v=>finish (p,v))
private theorem afterB_comp : Computable afterB := by
  have h0 : Computable (fun p : S₃=>p.1.1.1.1) := Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))
  have h1 : Computable (fun p : S₃=>p.1.1.1.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))))
  have h2 : Computable (fun p : S₃=>p.1.1.1.2.2.2.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))))))))
  have h3 : Computable (fun p : S₃=>(fun xs=>xs.map (liftCode 2)) (p.1.1.1.2.2.2.2.2.2.1)) := shift_inputs_pr.to_comp.comp (h2)
  have h4 : Computable (fun p : S₃=>UnitArithmeticFormulaCode.sourceFormulaCode (p.1.1.1.1) (p.1.1.1.2.2.1) ((fun xs=>xs.map (liftCode 2)) (p.1.1.1.2.2.2.2.2.2.1)) (variableCode 0)) := UnitArithmeticFormulaCode.Proof.effectiveAlgorithms.2.comp ((h0).pair ((h1).pair ((h3).pair ((Computable.const (variableCode 0))))))
  exact Computable.option_bind h4 finish_comp.to₂
private noncomputable def afterConstants (p : S₂) : Option Nat :=
  (UnitArithmeticFormulaCode.sourceFormulaCode (p.1.1.1) (p.1.1.2.1) ((fun xs=>xs.map (liftCode 2)) (p.1.1.2.2.2.2.2.2.1)) (variableCode 1)).bind (fun v=>afterB (p,v))
private theorem afterConstants_comp : Computable afterConstants := by
  have h0 : Computable (fun p : S₂=>p.1.1.1) := Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.id)))
  have h1 : Computable (fun p : S₂=>p.1.1.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.id))))
  have h2 : Computable (fun p : S₂=>p.1.1.2.2.2.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.id)))))))))
  have h3 : Computable (fun p : S₂=>(fun xs=>xs.map (liftCode 2)) (p.1.1.2.2.2.2.2.2.1)) := shift_inputs_pr.to_comp.comp (h2)
  have h4 : Computable (fun p : S₂=>UnitArithmeticFormulaCode.sourceFormulaCode (p.1.1.1) (p.1.1.2.1) ((fun xs=>xs.map (liftCode 2)) (p.1.1.2.2.2.2.2.2.1)) (variableCode 1)) := UnitArithmeticFormulaCode.Proof.effectiveAlgorithms.2.comp ((h0).pair ((h1).pair ((h3).pair ((Computable.const (variableCode 1))))))
  exact Computable.option_bind h4 afterB_comp.to₂
private noncomputable def afterType (p : S₁) : Option Nat :=
  (GraphCode.constantsCode (p.1.2.2.2.1) (p.1.2.2.2.2.1)).bind (fun v=>afterConstants (p,v))
private theorem afterType_comp : Computable afterType := by
  have h0 : Computable (fun p : S₁=>p.1.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.id)))))
  have h1 : Computable (fun p : S₁=>p.1.2.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.id))))))
  have h2 : Computable (fun p : S₁=>GraphCode.constantsCode (p.1.2.2.2.1) (p.1.2.2.2.2.1)) := GraphCode.Proof.effectiveAlgorithms.2.1.comp (h0) (h1)
  exact Computable.option_bind h2 afterConstants_comp.to₂
private noncomputable def guarded (p : S₁×Nat) : Option Nat :=
  if p.2≠0 ∧ (p.2-1).unpair.1=p.1.2 ∧ 0<SyntaxCode.typeLevel p.1.2 then afterType p.1 else none
private theorem guard_comp : Computable guarded := by
  have hs : Primrec (fun p : S₁×Nat=>p.1.2) := Primrec.snd.comp Primrec.fst
  have ha : Primrec (fun p : S₁×Nat=>p.2) := Primrec.snd
  have hh : PrimrecPred (fun p : S₁×Nat=>p.2≠0 ∧ (p.2-1).unpair.1=p.1.2 ∧ 0<SyntaxCode.typeLevel p.1.2) :=
    (Primrec.eq.comp ha (Primrec.const 0)).not.and
      ((Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp ha (Primrec.const 1)))) hs).and
        (Primrec.nat_lt.comp (Primrec.const 0) (SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp hs)))
  unfold guarded
  simpa only [Bool.cond_decide] using Computable.cond hh.decide.to_comp
    (afterType_comp.comp Computable.fst) (Computable.const none)
private noncomputable def afterDomain (p : S₁) : Option Nat :=
  (SyntaxCode.check p.1.1 p.1.2.1).bind (fun a=>guarded (p,a))
private theorem afterDomain_comp : Computable afterDomain :=
  Computable.option_bind (SyntaxCode.Proof.checkPrimitiveRecursive.to_comp.comp
    ((Computable.fst.comp Computable.fst).pair (Computable.fst.comp (Computable.snd.comp Computable.fst)))) guard_comp.to₂

theorem effectiveCompiler : Targets.EffectiveCompiler := by
  exact Computable.option_bind (SyntaxCode.Proof.checkPrimitiveRecursive.to_comp.comp
    (Computable.fst.pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))) afterDomain_comp.to₂
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Proof
