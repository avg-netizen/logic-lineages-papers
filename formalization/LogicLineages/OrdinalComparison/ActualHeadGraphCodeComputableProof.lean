module
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeTargets
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodePrimitiveProof
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodePrimitiveProof
public import LogicLineages.OrdinalComparison.UnitScalarEvaluationCodeProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentPrimitiveProof
public import LogicLineages.OrdinalComparison.EncodedCollapseProof
public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof
public import LogicLineages.OrdinalComparison.RawNormCode
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
open ArithmeticCode ForwardTranslation
attribute [local irreducible] Nat.sqrt Nat.unpair
private theorem num_pr : Primrec numeralCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.1
private theorem var_pr : Primrec variableCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.1
private theorem add_pr : Primrec₂ addCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.1
private theorem scale_pr : Primrec₂ scaleCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.1
private theorem lift_pr : Primrec₂ liftCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.1
private theorem eq_pr : Primrec₂ eqCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.1
private theorem le_pr : Primrec₂ leCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.1
private theorem obs_pr : Primrec (fun p : Nat×Nat×List Nat×Nat=>observationCode p.1 p.2.1 p.2.2.1 p.2.2.2) := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.1
private theorem and_pr : Primrec₂ andCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.1
private theorem or_pr : Primrec₂ orCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.1
private theorem exists_pr : Primrec existsCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.1
private theorem conj_pr : Primrec conjunctionCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.2.1
private theorem disj_pr : Primrec disjunctionCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem succ_pr : Primrec₂ successorCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem phi_pr : Primrec₂ phiCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem chain_pr : Primrec (fun p : Nat×Nat×Nat=>phiChainCode p.1 p.2.1 p.2.2) := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
private theorem norm_pr : Primrec headNormCode :=
  (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp encodedClosedHeadPrimitiveRecursive
private theorem shifted_pr : Primrec₂ shiftedNormCode :=
  Primrec.nat_add.comp (norm_pr.comp Primrec.fst) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
private theorem base_pr : Primrec₂ rayBaseCode :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (norm_pr.comp Primrec.fst) Primrec.snd) (Primrec.const 1)
private theorem threshold_pr : Primrec (fun p : Nat×Nat×Nat=>thresholdCode p.1 p.2.1 p.2.2) :=
  Primrec.nat_max.comp (shifted_pr.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
    (base_pr.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
private theorem control_pr : Primrec₂ controlIter :=
  Primrec.nat_iterate Primrec.fst Primrec.snd (Phi_primrec.comp Primrec.snd).to₂
private theorem prefix_comp : Computable (fun p : Nat×Nat×Nat=>prefixValueCode p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat×Nat×Nat=>p.2.1) := Primrec.fst.comp Primrec.snd
  have hv := Primrec.nat_sub.comp (control_pr.comp hd (Primrec.snd.comp Primrec.snd)) (norm_pr.comp Primrec.fst)
  exact Primrec.nat_add.to_comp.comp (encodedCollapseComputable.comp
    (encodedFiniteTailPrimitiveRecursive.comp (encodedClosedHeadPrimitiveRecursive.comp Primrec.fst) hv).to_comp) hd.to_comp
attribute [local irreducible] headNormCode shiftedNormCode rayBaseCode thresholdCode controlIter prefixValueCode
private theorem ray_pr : Primrec₂ raySourceCode := by
  have hg : Primrec (fun p : List Nat×Nat=>GroundCaptureClosingCode.sourceCode p.1 0 p.2) :=
    GroundCaptureClosingCode.Proof.primitiveRecursiveAlgorithms.1.comp (Primrec.fst.pair ((Primrec.const 0).pair Primrec.snd))
  have hi := ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp ((Primrec.const 0).pair ((Primrec.const 1).pair hg))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp hi (Primrec.const 0))) (Primrec.const 5)
private abbrev F := Nat×Nat×Nat×Nat×Nat
private abbrev G := Nat×Nat×Nat×Nat×Nat×Nat×Nat
private theorem fold_prefix {α β : Type} (xs : List α) (default : α) (step : β → α → β) (init : β)
    (n : Nat) (hn : n≤xs.length) :
    Nat.rec init (fun i previous => step previous (xs.getD i default)) n=(xs.take n).foldl step init := by
  induction n with
  | zero => simp
  | succ n ih =>
    change step (Nat.rec init (fun i previous => step previous (xs.getD i default)) n) (xs.getD n default)=_
    rw [ih (by omega),List.take_succ_eq_append_getElem (by omega),List.foldl_append,
      List.foldl_cons,List.foldl_nil,List.getD_eq_getElem xs default (by omega)]

private theorem computable_foldl {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun state item => h a (state,item)) (g a)) := by
  have hitem : Computable (fun p : α × (Nat × σ) => (f p.1).getD p.2.1 default) :=
    (Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun a : α => fun state : Nat × σ => h a (state.2,(f a).getD state.1 default)) :=
    hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair hitem)
  apply (Computable.nat_rec (Computable.list_length.comp hf) hg hstep).of_eq
  intro a
  rw [fold_prefix (f a) default (fun state item => h a (state,item)) (g a) (f a).length le_rfl]
  simp only [List.take_length]

private theorem computable_foldr {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → σ} {h : α → β × σ → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun item state => h a (item,state)) (g a)) := by
  have hs : Computable₂ (fun a : α => fun state : σ × β => h a (state.2,state.1)) :=
    hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd))
  apply (computable_foldl default (Computable.list_reverse.comp hf) hg hs).of_eq
  intro a
  rw [List.foldr_eq_foldl_reverse]

private theorem map_comp {α : Type} [Primcodable α] {f : α → List Nat} {g : α → Nat → Nat}
    (hf : Computable f) (hg : Computable₂ g) : Computable (fun a=>(f a).map (g a)) := by
  have hs : Computable (fun p : α×(Nat×List Nat)=>(g p.1 p.2.1)::p.2.2) :=
    Computable.list_cons.comp (hg.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (computable_foldr 0 hf (Computable.const []) hs.to₂).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons,List.map_cons,ih]

private theorem finite_comp : Computable (fun p : F=>finitePrefixCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have ha : Primrec (fun p : F=>p.1) := Primrec.fst
  have hc : Primrec (fun p : F=>p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : F=>p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hbound := threshold_pr.comp (ha.pair (hc.pair hd))
  have hrel : PrimrecRel (fun j b : Nat=>b ≤ j) :=
    Primrec.nat_le.comp₂ Primrec₂.right Primrec₂.left
  have hfilter : Primrec (fun p : F=>(List.range (thresholdCode p.1 p.2.1 p.2.2.1)).filter
      (fun j=>decide (shiftedNormCode p.1 p.2.2.1 ≤ j))) :=
    (PrimrecRel.listFilter hrel).comp
      (Primrec.list_range.comp hbound) (shifted_pr.comp ha hd)
  have hj : Computable (fun p : F×Nat=>andCode (eqCode p.1.2.2.2.1 (numeralCode p.2))
      (eqCode p.1.2.2.2.2 (numeralCode (prefixValueCode p.1.1 p.1.2.2.1 p.2)))) := by
    have ht : Computable (fun p : F×Nat=>p.1.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    have hy : Computable (fun p : F×Nat=>p.1.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    have hp : Computable (fun p : F×Nat=>prefixValueCode p.1.1 p.1.2.2.1 p.2) := prefix_comp.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair Computable.snd))
    exact and_pr.to_comp.comp (eq_pr.to_comp.comp ht (num_pr.to_comp.comp Computable.snd))
      (eq_pr.to_comp.comp hy (num_pr.to_comp.comp hp))
  exact disj_pr.to_comp.comp (map_comp hfilter.to_comp hj.to₂)
private theorem zeros_pr : Primrec (fun n : Nat=>List.replicate n (numeralCode 0)) :=
  (Primrec.list_map Primrec.list_range (Primrec.const (numeralCode 0)).to₂).of_eq (fun n=>by simp)
private theorem tail_pr : Primrec (fun p : G=>tailCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  have hn : Primrec (fun p : G=>p.1) := Primrec.fst
  have ha : Primrec (fun p : G=>p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : G=>p.2.2.1) := (Primrec.fst.comp Primrec.snd).comp Primrec.snd
  have hd : Primrec (fun p : G=>p.2.2.2.1) := ((Primrec.fst.comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have hq : Primrec (fun p : G=>p.2.2.2.2.1) := (((Primrec.fst.comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have ht : Primrec (fun p : G=>p.2.2.2.2.2.1) := ((((Primrec.fst.comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have hy : Primrec (fun p : G=>p.2.2.2.2.2.2) := ((((Primrec.snd.comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have hbound := threshold_pr.comp (ha.pair (hc.pair hd))
  have hbase := base_pr.comp ha hc
  have hchain := chain_pr.comp (hd.pair ((lift_pr.comp (Primrec.const 2) ht).pair
    (add_pr.comp (num_pr.comp hbase) (Primrec.const (variableCode 1)))))
  have hunit := UnitArithmeticFormulaCode.Proof.effectiveAlgorithms.1.comp
    (hq.pair ((Primrec.list_cons.comp (Primrec.const (variableCode 1)) (zeros_pr.comp hn)).pair (Primrec.const (variableCode 0))))
  have heq := eq_pr.comp (lift_pr.comp (Primrec.const 2) hy)
    (add_pr.comp (Primrec.const (variableCode 0)) (num_pr.comp hd))
  exact and_pr.comp (le_pr.comp (num_pr.comp hbound) ht) (exists_pr.comp (exists_pr.comp
    (conj_pr.comp (Primrec.list_cons.comp hchain (Primrec.list_cons.comp hunit (Primrec.list_cons.comp heq (Primrec.const [])))))))
attribute [local irreducible] finitePrefixCode tailCode raySourceCode
private theorem graph_comp : Computable (fun p : G=>graphCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  have hf : Computable (fun p : G=>finitePrefixCode p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) :=
    finite_comp.comp ((Computable.fst.comp Computable.snd).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd))))))))
  exact or_pr.to_comp.comp hf tail_pr.to_comp
private abbrev C := List Nat×Nat
private theorem result_comp : Computable (fun p : C×Nat×Nat=>
    (UnitEliminationBuildCode.realizedCompileCode (0::p.1.1) (raySourceCode p.1.1 p.1.2)).bind
      (fun q=>some (p.2.1,p.2.2,q))) := by
  have hq : Computable (fun p : C×Nat×Nat=>UnitEliminationBuildCode.realizedCompileCode (0::p.1.1) (raySourceCode p.1.1 p.1.2)) :=
    UnitEliminationBuildCode.Proof.actualUniformSourceCompiler.1.comp
      (Computable.list_cons.comp (Computable.const 0) (Computable.fst.comp Computable.fst))
      (ray_pr.to_comp.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.fst))
  exact Computable.option_bind hq (Computable.option_some.comp
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))).to₂
private theorem scalar_comp : Computable (fun p : C×List Nat×Nat=>
    (UnitScalarEvaluationCode.valueCode (p.2.1.getD 0 0)).bind fun c=>
      (UnitEliminationBuildCode.realizedCompileCode (0::p.1.1) (raySourceCode p.1.1 p.1.2)).bind
        (fun q=>some (p.2.2,c,q))) := by
  have hv : Computable (fun p : C×List Nat×Nat=>UnitScalarEvaluationCode.valueCode (p.2.1.getD 0 0)) :=
    UnitScalarEvaluationCode.Proof.effectiveGeneratedScalar.2.1.comp
      (((Primrec.list_getD (0 : Nat)).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).to_comp)
  exact Computable.option_bind hv (result_comp.comp ((Computable.fst.comp Computable.fst).pair
    ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))).to₂
private theorem vector_comp : Computable (fun p : C×List Nat=>
    (UnitHeadCode.positiveCode (p.2.getD 1 0)).bind fun a=>
      (UnitScalarEvaluationCode.valueCode (p.2.getD 0 0)).bind fun c=>
      (UnitEliminationBuildCode.realizedCompileCode (0::p.1.1) (raySourceCode p.1.1 p.1.2)).bind
        (fun q=>some (a,c,q))) := by
  have hv : Computable (fun p : C×List Nat=>UnitHeadCode.positiveCode (p.2.getD 1 0)) :=
    (UnitHeadCode.Proof.primitiveRecursiveAlgorithms.2.1.comp
      ((Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1))).to_comp
  exact Computable.option_bind hv (scalar_comp.comp ((Computable.fst.comp Computable.fst).pair
    ((Computable.snd.comp Computable.fst).pair Computable.snd))).to₂
private theorem assignment_comp : Computable (fun p : C=>
    (DefaultSourceAssignment.assignmentCode p.1 p.2).bind fun v=>
    (UnitHeadCode.positiveCode (v.getD 1 0)).bind fun a=>
      (UnitScalarEvaluationCode.valueCode (v.getD 0 0)).bind fun c=>
      (UnitEliminationBuildCode.realizedCompileCode (0::p.1) (raySourceCode p.1 p.2)).bind
        (fun q=>some (a,c,q))) :=
  Computable.option_bind DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.to_comp vector_comp.to₂
private theorem constants_comp : Computable₂ constantsCode := by
  have hafter : Computable (fun p : C×Nat=>if p.2=SyntaxCode.typeCode (Ty.curriedGround 1) then
      (DefaultSourceAssignment.assignmentCode p.1.1 p.1.2).bind (fun v=>
      (UnitHeadCode.positiveCode (v.getD 1 0)).bind fun a=>
        (UnitScalarEvaluationCode.valueCode (v.getD 0 0)).bind fun c=>
        (UnitEliminationBuildCode.realizedCompileCode (0::p.1.1) (raySourceCode p.1.1 p.1.2)).bind
          (fun q=>some (a,c,q))) else none) :=
    by
      have hp : PrimrecPred (fun p : C×Nat=>p.2=SyntaxCode.typeCode (Ty.curriedGround 1)) :=
        Primrec.eq.comp Primrec.snd (Primrec.const _)
      simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp
        (assignment_comp.comp Computable.fst) (Computable.const none)
  exact Computable.option_bind SyntaxCode.Proof.checkPrimitiveRecursive.to_comp hafter.to₂
attribute [local irreducible] graphCode constantsCode
private theorem compile_comp : Computable (fun p : List Nat×Nat×Nat×Nat×Nat=>compileCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hc : Computable (fun p : List Nat×Nat×Nat×Nat×Nat=>constantsCode p.1 p.2.1) :=
    constants_comp.comp Computable.fst (Computable.fst.comp Computable.snd)
  exact Computable.option_map hc (graph_comp.comp
    ((Computable.list_length.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.fst.comp Computable.snd).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
            ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
              (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))))))).to₂

theorem effectiveAlgorithms : Targets.EffectiveAlgorithms := ⟨ray_pr,constants_comp,graph_comp,compile_comp⟩
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
