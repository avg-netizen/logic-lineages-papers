module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixTermProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
open LogicLineages.OrdinalComparison.Source
open PrimitiveLowering RawSourceDAG
open RawSourceDAG.InputCompiler (InputStep InputCode encodeInput encodeInputRow)

abbrev BooleanEmitter (Γ : List Ty) :=
  ∀ (m : Nat), SourceAST.BooleanContinuation Γ m → InputNormalization.Input Γ m

/-- Full raw CPS law: every old Boolean reference is retained at its true
shift, and the returned root is actual most recent Boolean reference 0. -/
def BooleanTrace {Γ : List Ty} (q : Emit) (run : BooleanEmitter Γ) : Prop :=
  ∀ m : Nat, ∃ (Ξ : List Ty) (s : Renaming Γ Ξ) (n : Nat) (e : Fin m → Fin n) (root : Fin n),
    PrefixAt s q.2.1 ∧ (∀ i, (e i).val = i.val+q.2.2) ∧ root.val=0 ∧
    ∀ k : SourceAST.BooleanContinuation Γ m,
      encodeInput (run m k) = rowsBefore q.1 (encodeInput (k s e root))

private theorem tagMod (n t : Nat) (ht : t<8) : (8*n+t)%8=t := by omega
private theorem tagDiv (n t : Nat) (ht : t<8) : (8*n+t)/8=n := by omega

private theorem termPort {Γ Δ} (v : Port Γ) (r : Renaming Γ Δ) (off : Nat) (h : PrefixAt r off) :
    PrimitiveGate.encodePort (ExistentialPlan.portRename r v)=liftPort off (PrimitiveGate.encodePort v) := by
  cases v with
  | zero => rfl
  | var x =>
    simp only [PrimitiveGate.encodePort,ExistentialPlan.portRename,liftPort,Nat.add_one_ne_zero,
      if_false,h.2]
    omega

private theorem atomicTrace {Γ Δ : List Ty} (r : Renaming Γ Δ) (off : Nat) (hr : PrefixAt r off)
    (a b : SourceAST.Term Γ) (tag : Nat)
    (node : ∀ {Ξ n}, Port Ξ → Port Ξ → InputNormalization.Node Ξ n)
    (hout : ∀ {Ξ n} (u v : Port Ξ), encodeInputRow (node (n:=n) u v) =
      (tag,PrimitiveGate.encodePort u,PrimitiveGate.encodePort v)) :
    let A := emitTerm off (term a)
    let B := emitTerm (off+A.2.1) (term b)
    BooleanTrace (A.1++B.1++[noneStep tag (liftPort B.2.1 A.2.2) B.2.2],A.2.1+B.2.1,1)
      (fun _ k => SourceAST.emitRelation a b r node k) := by
  dsimp only
  let A := emitTerm off (term a)
  let B := emitTerm (off+A.2.1) (term b)
  obtain ⟨Ξ,s,u,hs,hu,ha⟩ := termTrace r a off hr
  obtain ⟨Ω,t,v,ht,hv,hb⟩ := termTrace (fun x => s (r x)) b (off+A.2.1) (prefixComp hr hs)
  intro m
  refine ⟨Ω,(fun x => t (s x)),m+1,Fin.succ,0,prefixComp hs ht,fun _ => rfl,rfl,?_⟩
  intro k
  unfold SourceAST.emitRelation
  rw [ha,hb]
  have hp := termPort u t B.2.1 ht
  rw [hu] at hp
  simp only [encodeInput,InputCompiler.prependStep,hout,hp,hv,rowsBefore,noneStep,
    List.append_assoc,List.cons_append,List.nil_append]

private theorem literalTrace (Γ : List Ty) (truth : Bool) :
    BooleanTrace (Γ:=Γ) ([noneStep (if truth then 0 else 2) 0 0],0,1)
      (fun m k => .boolean (if truth then .eq .zero .zero else .lt .zero .zero)
        (k (fun x => x) Fin.succ 0)) := by
  intro m
  refine ⟨Γ,(fun x => x),m+1,Fin.succ,0,prefixId Γ,fun _ => rfl,rfl,?_⟩
  intro k
  cases truth <;> rfl

private theorem unaryTrace {Γ Δ} (r : Renaming Γ Δ) (a : SourceAST.Formula Γ) (off : Nat)
    (ha : BooleanTrace (emitFormula off (formula a)) (fun _ k => a.emit r k)) :
    let A := emitFormula off (formula a)
    BooleanTrace (A.1++[noneStep 3 0 0],A.2.1,A.2.2+1) (fun _ k => (.neg a : SourceAST.Formula Γ).emit r k) := by
  dsimp only
  let A := emitFormula off (formula a)
  intro m
  obtain ⟨Ξ,s,n,e,root,hs,he,hroot,hcode⟩ := ha m
  refine ⟨Ξ,s,n+1,(fun i => (e i).succ),0,hs,?_,rfl,?_⟩
  · intro i
    change (e i).val+1=i.val+(A.2.2+1)
    rw [he]
    dsimp only [A]
    omega
  · intro k
    change encodeInput (a.emit r (fun s e root =>
      .boolean (.neg root) (k s (fun i => (e i).succ) 0))) = _
    rw [hcode]
    simp only [encodeInput,encodeInputRow,hroot,InputCompiler.prependStep,rowsBefore,noneStep,
      List.append_assoc,List.cons_append,List.nil_append]

private theorem binaryTrace {Γ Δ} (r : Renaming Γ Δ) (a b : SourceAST.Formula Γ)
    (off : Nat) (hr : PrefixAt r off) (isAnd : Bool)
    (ha : BooleanTrace (emitFormula off (formula a)) (fun _ k => a.emit r k))
    (hb : ∀ (Ξ : List Ty) (s : Renaming Γ Ξ) (o : Nat), PrefixAt s o →
      BooleanTrace (emitFormula o (formula b)) (fun _ k => b.emit s k)) :
    let A := emitFormula off (formula a)
    let B := emitFormula (off+A.2.1) (formula b)
    BooleanTrace (A.1++B.1++[noneStep (if isAnd then 4 else 5) B.2.2 0],A.2.1+B.2.1,A.2.2+B.2.2+1)
      (fun _ k => (if isAnd then .conj a b else .disj a b : SourceAST.Formula Γ).emit r k) := by
  dsimp only
  let A := emitFormula off (formula a)
  let B := emitFormula (off+A.2.1) (formula b)
  intro m
  obtain ⟨Ξ,s,n,e,left,hs,he,hl,hca⟩ := ha m
  obtain ⟨Ω,t,j,k,right,ht,hk,hright,hcb⟩ := hb Ξ (fun x => s (r x))
    (off+A.2.1) (prefixComp hr hs) n
  refine ⟨Ω,(fun x => t (s x)),j+1,(fun i => (k (e i)).succ),0,prefixComp hs ht,?_,rfl,?_⟩
  · intro i
    change (k (e i)).val+1=i.val+(A.2.2+B.2.2+1)
    rw [hk,he]
    dsimp only [A,B]
    omega
  · intro cont
    have hh : (k left).val=B.2.2 := by rw [hk,hl,Nat.zero_add]
    cases isAnd <;> simp only [Bool.false_eq_true,↓reduceIte,SourceAST.Formula.emit]
    all_goals
      rw [hca,hcb]
      simp only [encodeInput,encodeInputRow,hh,hright,InputCompiler.prependStep,rowsBefore,noneStep,
        List.append_assoc,List.cons_append,List.nil_append]

theorem formulaTrace {Γ Δ} (r : Renaming Γ Δ) (a : SourceAST.Formula Γ) (off : Nat)
    (hr : PrefixAt r off) : BooleanTrace (emitFormula off (formula a)) (fun _ k => a.emit r k) := by
  induction a generalizing Δ off with
  | truth =>
    rw [formula,emitFormula]
    exact literalTrace Δ true
  | falsity =>
    rw [formula,emitFormula]
    exact literalTrace Δ false
  | eq a b | le a b | lt a b =>
    rw [formula,emitFormula]
    simp only [eq,le,lt,atom,tagMod _ 2 (by decide),tagMod _ 3 (by decide),tagMod _ 4 (by decide),
      tagDiv _ 2 (by decide),tagDiv _ 3 (by decide),tagDiv _ 4 (by decide),Nat.unpair_pair,
      Nat.reduceLeDiff,Nat.reduceSub,↓reduceIte,SourceAST.Formula.emit]
    first
      | exact atomicTrace r off hr a b 0 (fun a b => .eq a b) (fun _ _ => rfl)
      | exact atomicTrace r off hr a b 1 (fun a b => .le a b) (fun _ _ => rfl)
      | exact atomicTrace r off hr a b 2 (fun a b => .lt a b) (fun _ _ => rfl)
  | neg a ih =>
    rw [formula,emitFormula]
    simp only [neg,tagMod _ 5 (by decide),tagDiv _ 5 (by decide),le_refl,↓reduceIte]
    exact unaryTrace r a off (ih r off hr)
  | conj a b ia ib | disj a b ia ib =>
    rw [formula,emitFormula]
    simp only [both,either,atom,tagMod _ 6 (by decide),tagMod _ 7 (by decide),
      tagDiv _ 6 (by decide),tagDiv _ 7 (by decide),Nat.unpair_pair,Nat.reduceLeDiff,
      reduceCtorEq,↓reduceIte,Nat.reduceSub]
    first
      | exact binaryTrace r a b off hr true (ia r off hr) (fun _ r' o hp => ib r' o hp)
      | exact binaryTrace r a b off hr false (ia r off hr) (fun _ r' o hp => ib r' o hp)

theorem exactInputCode {Γ} (a : SourceAST.Formula Γ) :
    inputCode (formula a)=encodeInput a.toInput := by
  obtain ⟨Ξ,s,n,e,root,hs,he,hroot,hex⟩ := formulaTrace (fun x => x) a 0 (prefixId Γ) 0
  unfold SourceAST.Formula.toInput
  rw [hex]
  simp only [encodeInput,hroot,inputCode,rowsBefore,List.append_nil]

theorem exactMatrixCodes : Targets.ExactMatrixCodes :=
  ⟨fun _ _ r t => termRename r t,fun _ _ r a => formulaRename r a,fun _ a => exactInputCode a⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
