module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixRenameProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
open LogicLineages.OrdinalComparison.Source
open PrimitiveLowering RawSourceDAG
open RawSourceDAG.InputCompiler (InputCode InputStep encodeInput)

/-- Literal positional record for the actual fresh-natural-variable prefix. -/
def PrefixAt {Γ Δ : List Ty} (r : Renaming Γ Δ) (off : Nat) : Prop :=
  Δ.map SyntaxCode.typeCode = List.replicate off 0 ++ Γ.map SyntaxCode.typeCode ∧
  ∀ {σ} (x : Variable Γ σ), variableIndex (r x) = off+variableIndex x

theorem prefixId (Γ : List Ty) : PrefixAt (fun {σ} (x : Variable Γ σ) => x) 0 := by
  exact ⟨rfl,fun x => (Nat.zero_add _).symm⟩

theorem prefixOne (Γ : List Ty) : PrefixAt (Renaming.weaken Γ .ground) 1 := by
  exact ⟨rfl,fun x => Nat.add_comm _ _⟩

theorem prefixComp {Γ Δ Ξ} {r : Renaming Γ Δ} {s : Renaming Δ Ξ} {u v : Nat}
    (hr : PrefixAt r u) (hs : PrefixAt s v) : PrefixAt (fun x => s (r x)) (u+v) := by
  constructor
  · rw [hs.1,hr.1,← List.append_assoc,← List.replicate_add,Nat.add_comm v u]
  · intro σ x
    rw [hs.2,hr.2]
    omega

theorem actualLift {Γ Δ σ} (r : Renaming Γ Δ) (off : Nat) (h : PrefixAt r off)
    (d : GroundEquivalence.Input Γ σ) :
    CurrentDecisionEmitter.liftCode off (encode ⟨Γ,σ,d⟩) =
      encode ⟨Δ,σ,ScopedDAG.renameInput r d⟩ := by
  have hTab : RawSourceDAG.BinaryPlanCompiler.prefixTable off (Γ.map SyntaxCode.typeCode) =
      RawSourceDAG.Operations.renamingCode r := by
    unfold RawSourceDAG.BinaryPlanCompiler.prefixTable
    rw [List.length_map]
    exact tableByIndex r (fun i => i+off) (fun x => (Nat.add_comm _ _).trans (h.2 x).symm)
  rw [RawSourceDAG.Operations.rename_input]
  simp only [CurrentDecisionEmitter.liftCode,RawSourceDAG.encode,hTab,h.1]

def rowsBefore (rows : List InputStep) (p : InputCode) : InputCode := (rows++p.1,p.2)

@[simp] theorem rowsEmpty (p : InputCode) : rowsBefore [] p = p := rfl
@[simp] theorem rowsCompose (a b : List InputStep) (p : InputCode) :
    rowsBefore a (rowsBefore b p) = rowsBefore (a++b) p := by simp [rowsBefore,List.append_assoc]

private theorem codePort {Γ Δ} (v : Port Γ) (r : Renaming Γ Δ) (off : Nat) (h : PrefixAt r off) :
    RawSourceDAG.PrimitiveGate.encodePort (ExistentialPlan.portRename r v) =
      liftPort off (RawSourceDAG.PrimitiveGate.encodePort v) := by
  cases v with
  | zero => rfl
  | var x =>
    simp only [RawSourceDAG.PrimitiveGate.encodePort, ExistentialPlan.portRename,liftPort,
      Nat.add_one_ne_zero,if_false,h.2]
    omega

private theorem tagMod (n t : Nat) (ht : t<8) : (8*n+t)%8=t := by omega
private theorem tagDiv (n t : Nat) (ht : t<8) : (8*n+t)/8=n := by omega

/-- Split one actual source term's CPS input emission from its continuation.
Result position and natural/Boolean context changes are not forgotten. -/
def TermTrace {Γ Δ : List Ty} (r : Renaming Γ Δ) (a : SourceAST.Term Γ) (offset : Nat) : Prop :=
  let q := emitTerm offset (term a)
  ∃ (Ξ : List Ty) (s : Renaming Δ Ξ) (v : Port Ξ),
    PrefixAt s q.2.1 ∧ RawSourceDAG.PrimitiveGate.encodePort v = q.2.2 ∧
    ∀ (m : Nat) (k : SourceAST.Continuation Δ m),
      encodeInput (a.emit r k) = rowsBefore q.1 (encodeInput (k s v))

theorem termTrace {Γ Δ} (r : Renaming Γ Δ) (a : SourceAST.Term Γ) (off : Nat)
    (hr : PrefixAt r off) : TermTrace r a off := by
  induction a generalizing Δ off with
  | var x =>
    have h : emitTerm off (term (.var x))=([],0,variableIndex x+off+1) := by
      rw [term,emitTerm]
      simp only [var,show 8*variableIndex x%8=0 from tagMod _ 0 (by decide),
        show 8*variableIndex x/8=variableIndex x from tagDiv _ 0 (by decide),↓reduceIte]
    unfold TermTrace
    rw [h]
    refine ⟨Δ,(fun z => z),.var (r x),prefixId Δ,?_,?_⟩
    · simp only [PrimitiveGate.encodePort,hr.2]
      omega
    · intro m k
      rfl
  | literal n =>
    have h : emitTerm off (term (.literal n : SourceAST.Term Γ))=([noneStep 7 n 0],1,1) := by
      rw [term,emitTerm]
      simp only [lit,tagMod _ 1 (by decide),tagDiv _ 1 (by decide),reduceCtorEq,false_or,↓reduceIte]
    unfold TermTrace
    rw [h]
    exact ⟨.ground::Δ,Renaming.weaken Δ .ground,.var .here,prefixOne Δ,rfl,fun _ _ => rfl⟩
  | observation d =>
    have h : emitTerm off (term (.observation d))=([sourceStep 8 0 (encode ⟨Δ,.ground,
        ScopedDAG.renameInput r d⟩)],1,1) := by
      rw [term,emitTerm]
      simp only [observe,tagMod _ 3 (by decide),tagDiv _ 3 (by decide),reduceCtorEq,
        or_self,↓reduceIte,literalPayload,actualLift r off hr]
    unfold TermTrace
    rw [h]
    exact ⟨.ground::Δ,Renaming.weaken Δ .ground,.var .here,prefixOne Δ,rfl,fun _ _ => rfl⟩
  | add a b ia ib =>
    let A := emitTerm off (term a)
    let B := emitTerm (off+A.2.1) (term b)
    obtain ⟨Ξ,s,v,hs,hv,ea⟩ := ia r off hr
    let r' : Renaming Γ Ξ := fun x => s (r x)
    obtain ⟨Ω,t,w,ht,hw,eb⟩ := ib r' (off+A.2.1) (prefixComp hr hs)
    let R : Renaming Δ (.ground::Ω) := fun x => .there (t (s x))
    have e : emitTerm off (term (.add a b)) =
        (A.1++B.1++[noneStep 6 (liftPort B.2.1 A.2.2) B.2.2],A.2.1+B.2.1+1,1) := by
      rw [term,emitTerm]
      simp only [add,tagMod _ 2 (by decide),tagDiv _ 2 (by decide),Nat.unpair_pair,reduceCtorEq,
        true_or,↓reduceIte,A,B]
    unfold TermTrace
    rw [e]
    refine ⟨.ground::Ω,R,.var .here,prefixComp (prefixComp hs ht) (prefixOne Ω),rfl,?_⟩
    intro m k
    change encodeInput (a.emit r (fun s av => b.emit (fun x => s (r x)) fun t bv =>
      .add (ExistentialPlan.portRename t av) bv (k (fun x => .there (t (s x))) (.var .here)))) = _
    rw [ea,eb]
    have hport := codePort v t B.2.1 ht
    rw [hv] at hport
    change rowsBefore A.1 (rowsBefore B.1 (rowsBefore [noneStep 6
      (PrimitiveGate.encodePort (ExistentialPlan.portRename t v))
      (PrimitiveGate.encodePort w)] (encodeInput (k R (.var .here))))) = _
    rw [hport,hw,rowsCompose,rowsCompose]
  | unary h a ih =>
    let A := emitTerm off (term a)
    obtain ⟨Ξ,s,v,hs,hv,ea⟩ := ih r off hr
    let R : Renaming Δ (.ground::.ground::Ξ) := fun x => .there (.there (s x))
    have e : emitTerm off (term (.unary h a)) =
        (A.1++[noneStep 6 A.2.2 0,sourceStep 9 0 (encode ⟨[],.arrow .ground .ground,h⟩)],A.2.1+2,1) := by
      rw [term,emitTerm]
      simp only [unary,tagMod _ 4 (by decide),tagDiv _ 4 (by decide),Nat.unpair_pair,reduceCtorEq,
        false_or,↓reduceIte,literalPayload,A]
    unfold TermTrace
    rw [e]
    refine ⟨.ground::.ground::Ξ,R,.var .here,?_,rfl,?_⟩
    · simpa only [Nat.add_assoc] using prefixComp (prefixComp hs (prefixOne Ξ)) (prefixOne (.ground::Ξ))
    · intro m k
      change encodeInput (a.emit r (fun s av => .add av .zero (.unary h .here
        (k (fun x => .there (.there (s x))) (.var .here))))) = _
      rw [ea]
      change rowsBefore A.1 (rowsBefore [noneStep 6 (PrimitiveGate.encodePort v) 0,
        sourceStep 9 0 (encode ⟨[],.arrow .ground .ground,h⟩)] (encodeInput (k R (.var .here)))) = _
      rw [hv,rowsCompose]

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
