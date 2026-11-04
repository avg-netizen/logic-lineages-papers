module
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeTargets
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Proof
open PrimitiveLowering ExistentialPlan

theorem port_correct {Γ} (a : Port Γ) : portCode (portNumber a)=SyntaxCode.encodeTerm a.term := by
  cases a <;> simp [portCode,portNumber,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,SourceAdditionCompletion.Atom.term]

theorem shift_index {Γ τ} (k : Nat) (x : Variable Γ τ) :
    SourceTypedPorts.variableIndex (shift k x)=SourceTypedPorts.variableIndex x+k := by
  induction k with
  | zero => simp [shift]
  | succ k ih => simp [shift,SourceTypedPorts.variableIndex,ih,Nat.add_assoc]

theorem shift_port {Γ} (k : Nat) (a : Port Γ) :
    portNumber (portRename (shift k) a)=shiftPort k (portNumber a) := by
  cases a <;> simp [portRename,portNumber,shiftPort,shift_index,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem fresh_index {Γ} : ∀ (n : Nat) (i : Fin n),
    SourceTypedPorts.variableIndex (fresh (Γ:=Γ) i)=i.val := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrArg (fun z => z+1) (ih j)

theorem aux_port {Γ} (i : Fin 9) : portNumber (aux (Γ:=Γ) i)=i.val+1 := by
  exact congrArg (fun z => z+1) (fresh_index 9 i)

theorem exactPorts : Targets.ExactPorts := ⟨fun _ a => port_correct a,fun _ k a => shift_port k a,fun _ i => aux_port i⟩

theorem expression_correct {Γ} (e : Expr Γ) : expressionCode e=SyntaxCode.encodeTerm e.term := by
  cases e with
  | port a => exact port_correct a
  | successor a =>
    change 8*Nat.pair 2 (portCode (portNumber a))+5=8*Nat.pair 2 (SyntaxCode.encodeTerm a.term)+5
    rw [port_correct]
  | erase a b =>
    change SourceGammaAggregateCode.eraserCode (portCode (portNumber a)) (portCode (portNumber b)) = _
    rw [port_correct,port_correct]
    exact (SourceGammaAggregateCode.Proof.exactLiteralCodes Γ a.term b.term).1
  | identityZero => rfl

theorem exactExpressions : Targets.ExactExpressions := by
  intro Γ e
  exact ⟨expression_correct e,by rw [(PrimitiveLowering.Proof.primitiveRealization Γ e).1]; exact expression_correct e⟩
end LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Proof
