module
public import LogicLineages.OrdinalComparison.PositiveSourceDataProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PositiveSourceDomain

theorem flag_correct (p : Prop) [Decidable p] : (if p then (1:Nat) else 0)=1 ↔ p := by
  split_ifs <;> simp_all

theorem data_constant (n : Nat) : encodedPositiveSourceData (positiveExprEncode (.constant n))=(1,0) := by
  have hm : (4*n)%4=0 := by omega
  rw [data_equation]
  simp [positiveExprEncode,encodedPositiveSourceDataStep,hm]

theorem data_input : encodedPositiveSourceData (positiveExprEncode .input)=(1,1) := by
  rw [data_equation]
  rfl

theorem data_add (E F : FixedLimitPositiveExpr) :
    encodedPositiveSourceData (positiveExprEncode (.add E F))=
      (if (encodedPositiveSourceData (positiveExprEncode E)).1=1 ∧
          (encodedPositiveSourceData (positiveExprEncode F)).1=1 then 1 else 0,
       if (encodedPositiveSourceData (positiveExprEncode E)).2=1 ∨
          (encodedPositiveSourceData (positiveExprEncode F)).2=1 then 1 else 0) := by
  let a := positiveExprEncode E
  let b := positiveExprEncode F
  have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
  have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  dsimp only [a,b] at ha hb hm hd
  rw [data_equation]
  simp only [positiveExprEncode,encodedPositiveSourceDataStep,hm,hd,Nat.unpair_pair]
  norm_num only
  rw [table_correct _ _ ha,table_correct _ _ hb]
  simp only [if_true,if_false]

theorem data_head (rho : NONote) (E : FixedLimitPositiveExpr) :
    encodedPositiveSourceData (positiveExprEncode (.head rho E))=
      (if encodedPositiveHeadDomain (rawNoteEncode rho.1)=1 ∧
          (encodedPositiveSourceData (positiveExprEncode E)).1=1 then 1 else 0,
       (encodedPositiveSourceData (positiveExprEncode E)).2) := by
  let a := rawNoteEncode rho.1
  let b := positiveExprEncode E
  have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
  have hm : (4*Nat.pair a b+3)%4=3 := by omega
  have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
  dsimp only [a,b] at hb hm hd
  rw [data_equation]
  simp only [positiveExprEncode,encodedPositiveSourceDataStep,hm,hd,Nat.unpair_pair]
  norm_num only
  rw [table_correct _ _ hb]
  simp only [if_true,if_false]

private theorem input_or (p q : Bool) :
    (if (if p then (1:Nat) else 0)=1 ∨ (if q then (1:Nat) else 0)=1 then (1:Nat) else 0)=
      (if p || q then 1 else 0) := by
  cases p <;> cases q <;> rfl

theorem data_program : Targets.PositiveSourceDataProgram := by
  refine ⟨data_primitive,?_⟩
  intro E
  induction E with
  | constant n => simp [data_constant,fixedLimitProfileBelow,positiveExprHasInput]
  | input => simp [data_input,fixedLimitProfileBelow,positiveExprHasInput]
  | add E F ihE ihF =>
    simp only [data_add,fixedLimitProfileBelow,positiveExprHasInput]
    constructor
    · rw [flag_correct,ihE.1,ihF.1]
    · rw [ihE.2,ihF.2]
      exact input_or (positiveExprHasInput E) (positiveExprHasInput F)
  | head rho E ih =>
    simp only [data_head,fixedLimitProfileBelow,positiveExprHasInput]
    constructor
    · rw [flag_correct,head_domain.2 rho,ih.1,and_assoc]
    · exact ih.2

end LogicLineages.OrdinalComparison.PositiveSourceDomain
