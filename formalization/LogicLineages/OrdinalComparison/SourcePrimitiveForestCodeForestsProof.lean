module
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodePortsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Proof
open PrimitiveLowering ExistentialPlan

def lowerCodes {Γ} (es : List (Expr Γ×Expr Γ)) : List (Nat×Nat) :=
  es.map (fun e => (expressionCode e.1,expressionCode e.2))

theorem forest_lower {Γ} (g : Gate Γ) : forestCodes g=lowerCodes (lower g) := by
  simp only [forestCodes,forest,List.map_map,lowerCodes]
  apply List.map_congr_left
  intro e he
  change (SyntaxCode.encodeTerm e.1.graph.term,SyntaxCode.encodeTerm e.2.graph.term)=_
  rw [← (exactExpressions _ e.1).2,← (exactExpressions _ e.2).2]

theorem lift_port {Γ} (a : Port Γ) : portNumber (liftPort a)=shiftPort 9 (portNumber a) := by
  exact shift_port 9 a

theorem unused_correct {Γ} (start : Nat) : unusedPairs start=lowerCodes (unused (Γ:=Γ) start) := by
  have hr : (List.finRange 9).map Fin.val=List.range 9 := by
    apply List.ext_getElem <;> simp
  rw [unusedPairs,← hr,List.filter_map,List.map_map]
  unfold lowerCodes unused
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  change (portCode (i.val+1),1)=(portCode (portNumber (aux i)),portCode (portNumber (.zero : Port (Block Γ))))
  rw [aux_port]
  rfl

theorem addPairs_correct {Γ} (a b c d : Port Γ) :
    addPairs (portNumber a) (portNumber b) (portNumber c) (portNumber d)=
      lowerCodes (addEquations a b c d) := rfl

theorem lower_cons {Γ} (e : Expr Γ×Expr Γ) (es) :
    lowerCodes (e::es)=(expressionCode e.1,expressionCode e.2)::lowerCodes es := rfl

theorem lower_append {Γ} (es fs : List (Expr Γ×Expr Γ)) :
    lowerCodes (es++fs)=lowerCodes es++lowerCodes fs := List.map_append

theorem exactForests : Targets.ExactForests := by
  refine ⟨?_,?_,?_⟩
  · intro Γ a b
    rw [forest_lower]
    change _=lowerCodes ((Expr.port (liftPort a),Expr.port (liftPort b))::unused 0)
    rw [lower_cons,← unused_correct]
    simp only [eqForest,expressionCode,lift_port]
  · intro Γ a b c
    rw [forest_lower]
    change _=lowerCodes (addEquations (liftPort a) (liftPort b) (liftPort c) (aux 0)++unused 1)
    rw [lower_append,← addPairs_correct,← unused_correct]
    simp only [addForest,lift_port,aux_port,Fin.val_zero,Nat.zero_add]
  · intro Γ a
    rw [forest_lower]
    change _=lowerCodes ((Expr.successor (aux 0),Expr.identityZero)::
      (addEquations (liftPort a) (liftPort a) (aux 0) (aux 1)++unused 2))
    rw [lower_cons,lower_append,← addPairs_correct,← unused_correct]
    simp only [oneForest,expressionCode,lift_port,aux_port,Fin.val_zero,Fin.val_one,Nat.zero_add]
end LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Proof
