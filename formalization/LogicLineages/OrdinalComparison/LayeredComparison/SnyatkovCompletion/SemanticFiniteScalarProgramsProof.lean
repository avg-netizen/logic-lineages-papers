module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseGraphProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarProgram
open SemanticFiniteScalar

/-- The conservative finite graph may also evaluate the FiniteCoefficientBaseProgram.left head-code branch
at a shift; that value is ignored. The actual coefficient program is used. -/
def compileAssemble (code : Nat) (xs : List (Option Nat)) : Option Nat :=
  if code % 4 = 0 then some code
  else if code % 4 = 1 then some code
  else if code % 4 = 2 then FiniteCoefficientBaseProgram.combine (fun a b => 4 * Nat.pair a b + 2) (xs.getD 0 none) (xs.getD 1 none)
  else FiniteCoefficientBaseProgram.combine FiniteCoefficientBase.Code.expand (SemanticCoefficient.Code.recognize (code / 4).unpair.1) (xs.getD 1 none)

theorem compile_equation (code : Nat) : Code.compile code =
    compileAssemble code ((FiniteCoefficientBaseProgram.children code).map Code.compile) := by
  rw [Code.compile]
  unfold compileAssemble FiniteCoefficientBaseProgram.children FiniteCoefficientBaseProgram.combine
  split_ifs <;> simp_all

private theorem computable_ite {A B : Type} [Primcodable A] [Primcodable B]
    {p : A → Prop} [DecidablePred p] {f g : A → B}
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  apply (Computable.cond hp hf hg).of_eq
  intro a
  by_cases h : p a <;> simp [h]

attribute [local irreducible] Nat.sqrt Nat.unpair

theorem compile_assemble_computable : Computable₂ compileAssemble := by
  let A := Nat × List (Option Nat)
  have h0 : Computable (fun p : A => p.2.getD 0 none) :=
    ((Primrec.list_getD none).comp Primrec.snd (Primrec.const 0)).to_comp
  have h1 : Computable (fun p : A => p.2.getD 1 none) :=
    ((Primrec.list_getD none).comp Primrec.snd (Primrec.const 1)).to_comp
  have ha : Computable (fun p : A => FiniteCoefficientBaseProgram.combine (fun a b => 4 * Nat.pair a b + 2) (p.2.getD 0 none) (p.2.getD 1 none)) :=
    (FiniteCoefficientBaseProgram.combine_primitive _ (SourceBooleanProgramsProof.binary_primitive 4 2)).to_comp.comp h0 h1
  have hs : Computable (fun p : A => FiniteCoefficientBaseProgram.combine FiniteCoefficientBase.Code.expand (SemanticCoefficient.Code.recognize (p.1 / 4).unpair.1) (p.2.getD 1 none)) :=
    (FiniteCoefficientBaseProgram.combine_primitive _ FiniteCoefficientBaseProgram.expand_primitive).to_comp.comp
      (SemanticCoefficientProof.actualNumericProgram.to_comp.comp (FiniteCoefficientBaseProgram.left.to_comp.comp Computable.fst)) h1
  exact computable_ite (Primrec.eq.comp (FiniteCoefficientBaseProgram.tag.comp Primrec.fst) (Primrec.const 0)).decide.to_comp
    (Computable.option_some.comp Computable.fst)
    (computable_ite (Primrec.eq.comp (FiniteCoefficientBaseProgram.tag.comp Primrec.fst) (Primrec.const 1)).decide.to_comp
      (Computable.option_some.comp Computable.fst)
      (computable_ite (Primrec.eq.comp (FiniteCoefficientBaseProgram.tag.comp Primrec.fst) (Primrec.const 2)).decide.to_comp ha hs))

theorem compile_computable : Computable Code.compile :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph Nat (Option Nat) FiniteCoefficientBaseProgram.children compileAssemble id
    FiniteCoefficientBaseProgram.children_primitive.to_comp compile_assemble_computable Computable.id
    Code.compile FiniteCoefficientBaseProgram.decreasing compile_equation).2

theorem actualNumericProgram : SemanticFiniteScalarTargets.ActualNumericProgram := compile_computable

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarProgram
