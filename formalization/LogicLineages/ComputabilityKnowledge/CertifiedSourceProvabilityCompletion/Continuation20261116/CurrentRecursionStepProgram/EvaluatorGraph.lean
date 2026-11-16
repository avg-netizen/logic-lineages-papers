module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EvaluatorGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem successorGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (a : Program inputs) (av : Term ctx) (ha : Computes p a args av) :
 Computes p (HistoryRuleSuffix.applyOne .succ a) args (.succ av) := by
 intro tag ht
 have heq := CurrentRecursionBaseProgram.GraphInputs.oneEq (.succ) a
 rw [heq] at ht
 obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag .succ (fun _ => a) ht args av
  (ha _ (Equations.argumentChild p tag .succ (fun _ => a) ht 0))
 obtain ⟨hs⟩ := Support.intoRegistry p .succ (tag+1) (Equations.functionChild p tag .succ (fun _ => a) ht) _
  (NamedArithmeticGraph.Equations.successor (tag+1) ctx (av ::ᵥ nil))
 exact ⟨Logic.trans _ _ _ he hs⟩

theorem shiftGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (offset : Nat) (a : Program inputs) (av : Term ctx) (ha : Computes p a args av) :
 Computes p (shiftProgram offset a) args (shiftTerm offset av) := by
 induction offset with
 | zero => exact ha
 | succ n ih => exact successorGraph p args (shiftProgram n a) (shiftTerm n av) ih

theorem previousGraph {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2))
 (qtag : Nat) (hq : (nodes p)[qtag]? = some ⟨m+1,Program.recursion base step⟩)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (previous base step) (target ::ᵥ counter ::ᵥ inputs) (call qtag (counter ::ᵥ inputs)) :=
 CurrentCalculationFormulaProgram.GraphProof.tailCall p _ qtag hq target (counter ::ᵥ inputs)

theorem stepArgsGraph {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2))
 (qtag : Nat) (hq : (nodes p)[qtag]? = some ⟨m+1,Program.recursion base step⟩)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin (m+2)) :
 Computes p (stepArguments base step i) (target ::ᵥ counter ::ᵥ inputs)
  ((counter ::ᵥ call qtag (counter ::ᵥ inputs) ::ᵥ inputs).get i) := by
 cases i using Fin.cases with
 | zero => exact projection p _ 1
 | succ i => cases i using Fin.cases with
   | zero => exact previousGraph p base step qtag hq target counter inputs
   | succ i => exact projection p _ i.succ.succ

theorem resultGraph {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (J : Tags)
 (hq : (nodes p)[J.qtag]? = some ⟨m+1,Program.recursion base step⟩)
 (hs : (nodes p)[J.stepTag]? = some ⟨m+2,step⟩)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (result base step) (target ::ᵥ counter ::ᵥ inputs)
  (call J.stepTag (counter ::ᵥ call J.qtag (counter ::ᵥ inputs) ::ᵥ inputs)) :=
 CurrentRecursionAccumulator.GraphSupport.composition p _ step J.stepTag hs _ _
  (stepArgsGraph p base step J.qtag hq target counter inputs)

theorem childGraph {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (I : Installation p base step child J) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (.composition child (childArguments base step)) (target ::ᵥ counter ::ᵥ inputs)
  (call J.childTag (shiftTerm (GorbowPRChildTags.stepTag base) target ::ᵥ counter ::ᵥ call J.qtag (counter ::ᵥ inputs) ::ᵥ inputs)) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition p _ child J.childTag I.hchild _ _
 intro i
 cases i using Fin.cases with
 | zero => exact shiftGraph p _ (GorbowPRChildTags.stepTag base) (.projection 0) target (projection p _ 0)
 | succ i => exact stepArgsGraph p base step J.qtag I.hq target counter inputs i

def rightValues {m ctx : Nat} (J : Tags) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) : List.Vector (Term ctx) (m+3) :=
 CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ call J.qtag (counter ::ᵥ inputs) ::ᵥ inputs)
theorem rightArgsGraph {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (I : Installation p base step child J) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin (m+3)) :
 Computes p (rightArguments base step i) (target ::ᵥ counter ::ᵥ inputs) ((rightValues J target counter inputs).get i) := by
 simp only [rightValues,CurrentRecursionBaseProgram.rawValues,List.Vector.get_ofFn,baseTags]
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp only [rightArguments,Fin.lastCases_last]
   exact unary p _ LiteralNumeralPrefix.numeralCode J.ntag I.hn (.projection 0) target (projection p _ 0)
 · simp only [rightArguments,Fin.lastCases_castSucc]
   cases j using Fin.cases with
   | zero => exact unary p _ LiteralNumeralPrefix.numeralCode J.ntag I.hn (.projection 1) counter (projection p _ 1)
   | succ j => cases j using Fin.cases with
     | zero => exact unary p _ LiteralNumeralPrefix.numeralCode J.ntag I.hn (previous base step) _ (previousGraph p base step J.qtag I.hq target counter inputs)
     | succ j => exact unary p _ LiteralNumeralPrefix.numeralCode J.ntag I.hn (.projection j.succ.succ) _ (projection p _ j.succ.succ)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EvaluatorGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EvaluatorGraph
