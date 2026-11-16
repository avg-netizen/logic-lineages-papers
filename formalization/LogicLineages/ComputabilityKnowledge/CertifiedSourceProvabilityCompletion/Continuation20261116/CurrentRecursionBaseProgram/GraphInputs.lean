module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphPrimitives
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphInputs
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem oneEq {arity : Nat} (f : Program 1) (a : Program arity) :
 HistoryRuleSuffix.applyOne f a = .composition f (fun _ => a) := by
 unfold HistoryRuleSuffix.applyOne
 congr 1
 funext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => exact Fin.elim0 i

theorem rootArgs {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin (m+1)) :
 Computes p (rootArguments m i) (target ::ᵥ inputs) ((rawValues J target inputs).get i) := by
 simp only [rawValues,List.Vector.get_ofFn]
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp only [rootArguments,Fin.lastCases_last]
   exact unary p _ LiteralNumeralPrefix.numeralCode J.ntag hn (.projection 0) target (projection p _ 0)
 · simp only [rootArguments,rawInputs,Fin.lastCases_castSucc]
   exact unary p _ LiteralNumeralPrefix.numeralCode J.ntag hn (.projection j.succ) (inputs.get j) (projection p _ j.succ)

theorem childCall {arity m ctx : Nat} (p : Program arity) (child : Program (m+1)) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨m+1,child⟩) (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (.composition child (childArguments m)) (target ::ᵥ inputs) (call ctag (.succ target ::ᵥ inputs)) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition p _ child ctag hc _ (.succ target ::ᵥ inputs)
 intro i
 cases i using Fin.cases with
 | zero =>
  change Computes p (HistoryRuleSuffix.applyOne .succ (.projection 0)) _ (.succ target)
  rw [oneEq]
  exact CurrentRecursionAccumulator.GraphSupport.successorProjection p _ 0
 | succ i => exact projection p _ i.succ

theorem termQuoteGraph {arity inputs n ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (t : Term n) (raw : Fin n → Program inputs) (rv : List.Vector (Term ctx) n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hr : ∀ i, Computes p (raw i) args (rv.get i)) :
 Computes p (.composition (FixedFormulaSubstitution.termProgram (PrescribedRuntimeSpecialization.runtimeEnvironment n) t) raw) args
  (FixedFormulaSubstitution.termValue ctag atag (PrescribedRuntimeSpecialization.runtimeEnvironment n) rv t) := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues p tag _ raw ht args rv
  (fun i => hr i _ (Equations.argumentChild p tag _ raw ht i))
 obtain ⟨hf⟩ := FixedFormulaSubstitution.StatementChecks.exactInternalTerm n 0 n _ t arity p (tag+1) ctag atag
  (Equations.functionChild p tag _ raw ht) hc ha ctx rv
 exact ⟨Logic.trans _ _ _ he hf⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphInputs
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphInputs
