module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TagSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativeInputs
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof GorbowFormulaSubstitution PrescribedRuntimeEquality
open GorbowSubstitution

theorem rootArgumentsEval (m target : Nat) (inputs : List.Vector Nat m) (i : Fin (m+1)) :
 evaluate (rootArguments m i) (target ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (TagSyntax.join target (fun j => Term.numeral (inputs.get j)) i)) := by
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp only [rootArguments,Fin.lastCases_last,TagSyntax.join,oneEval,projectionEval,List.Vector.get_cons_zero]
   exact LiteralNumeralPrefix.StatementChecks.exactNative target
 · simp only [rootArguments,rawInputs,Fin.lastCases_castSucc,TagSyntax.join,oneEval,projectionEval,List.Vector.get_cons_succ]
   exact LiteralNumeralPrefix.StatementChecks.exactNative (inputs.get j)

theorem childEval {m : Nat} (child : Program (m+1)) (target : Nat) (inputs : List.Vector Nat m) :
 evaluate (.composition child (childArguments m)) (target ::ᵥ inputs) = evaluate child ((target+1) ::ᵥ inputs) := by
 change evaluate child _ = _
 congr 1
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => simp [childArguments,evaluate]

theorem instantiatedRoot (m target : Nat) (inputs : List.Vector Nat m) :
 substituteFormula (TagSyntax.join target (fun j => Term.numeral (inputs.get j))) (rootTemplate m) =
 (.equal (call target (.zero ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs))
  (call (target+1) (GorbowPRNumeralCalculation.numeralArguments inputs))) := by
 rw [← TagSyntax.formulaFull,TagSyntax.root]
 have ha : (argumentVariables m).map (substitute (fun j => Term.numeral (inputs.get j))) = GorbowPRNumeralCalculation.numeralArguments inputs := by
  ext i
  simp [argumentVariables,substitute,GorbowPRNumeralCalculation.numeralArguments]
 simp only [CurrentRecursionBaseCertificate.rootFormula,substituteFormula,SixSol20261112.Fuel.Logic.substCall,
  List.Vector.map_cons,substitute,ha]

theorem quoteTerms {n arity : Nat} (t : Term n) (raw : Fin n → Program arity) (v : List.Vector Nat arity)
 (sigma : Fin n → Term 0) (h : ∀ i, evaluate (raw i) v = Encodable.encode (GorbowTermPrefixCode.encode (sigma i))) :
 evaluate (.composition (FixedFormulaSubstitution.termProgram (PrescribedRuntimeSpecialization.runtimeEnvironment n) t) raw) v =
 Encodable.encode (GorbowTermPrefixCode.encode (substitute sigma t)) := by
 have hv : (List.Vector.ofFn fun i => evaluate (raw i) v) = FixedFormulaSubstitution.rawInputs sigma := by
  ext i
  simpa only [List.Vector.get_ofFn,FixedFormulaSubstitution.rawInputs] using h i
 change evaluate (FixedFormulaSubstitution.termProgram _ t) _ = _
 rw [hv,FixedFormulaSubstitution.StatementChecks.exactNativeTerm,PrescribedRuntimeSpecialization.TraceSupportProof.assignmentRuntime]

theorem parentChild (m target : Nat) (inputs : List.Vector Nat m) :
 evaluate (parentCode m) (target ::ᵥ inputs) = Encodable.encode (GorbowTermPrefixCode.encode
  (call target (.zero ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs))) ∧
 evaluate (childCode m) (target ::ᵥ inputs) = Encodable.encode (GorbowTermPrefixCode.encode
  (call (target+1) (GorbowPRNumeralCalculation.numeralArguments inputs))) := by
 have he := instantiatedRoot m target inputs
 change Formula.equal _ _ = Formula.equal _ _ at he
 have hl := (Formula.equal.inj he).1
 have hr := (Formula.equal.inj he).2
 constructor
 · unfold parentCode
   rw [quoteTerms _ _ _ _ (rootArgumentsEval m target inputs),hl]
 · unfold childCode
   rw [quoteTerms _ _ _ _ (rootArgumentsEval m target inputs),hr]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativeInputs
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativeInputs
