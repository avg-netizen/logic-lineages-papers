module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.LeftRightGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.QuoteGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence FixedFormulaSubstitution GorbowRegistryTuple
open SixSol20261112.Fuel NamedArithmeticGraph
open EncodingSupport

theorem normalized {arity n inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (t : Term n) (raw : Fin n → Program inputs) (rv : List.Vector (Term ctx) n) (v : Term ctx)
 (hr : ∀ i, Computes p (raw i) args (rv.get i))
 (hv : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment n) rv t) v))) :
 Computes p (termQuote t raw) args v := by
 intro tag ht
 obtain ⟨hg⟩ := CurrentRecursionBaseProgram.GraphInputs.termQuoteGraph p args t raw rv J.ctag J.atag hc ha hr tag ht
 obtain ⟨hv⟩ := hv
 exact ⟨Logic.trans _ _ _ hg hv⟩

theorem prior {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (I : Installation p base step child J) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let cn := LiteralNumeralPrefix.numeralCall J.ntag counter
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)
 Computes p (termQuote (priorTemplate m) (CurrentRecursionBaseProgram.rootArguments (m+1)))
  (target ::ᵥ counter ::ᵥ inputs) (callValue K target (cn ::ᵥ nums)) := by
 exact normalized p _ J I.hc I.ha _ _ _ _
  (CurrentRecursionBaseProgram.GraphInputs.rootArgs p (baseTags J) I.hn target (counter ::ᵥ inputs))
  (TemplateGraph.prior p J I.hc I.ha target counter inputs)

theorem next {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (I : Installation p base step child J) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let cn := LiteralNumeralPrefix.numeralCall J.ntag counter
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)
 Computes p (termQuote (nextTemplate m) (CurrentRecursionBaseProgram.rootArguments (m+1)))
  (target ::ᵥ counter ::ᵥ inputs) (callValue K target (LiteralNumeralPrefix.numeralCall J.ntag (.succ counter) ::ᵥ nums)) := by
 exact normalized p _ J I.hc I.ha _ _ _ _
  (CurrentRecursionBaseProgram.GraphInputs.rootArgs p (baseTags J) I.hn target (counter ::ᵥ inputs))
  (TemplateGraph.next p J I.hc I.ha I.hn target counter inputs)

theorem left {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (I : Installation p base step child J) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) (offset : Nat) :
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let cn := LiteralNumeralPrefix.numeralCall J.ntag counter
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)
 Computes p (termQuote (leftTemplate m offset) (CurrentRecursionBaseProgram.rootArguments (m+1)))
  (target ::ᵥ counter ::ᵥ inputs) (callValue K (shiftTerm offset target) (cn ::ᵥ callValue K target (cn ::ᵥ nums) ::ᵥ nums)) := by
 exact normalized p _ J I.hc I.ha _ _ _ _
  (CurrentRecursionBaseProgram.GraphInputs.rootArgs p (baseTags J) I.hn target (counter ::ᵥ inputs))
  (LeftRightGraph.left p J I.hc I.ha I.hn target counter inputs offset)

theorem rightTemplateEq (m offset : Nat) :
 rightTemplate m offset = CurrentRecursionBaseProgram.openCall (shiftTerm offset (.var (Fin.last (m+2))))
  (List.Vector.ofFn (fun i : Fin (m+2) => .var i.castSucc)) := by
 unfold rightTemplate
 congr 1
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => cases i using Fin.cases with
   | zero => rfl
   | succ i => rfl

theorem right {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (I : Installation p base step child J) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) (offset : Nat) :
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let previous := call J.qtag (counter ::ᵥ inputs)
 Computes p (termQuote (rightTemplate m offset) (rightArguments base step)) (target ::ᵥ counter ::ᵥ inputs)
  (callValue K (shiftTerm offset target)
   (LiteralNumeralPrefix.numeralCall J.ntag counter ::ᵥ LiteralNumeralPrefix.numeralCall J.ntag previous ::ᵥ
    inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))) := by
 apply normalized p _ J I.hc I.ha _ _ (EvaluatorGraph.rightValues J target counter inputs) _
  (EvaluatorGraph.rightArgsGraph p base step child J I target counter inputs)
 rw [rightTemplateEq]
 exact LeftRightGraph.shiftedArguments p J I.hc I.ha I.hn target
  (counter ::ᵥ call J.qtag (counter ::ᵥ inputs) ::ᵥ inputs) offset

theorem unary {arity m ctx : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (I : Installation p base step child J) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) (offset : Nat) :
 Computes p (unaryCode m offset) (target ::ᵥ counter ::ᵥ inputs)
  (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.headEnvironment (m+2))
   (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (unaryTemplate m offset)) := by
 intro tag ht
 let args := target ::ᵥ counter ::ᵥ inputs
 let rv := CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)
 obtain ⟨he⟩ := Equations.compositionValues p tag _ _ ht args rv
  (fun i => CurrentRecursionBaseProgram.GraphInputs.rootArgs p (baseTags J) I.hn target (counter ::ᵥ inputs) i _
   (Equations.argumentChild p tag _ _ ht i))
 obtain ⟨hf⟩ := FixedFormulaSubstitution.StatementChecks.exactInternalTerm (m+3) 1 (m+2) _ (unaryTemplate m offset)
  arity p (tag+1) J.ctag J.atag (Equations.functionChild p tag _ _ ht) I.hc I.ha ctx rv
 exact ⟨Logic.trans _ _ _ he hf⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.QuoteGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.QuoteGraph
