module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
/-- Literal raw decoded recurrence of the actual assembled AST, all child
outputs and counts. It does not replace malformed codes with semantic formulas. -/
def NativeRaw : Prop := ∀ m (f : Program m) (g : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 target (inputs : List.Vector Nat m) counter,
 evaluate (program f g B G) (target ::ᵥ counter ::ᵥ inputs) =
 CurrentRecursionAccumulator.rawNumber
  (fun k => evaluate (CurrentCalculationFormulaProgram.program (.recursion f g)) (target ::ᵥ k ::ᵥ inputs))
  (fun k => evaluate (CurrentRecursionStepProgram.program f g G) (target ::ᵥ k ::ᵥ inputs))
  (evaluate (CurrentRecursionBaseProgram.program f B) (target ::ᵥ inputs)) counter
/-- Original formula and certificate recipes, obtained from actual concrete AST
calibrations; no supplied calibration or certificate-correctness hypothesis. -/
def NativeOriginal : Prop := ∀ m (f : Program m) (g : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 target (inputs : List.Vector Nat m) counter,
 evaluate (program f g B G) (target ::ᵥ counter ::ᵥ inputs) = originalNumber f g B G target inputs counter
/-- Arbitrary-symbolic graph, not just numeral evaluation. The public wrapper
uses the SAME target parameter at zero, successor, formula, step and prior call.
Source existence and new-root CORE correctness are deliberately not asserted. -/
def InternalGraph : Prop := ∀ arity (p : Program arity) m (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)), ∀ N : GraphNodes p f g B G,
 ∀ ctx (target counter : Term ctx) (inputs : List.Vector (Term ctx) m),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj
   (.equal (call N.publicTag (target ::ᵥ .zero ::ᵥ inputs)) (call N.baseTag (target ::ᵥ inputs)))
   (.equal (call N.publicTag (target ::ᵥ .succ counter ::ᵥ inputs))
    (LiteralMPRun.certificate N.mpTag .zero
     (call N.formulaTag (target ::ᵥ .succ counter ::ᵥ inputs))
     (call N.stepTag (target ::ᵥ counter ::ᵥ inputs))
     (call N.publicTag (target ::ᵥ counter ::ᵥ inputs))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.Targets
