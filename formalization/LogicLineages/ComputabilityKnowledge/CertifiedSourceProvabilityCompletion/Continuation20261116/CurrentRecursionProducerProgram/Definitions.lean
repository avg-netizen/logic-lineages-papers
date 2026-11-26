module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
/-- Explicit swap of first two coordinates, preserving all remaining inputs. -/
def swapInputs (m : Nat) : Fin (m+2) → Program (m+2) :=
 Fin.cases (.projection 1) (Fin.cases (.projection 0) (fun i => .projection i.succ.succ))
def swap {m : Nat} (q : Program (m+2)) : Program (m+2) := .composition q (swapInputs m)
/-- Formula/step receive target,counter,inputs; recursion needs counter,target,inputs. -/
def formula {m : Nat} (f : Program m) (g : Program (m+2)) : Program (m+2) :=
 swap (CurrentCalculationFormulaProgram.program (.recursion f g))
def step {m : Nat} (f : Program m) (g : Program (m+2)) (G : Program (m+3)) : Program (m+2) :=
 swap (CurrentRecursionStepProgram.program f g G)
/-- B and G are actual child ASTs, never arbitrary chosen certificates. -/
def accumulator {m : Nat} (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) : Program (m+2) :=
 CurrentRecursionAccumulator.producer (CurrentRecursionBaseProgram.program f B) (formula f g) (step f g G)
/-- Public interface is again target,counter,inputs. The target remains fixed
throughout the recursion and the prior accumulator is join's projection1. -/
def program {m : Nat} (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) : Program (m+2) := swap (accumulator f g B G)
/-- Explicit numeric original recipe with no child acceptance assumption. -/
def originalNumber {m : Nat} (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) (target : Nat) (inputs : List.Vector Nat m) : Nat → Nat :=
 CurrentRecursionAccumulator.number
  (fun k => EffectiveNumeral.calculation target (.recursion f g) (k ::ᵥ inputs))
  (fun k => let previous := evaluate (.recursion f g) (k ::ᵥ inputs)
    CurrentRecursionStepCertificate.number f target k inputs previous
     (evaluate g (k ::ᵥ previous ::ᵥ inputs))
     (evaluate G ((target+GorbowPRChildTags.stepTag f) ::ᵥ k ::ᵥ previous ::ᵥ inputs)))
  (CurrentRecursionBaseCertificate.number target inputs (evaluate f inputs) (evaluate B ((target+1) ::ᵥ inputs)))
/-- Graph preconditions only, not a source-realization theorem. Every named
node is the concrete AST shown; no calibration, success or closure oracle. -/
structure GraphNodes {arity m : Nat} (p : Program arity) (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) where
 publicTag : Nat
 accumulatorTag : Nat
 baseTag : Nat
 formulaTag : Nat
 stepTag : Nat
 mpTag : Nat
 hpublic : (nodes p)[publicTag]? = some ⟨m+2,program f g B G⟩
 haccumulator : (nodes p)[accumulatorTag]? = some ⟨m+2,accumulator f g B G⟩
 hbase : (nodes p)[baseTag]? = some ⟨m+1,CurrentRecursionBaseProgram.program f B⟩
 hformula : (nodes p)[formulaTag]? = some ⟨m+2,CurrentCalculationFormulaProgram.program (.recursion f g)⟩
 hstep : (nodes p)[stepTag]? = some ⟨m+2,CurrentRecursionStepProgram.program f g G⟩
 hmp : (nodes p)[mpTag]? = some ⟨4,LiteralRawMP.constructor⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram
