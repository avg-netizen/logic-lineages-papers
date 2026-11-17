module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
/-- Fixed runtime interface: target address, second-child offset, numerical input.
No selected source AST, node count, or certificate is embedded or supplied. -/
def target : Program 3 := .projection 0
def secondOffset : Program 3 := .projection 1
def input : Program 3 := .projection 2
def projectionTag : Program 3 := applyOne .succ target
def firstTag : Program 3 := CurrentRecursionStepProgram.shiftProgram 2 target
def secondTag : Program 3 := applyTwo HistoryCodec.add target secondOffset
def rawInput : Program 3 := applyOne LiteralNumeralPrefix.numeralCode input
/-- All four addresses are COMPUTED numerically before quotation. Arithmetic
inside the quoted tag position would change the original defining axiom AST. -/
def rawTags : List.Vector (Program 3) 4 :=
 (target ::ᵥ projectionTag ::ᵥ firstTag ::ᵥ secondTag ::ᵥ nil).map
  (applyOne LiteralNumeralPrefix.numeralCode)
def rawRoot : List.Vector (Program 3) 5 := rawInput ::ᵥ rawTags
/-- One original input variable, followed by four unclosed address slots. -/
def rootTemplate : Formula 5 :=
 .equal (CurrentRecursionBaseProgram.openCall (.var 1) (.var 0 ::ᵥ nil))
  (CurrentRecursionBaseProgram.openCall (.var 2)
   (CurrentRecursionBaseProgram.openCall (.var 3) (.var 0 ::ᵥ nil) ::ᵥ
    CurrentRecursionBaseProgram.openCall (.var 4) (.var 0 ::ᵥ nil) ::ᵥ nil))
/-- Explicit single original binder; address slots are never universally closed. -/
def rootSeed : Program 3 :=
 CurrentRecursionBaseProgram.mp
  (CurrentRecursionBaseProgram.quote rootTemplate rawRoot.get)
  (CurrentRecursionBaseProgram.allInstance
   (CurrentRecursionBaseProgram.headQuote rootTemplate rawTags.get) rawInput)
  (CurrentRecursionBaseProgram.axiomProgram
   (CurrentRecursionBaseProgram.quote (.all rootTemplate) rawTags.get))
def firstCall : Program 3 := CurrentCompositionProducerProgram.callCode firstTag (rawInput ::ᵥ nil)
def secondCall : Program 3 := CurrentCompositionProducerProgram.callCode secondTag (rawInput ::ᵥ nil)
def leftCode : Program 3 := CurrentCompositionProducerProgram.callCode target (rawInput ::ᵥ nil)
def middleCode : Program 3 := CurrentCompositionProducerProgram.callCode projectionTag (firstCall ::ᵥ secondCall ::ᵥ nil)
def projectionTemplate : Formula 3 :=
 .equal (CurrentRecursionBaseProgram.openCall (.var 2) (.var 0 ::ᵥ .var 1 ::ᵥ nil)) (.var 0)
def projectionSeed : Program 3 :=
 CurrentRecursionBaseProgram.seedProgram 2 projectionTemplate
  (firstCall ::ᵥ secondCall ::ᵥ applyOne LiteralNumeralPrefix.numeralCode projectionTag ::ᵥ nil).get
def program : Program 3 :=
 CurrentRecursionBaseProgram.transitivity leftCode middleCode firstCall rootSeed projectionSeed
/-- Independent original numeric recipe, not evaluation of the producer. -/
def number {n : Nat} (p : Program 1) (q : Program n) (tag value : Nat) : Nat :=
 let g := CorrectedAugmentationErasure.branches p q
 let nums : List.Vector (Term 0) 1 := Term.numeral value ::ᵥ nil
 let calls := List.Vector.ofFn (fun i : Fin 2 => call (tag + argumentTag (.projection (0 : Fin 2)) g i) nums)
 let parent := call tag nums
 let mid := call (tag+1) calls
 let rf := CurrentCompositionCertificate.rootFormula (.projection (0 : Fin 2)) g tag
 let pf := CorrectedAugmentationErasure.projectionFormula tag
 let root := PrescribedRuntimeSpecialization.produce rf (fun _ => Term.numeral value) (PrescribedSourceAxiomSpecialization.seed rf)
 let proj := PrescribedRuntimeSpecialization.produce pf calls.get (PrescribedSourceAxiomSpecialization.seed pf)
 transitivityNumber parent mid (calls.get 0) root proj
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer
