module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphOperations
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.QuoteGraph
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphRules
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.SeedGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open GraphOperations

theorem exactInternal : Targets.InternalStep := by
 intro arity p m base step child J tag I ht ctx target counter inputs
 let args := target ::ᵥ counter ::ᵥ inputs
 let offset := GorbowPRChildTags.stepTag base
 have hprior := QuoteGraph.prior p base step child J I target counter inputs
 have hnext := QuoteGraph.next p base step child J I target counter inputs
 have hleft := QuoteGraph.left p base step child J I target counter inputs offset
 have hright := QuoteGraph.right p base step child J I target counter inputs offset
 have hopen := QuoteGraph.unary p base step child J I target counter inputs offset
 have hprevious := LiteralRawMP.ConstructorSupportProof.unary p args LiteralNumeralPrefix.numeralCode J.ntag I.hn
  (previous base step) (call J.qtag (counter ::ᵥ inputs))
  (EvaluatorGraph.previousGraph p base step J.qtag I.hq target counter inputs)
 have houtput := LiteralRawMP.ConstructorSupportProof.unary p args LiteralNumeralPrefix.numeralCode J.ntag I.hn
  (result base step) (call J.stepTag (counter ::ᵥ call J.qtag (counter ::ᵥ inputs) ::ᵥ inputs))
  (EvaluatorGraph.resultGraph p base step J I.hq I.hstep target counter inputs)
 have hP := binaryGraph p args J.ctag J.atag I.hc I.ha 0 _ _ _ _ hprior hprevious
 have hroot := binaryGraph p args J.ctag J.atag I.hc I.ha 0 _ _ _ _ hnext hleft
 have hchildFormula := binaryGraph p args J.ctag J.atag I.hc I.ha 0 _ _ _ _ hright houtput
 have hseed := SeedGraphProof.seedGraph p args base step child J I (m+1) (rootTemplate m offset)
  (CurrentRecursionBaseProgram.rootArguments (m+1))
  (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs))
  (CurrentRecursionBaseProgram.GraphInputs.rootArgs p (baseTags J) I.hn target (counter ::ᵥ inputs))
 have hcongruence := GraphRules.unaryGraph p args base step child J I _ _ _ _ _ _ _ _ _ _ hopen hprior hprevious hleft hright
 have hlift := liftGraph p args base step child J I _ _ _ _ _ _ hroot hP hseed
 have hfirst := GraphRules.transitivityGraph p args base step child J I _ _ _ _ _ _ _ _ _ _ _ _
  hP hnext hleft hright hlift hcongruence
 have hchild := EvaluatorGraph.childGraph p base step child J I target counter inputs
 have hliftChild := liftGraph p args base step child J I _ _ _ _ _ _ hchildFormula hP hchild
 exact GraphRules.transitivityGraph p args base step child J I _ _ _ _ _ _ _ _ _ _ _ _
  hP hnext hright houtput hfirst hliftChild tag ht
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphProof
