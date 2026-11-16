module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- One genuine original substitution/quantifier normalization contract.
Runtime codes are arbitrary; only original arity1 matrix/closed witness guards
are assumed. No output-validity, successful-instance, native-image, prefix
exhaustion or commutation premise. Existing output validity is reused, not
recounted. No source selection, existential introduction or HB3 claim. -/
def Internal : Prop := ∀ n (p : Program n) (I : UniformClosedRule13Validity.Installation p),
 ∀ ctx (matrix witness : Term ctx),
 let raw := instanceValue I matrix witness
 let negMatrix := negValue I.ctag matrix
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards I.fval I.vtag matrix witness)
   (.conj (.equal (instanceValue I negMatrix witness) (negValue I.ctag raw))
    (.equal (UniformClosedRule13Validity.compiledConclusion I.toGraphInstallation negMatrix witness)
     (PrescribedRuntimeEquality.impValue I.ctag I.atag
      (FixedFormulaSubstitution.unaryValue I.ctag 10 negMatrix) (negValue I.ctag raw))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.Targets
