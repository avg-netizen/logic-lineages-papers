module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.TermProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FormulaProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph Traversal
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- All twelve original formula constructors, retaining actual task order and
successor-depth binder environments. This is a structural traversal proof,
not native calibration or an assumed formula-code image at runtime. -/
theorem traverses {n ctx : Nat} (p : Program n) (I : Installation p)
 (depth : Nat) (f : Formula (depth+1)) (raw : Term ctx) :
 ∀ rest out : Term ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (GorbowFormulaPrefixCode.encode f)
   (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag 1 (Term.numeral (depth+1))) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out
     (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) f (EnvironmentProof.environment depth)))))) := by
 cases f with
 | equal a b =>
  intro rest out
  exact BinaryProof.traverses p I (.formula 0) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (GorbowTermPrefixCode.encode a) (GorbowTermPrefixCode.encode b)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) a)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) b) raw rfl (TermProof.traverses p I depth a raw) (TermProof.traverses p I depth b raw) rest out
 | universalRelation a =>
  intro rest out
  exact UnaryProof.traverses p I (.formula 1) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0 (GorbowTermPrefixCode.encode a)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) a) raw rfl (TermProof.traverses p I depth a raw) rest out
 | agent a =>
  intro rest out
  exact UnaryProof.traverses p I (.formula 2) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0 (GorbowTermPrefixCode.encode a)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) a) raw rfl (TermProof.traverses p I depth a raw) rest out
 | knowledgeAll a =>
  intro rest out
  exact UnaryProof.traverses p I (.formula 3) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0 (GorbowTermPrefixCode.encode a)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) a) raw rfl (TermProof.traverses p I depth a raw) rest out
 | knowledge a b =>
  intro rest out
  exact BinaryProof.traverses p I (.formula 4) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (GorbowTermPrefixCode.encode a) (GorbowTermPrefixCode.encode b)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) a)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) b) raw rfl (TermProof.traverses p I depth a raw) (TermProof.traverses p I depth b raw) rest out
 | truth a =>
  intro rest out
  exact UnaryProof.traverses p I (.formula 5) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0 (GorbowTermPrefixCode.encode a)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) a) raw rfl (TermProof.traverses p I depth a raw) rest out
 | neg a =>
  intro rest out
  exact UnaryProof.traverses p I (.formula 6) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 1 (GorbowFormulaPrefixCode.encode a)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) a (EnvironmentProof.environment depth)) raw rfl (traverses p I depth a raw) rest out
 | imp a b =>
  intro rest out
  exact BinaryProof.traverses p I (.formula 7) (by intro h; cases h) (Term.numeral (depth+1)) 1
   (GorbowFormulaPrefixCode.encode a) (GorbowFormulaPrefixCode.encode b)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) a (EnvironmentProof.environment depth))
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) b (EnvironmentProof.environment depth)) raw rfl (traverses p I depth a raw) (traverses p I depth b raw) rest out
 | conj a b =>
  intro rest out
  exact BinaryProof.traverses p I (.formula 8) (by intro h; cases h) (Term.numeral (depth+1)) 1
   (GorbowFormulaPrefixCode.encode a) (GorbowFormulaPrefixCode.encode b)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) a (EnvironmentProof.environment depth))
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) b (EnvironmentProof.environment depth)) raw rfl (traverses p I depth a raw) (traverses p I depth b raw) rest out
 | disj a b =>
  intro rest out
  exact BinaryProof.traverses p I (.formula 9) (by intro h; cases h) (Term.numeral (depth+1)) 1
   (GorbowFormulaPrefixCode.encode a) (GorbowFormulaPrefixCode.encode b)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) a (EnvironmentProof.environment depth))
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) b (EnvironmentProof.environment depth)) raw rfl (traverses p I depth a raw) (traverses p I depth b raw) rest out
 | all a =>
  intro rest out
  have h := UnaryProof.traverses p I (.formula 10) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral ((depth+1)+1)) 1 (GorbowFormulaPrefixCode.encode a)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) a (EnvironmentProof.environment (depth+1))) raw rfl (traverses p I (depth+1) a raw) rest out
  simpa only [FixedFormulaSubstitution.formulaValue,EnvironmentProof.lifted] using h
 | ex a =>
  intro rest out
  have h := UnaryProof.traverses p I (.formula 11) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral ((depth+1)+1)) 1 (GorbowFormulaPrefixCode.encode a)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (raw ::ᵥ nil) a (EnvironmentProof.environment (depth+1))) raw rfl (traverses p I (depth+1) a raw) rest out
  simpa only [FixedFormulaSubstitution.formulaValue,EnvironmentProof.lifted] using h
termination_by sizeOf f
decreasing_by all_goals simp_wf
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FormulaProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FormulaProof
