module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.TermProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.FormulaProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution
open UniformFixedFormulaAgreement.Traversal MachineProof
open RelationalSyntaxDepthTransport.ConstructorStepTargets
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Structural traversal over all original formula constructors, with actual
runtime input segments and explicit capture-correct environment commutation. -/
theorem traverses {arity ctx n depth inputs : Nat} (p : Program arity) (I : Installation p)
 (vtag scanTag len q : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hscan : (nodes p)[scanTag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (G : List (Formula ctx)) (e : Environment n (depth+1) inputs) (raw : List.Vector (Term ctx) inputs)
 (replacement : Term ctx)
 (hinputs : ∀ j : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid vtag (raw.get j)))) (f : Formula n) :
 ∀ rest out : Term ctx, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I (formulaValue I.ctag I.atag raw f e)
   (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag 1 (Term.numeral (depth+1))) rest)) out replacement)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out (formulaValue I.ctag I.atag (replacement ::ᵥ raw) f (specialize e)))))) := by
 cases f with
 | equal a b =>
  intro rest out
  exact ChildrenProof.binary p I G (.formula 0) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw a) (termValue I.ctag I.atag e raw b) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) a) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) b)
   replacement rfl (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs b) rest out
 | universalRelation a =>
  intro rest out
  exact ChildrenProof.unary p I G (.formula 1) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw a) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) a) replacement rfl (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) rest out
 | agent a =>
  intro rest out
  exact ChildrenProof.unary p I G (.formula 2) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw a) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) a) replacement rfl (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) rest out
 | knowledgeAll a =>
  intro rest out
  exact ChildrenProof.unary p I G (.formula 3) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw a) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) a) replacement rfl (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) rest out
 | knowledge a b =>
  intro rest out
  exact ChildrenProof.binary p I G (.formula 4) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw a) (termValue I.ctag I.atag e raw b) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) a) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) b)
   replacement rfl (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs b) rest out
 | truth a =>
  intro rest out
  exact ChildrenProof.unary p I G (.formula 5) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw a) (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) a) replacement rfl (TermProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) rest out
 | neg a =>
  intro rest out
  exact ChildrenProof.unary p I G (.formula 6) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 1
   (formulaValue I.ctag I.atag raw a e) (formulaValue I.ctag I.atag (replacement ::ᵥ raw) a (specialize e)) replacement rfl (traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) rest out
 | imp a b =>
  intro rest out
  exact ChildrenProof.binary p I G (.formula 7) (by intro h; cases h) (Term.numeral (depth+1)) 1
   (formulaValue I.ctag I.atag raw a e) (formulaValue I.ctag I.atag raw b e) (formulaValue I.ctag I.atag (replacement ::ᵥ raw) a (specialize e)) (formulaValue I.ctag I.atag (replacement ::ᵥ raw) b (specialize e))
   replacement rfl (traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) (traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs b) rest out
 | conj a b =>
  intro rest out
  exact ChildrenProof.binary p I G (.formula 8) (by intro h; cases h) (Term.numeral (depth+1)) 1
   (formulaValue I.ctag I.atag raw a e) (formulaValue I.ctag I.atag raw b e) (formulaValue I.ctag I.atag (replacement ::ᵥ raw) a (specialize e)) (formulaValue I.ctag I.atag (replacement ::ᵥ raw) b (specialize e))
   replacement rfl (traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) (traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs b) rest out
 | disj a b =>
  intro rest out
  exact ChildrenProof.binary p I G (.formula 9) (by intro h; cases h) (Term.numeral (depth+1)) 1
   (formulaValue I.ctag I.atag raw a e) (formulaValue I.ctag I.atag raw b e) (formulaValue I.ctag I.atag (replacement ::ᵥ raw) a (specialize e)) (formulaValue I.ctag I.atag (replacement ::ᵥ raw) b (specialize e))
   replacement rfl (traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs a) (traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs b) rest out
 | all a =>
  intro rest out
  have h := ChildrenProof.unary p I G (.formula 10) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral ((depth+1)+1)) 1
   (formulaValue I.ctag I.atag raw a (liftEnvironment e))
   (formulaValue I.ctag I.atag (replacement ::ᵥ raw) a (specialize (liftEnvironment e)))
   replacement rfl (traverses p I vtag scanTag len q hv hscan hlen hq G
    (liftEnvironment e) raw replacement hinputs a) rest out
  simpa only [formulaValue,EnvironmentProof.lifted,token,input,kind,
   show (10 : Fin 12).val = 10 from rfl] using h
 | ex a =>
  intro rest out
  have h := ChildrenProof.unary p I G (.formula 11) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral ((depth+1)+1)) 1
   (formulaValue I.ctag I.atag raw a (liftEnvironment e))
   (formulaValue I.ctag I.atag (replacement ::ᵥ raw) a (specialize (liftEnvironment e)))
   replacement rfl (traverses p I vtag scanTag len q hv hscan hlen hq G
    (liftEnvironment e) raw replacement hinputs a) rest out
  simpa only [formulaValue,EnvironmentProof.lifted,token,input,kind,
   show (11 : Fin 12).val = 11 from rfl] using h
termination_by sizeOf f
decreasing_by
 all_goals
  simp_wf
  have hf := eq_of_heq ‹HEq f _›
  rw [hf]
  simp <;> omega
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.FormulaProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.FormulaProof
