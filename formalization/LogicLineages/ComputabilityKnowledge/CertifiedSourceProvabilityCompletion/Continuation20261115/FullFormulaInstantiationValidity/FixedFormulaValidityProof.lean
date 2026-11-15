module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedFormulaValidityTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedFormulaValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113 RelationalSyntaxDepthTransport ConstructorValidityTargets FixedFormulaSubstitution
/-- Full original formula syntax, with capture-correct environments generalized
through both binders. Runtime inputs carry actual internal validator proofs. -/
theorem fixedFormulaValidity : FixedFormulaValidityTargets.InternalFixedFormulaValidity := by
 intro n depth inputs e f arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
 induction f generalizing depth with
 | equal t u =>
  have ht := FixedTermValidityProof.fixedTermValidity _ depth inputs e t arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hu := FixedTermValidityProof.fixedTermValidity _ depth inputs e u arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 0)) [termValue ctag atag e raw t, termValue ctag atag e raw u] :=
   .cons ht (.cons hu .nil)
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 0) (Term.numeral depth) [termValue ctag atag e raw t, termValue ctag atag e raw u] hchildren
  exact ⟨hcoded⟩
 | universalRelation t =>
  have ht := FixedTermValidityProof.fixedTermValidity _ depth inputs e t arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 1)) [termValue ctag atag e raw t] :=
   .cons ht .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 1) (Term.numeral depth) [termValue ctag atag e raw t] hchildren
  exact ⟨hcoded⟩
 | agent t =>
  have ht := FixedTermValidityProof.fixedTermValidity _ depth inputs e t arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 2)) [termValue ctag atag e raw t] :=
   .cons ht .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 2) (Term.numeral depth) [termValue ctag atag e raw t] hchildren
  exact ⟨hcoded⟩
 | knowledgeAll t =>
  have ht := FixedTermValidityProof.fixedTermValidity _ depth inputs e t arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 3)) [termValue ctag atag e raw t] :=
   .cons ht .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 3) (Term.numeral depth) [termValue ctag atag e raw t] hchildren
  exact ⟨hcoded⟩
 | knowledge t u =>
  have ht := FixedTermValidityProof.fixedTermValidity _ depth inputs e t arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hu := FixedTermValidityProof.fixedTermValidity _ depth inputs e u arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 4)) [termValue ctag atag e raw t, termValue ctag atag e raw u] :=
   .cons ht (.cons hu .nil)
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 4) (Term.numeral depth) [termValue ctag atag e raw t, termValue ctag atag e raw u] hchildren
  exact ⟨hcoded⟩
 | truth t =>
  have ht := FixedTermValidityProof.fixedTermValidity _ depth inputs e t arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 5)) [termValue ctag atag e raw t] :=
   .cons ht .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 5) (Term.numeral depth) [termValue ctag atag e raw t] hchildren
  exact ⟨hcoded⟩
 | neg f ih =>
  have hf := ih (depth := depth) (e := e)
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 6)) [FixedFormulaSubstitution.formulaValue ctag atag raw f e] :=
   .cons hf .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 6) (Term.numeral depth) [FixedFormulaSubstitution.formulaValue ctag atag raw f e] hchildren
  exact ⟨hcoded⟩
 | imp f g ihf ihg =>
  have hf := ihf (depth := depth) (e := e)
  have hg := ihg (depth := depth) (e := e)
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 7)) [FixedFormulaSubstitution.formulaValue ctag atag raw f e, FixedFormulaSubstitution.formulaValue ctag atag raw g e] :=
   .cons hf (.cons hg .nil)
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 7) (Term.numeral depth) [FixedFormulaSubstitution.formulaValue ctag atag raw f e, FixedFormulaSubstitution.formulaValue ctag atag raw g e] hchildren
  exact ⟨hcoded⟩
 | conj f g ihf ihg =>
  have hf := ihf (depth := depth) (e := e)
  have hg := ihg (depth := depth) (e := e)
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 8)) [FixedFormulaSubstitution.formulaValue ctag atag raw f e, FixedFormulaSubstitution.formulaValue ctag atag raw g e] :=
   .cons hf (.cons hg .nil)
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 8) (Term.numeral depth) [FixedFormulaSubstitution.formulaValue ctag atag raw f e, FixedFormulaSubstitution.formulaValue ctag atag raw g e] hchildren
  exact ⟨hcoded⟩
 | disj f g ihf ihg =>
  have hf := ihf (depth := depth) (e := e)
  have hg := ihg (depth := depth) (e := e)
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 9)) [FixedFormulaSubstitution.formulaValue ctag atag raw f e, FixedFormulaSubstitution.formulaValue ctag atag raw g e] :=
   .cons hf (.cons hg .nil)
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 9) (Term.numeral depth) [FixedFormulaSubstitution.formulaValue ctag atag raw f e, FixedFormulaSubstitution.formulaValue ctag atag raw g e] hchildren
  exact ⟨hcoded⟩
 | all f ih =>
  have hf := ih (depth := depth + 1) (e := liftEnvironment e)
  -- The original numeral recursion identifies depth+1 with successor bound.
  change Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag
    (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (.succ (Term.numeral depth))))
    (FixedFormulaSubstitution.formulaValue ctag atag raw f (liftEnvironment e))) (.succ .zero))) at hf
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 10)) [FixedFormulaSubstitution.formulaValue ctag atag raw f (liftEnvironment e)] :=
   .cons hf .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 10) (Term.numeral depth) [FixedFormulaSubstitution.formulaValue ctag atag raw f (liftEnvironment e)] hchildren
  exact ⟨hcoded⟩
 | ex f ih =>
  have hf := ih (depth := depth + 1) (e := liftEnvironment e)
  -- The original numeral recursion identifies depth+1 with successor bound.
  change Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag
    (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (.succ (Term.numeral depth))))
    (FixedFormulaSubstitution.formulaValue ctag atag raw f (liftEnvironment e))) (.succ .zero))) at hf
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.formula 11)) [FixedFormulaSubstitution.formulaValue ctag atag raw f (liftEnvironment e)] :=
   .cons hf .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.formula 11) (Term.numeral depth) [FixedFormulaSubstitution.formulaValue ctag atag raw f (liftEnvironment e)] hchildren
  exact ⟨hcoded⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedFormulaValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedFormulaValidityProof
