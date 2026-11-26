module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.OriginalValidityPreflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorValidityTargets FixedTemplateEncodingTargets
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- The unchanged original tag13 formula is internally valid, including the
literal encoded full template and capture-correct arbitrary closed raw instance.
Scanner/equality nodes are extracted internally from the original validator. -/
theorem internalFormulaValidity : Targets.InternalFormulaValidity := by
 intro f n p vtag ftag ptag ctag atag hv hf hp hc ha ctx raw
 obtain ⟨stag,sp,sc,etag,hs,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p ftag hf
 let G := [RawReflexivityDispatcher.valid vtag raw]
 have hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid vtag raw) := .hypothesis List.mem_cons_self
 obtain ⟨htemplate⟩ := FixedFormulaValidityProof.fixedFormulaValidity 1 1 0 (boundEnvironment 1) f
  n p vtag stag ptag ctag atag hv hs hp hc ha ctx G nil (fun i => Fin.elim0 i)
 obtain ⟨hcode⟩ := FixedTemplateEncodingProof.boundFormulaEncoding 1 f n p ctag atag hc ha ctx
 let symbolic := FixedFormulaSubstitution.formulaValue ctag atag (nil : List.Vector (Term ctx) 0) f (boundEnvironment 1)
 let literal := Term.numeral (n := ctx) (FullFormulaInstantiation.templateCode f)
 have hscan := Logic.callCongruence (ctx := ctx) (GorbowPRNumeralCalculation.Theory p) stag
  (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (Term.numeral 1)) ::ᵥ symbolic ::ᵥ nil)
  (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (Term.numeral 1)) ::ᵥ literal ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hcode
     | succ i => exact Fin.elim0 i)
 have htemplateLiteral : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag
   (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (.succ .zero))) literal) (.succ .zero)) :=
  localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hscan)) htemplate
 have hforallChildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks ptag (.zero : Term ctx) (.formula 10)) [literal] :=
  .cons ⟨htemplateLiteral⟩ .nil
 obtain ⟨hforall⟩ := ConstructorValidityProof.constructorValidity n p stag ptag ctag atag hs hp hc ha ctx G
  (.formula 10) .zero [literal] hforallChildren
 have hruntime : ∀ i : Fin 1, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid vtag ((raw ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hvalid⟩
  | succ i => exact Fin.elim0 i
 obtain ⟨hinstance⟩ := FixedFormulaValidityProof.fixedFormulaValidity 1 0 1 FullFormulaInstantiation.environment f
  n p vtag stag ptag ctag atag hv hs hp hc ha ctx G (raw ::ᵥ nil) hruntime
 let antecedent := HistoryLookup.consCall ctag (Term.numeral 10) literal
 let consequent := FullFormulaInstantiation.instanceValue ctag atag f raw
 have himpChildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks ptag (.zero : Term ctx) (.formula 7)) [antecedent,consequent] :=
  .cons ⟨hforall⟩ (.cons ⟨hinstance⟩ .nil)
 obtain ⟨himp⟩ := ConstructorValidityProof.constructorValidity n p stag ptag ctag atag hs hp hc ha ctx G
  (.formula 7) .zero [antecedent,consequent] himpChildren
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p ftag stag ptag ctag etag
  hf hs hp hc he (.zero : Term ctx) (FullFormulaInstantiation.formulaValue ctag atag f raw)
 exact ⟨(Hilbert.Local.mp (Hilbert.Local.base hcomplete) himp).discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Proof
