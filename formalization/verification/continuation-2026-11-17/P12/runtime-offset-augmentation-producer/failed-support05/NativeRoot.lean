module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeValues
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.SeedNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeRoot
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open GorbowSubstitution GorbowFormulaSubstitution HistoryRuleSuffix.NativeProof
open CurrentRecursionBaseProgram.NativePrimitives

theorem addressNumeral (tag offset : Nat) (i : Fin 4) : ∃ n, (SyntaxProof.addresses tag offset).get i = Term.numeral n := by
 refine Fin.cases ?_ (fun i => ?_) i
 · exact ⟨tag,rfl⟩
 · refine Fin.cases ?_ (fun i => ?_) i
   · exact ⟨tag+1,rfl⟩
   · refine Fin.cases ?_ (fun i => ?_) i
     · exact ⟨tag+2,rfl⟩
     · have hi : i = 0 := Fin.eq_zero i
       subst i
       exact ⟨tag+offset,rfl⟩

theorem full (tag offset value : Nat) :
 substituteFormula (Term.numeral value ::ᵥ SyntaxProof.addresses tag offset).get rootTemplate =
 substituteFormula (fun _ : Fin 1 => Term.numeral value) (SyntaxProof.rootAt tag offset) := by
 rw [← SyntaxProof.root,GorbowFormulaCompositionProof.composition]
 congr 1
 funext i
 refine Fin.cases ?_ (fun j => ?_) i
 · rfl
 · obtain ⟨n,hn⟩ := addressNumeral tag offset j
   simp only [List.Vector.get_cons_succ,liftSubstitute,hn,GorbowHeaderSubstitutionProof.numerals,
    SixSol20261112.Fuel.Logic.substNumeral]

theorem rootSeedEval (tag offset value : Nat) :
 evaluate rootSeed (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) =
 PrescribedRuntimeSpecialization.produce (SyntaxProof.rootAt tag offset)
  (fun _ => Term.numeral value) (PrescribedSourceAxiomSpecialization.seed (SyntaxProof.rootAt tag offset)) := by
 let args := tag ::ᵥ offset ::ᵥ value ::ᵥ nil
 have ht := NativeValues.tagsEval tag offset value
 have hi := NativeValues.inputEval tag offset value
 have hr : ∀ i, evaluate (rawRoot.get i) args =
  Encodable.encode (GorbowTermPrefixCode.encode ((Term.numeral value ::ᵥ SyntaxProof.addresses tag offset).get i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hi
  · exact ht j
 have hf := quoteEval rootTemplate rawRoot.get args _ hr
 rw [full] at hf
 have hm := headQuoteEval rootTemplate rawTags.get args _ ht
 rw [SyntaxProof.root] at hm
 have ha := quoteEval (.all rootTemplate) rawTags.get args _ ht
 change evaluate (CurrentRecursionBaseProgram.quote (.all rootTemplate) rawTags.get) args =
  Encodable.encode (GorbowFormulaPrefixCode.encode (.all (substituteFormula (liftSubstitute (SyntaxProof.addresses tag offset).get) rootTemplate))) at ha
 rw [SyntaxProof.root] at ha
 have hax := CurrentRecursionBaseProgram.SeedNativeProof.axiomEval _ args _ ha
 unfold rootSeed
 rw [mpEval _ _ _ args _ hf,allInstanceEval _ _ args _ _ hm hi,hax]
 have he : (liftSubstitute (fun i : Fin 0 => (Term.numeral value : Term 0))) = (Term.var : Fin 1 → Term 1) := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl
 simp only [PrescribedRuntimeSpecialization.produce,he,SixSol20261112.Fuel.Logic.formulaIdentity,
  PrescribedSourceAxiomSpecialization.seed,GorbowStandardInduction.universalClosure]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeRoot
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeRoot
