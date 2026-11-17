module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourPlugProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourSyntaxProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open GorbowSubstitution GorbowFormulaSubstitution

theorem root (tag offset : Nat) : FourPlugProof.plugged rootTemplate tag (tag+1) (tag+2) (tag+offset) = SyntaxProof.rootAt tag offset := by
 simp only [FourPlugProof.plugged,rootTemplate,SyntaxProof.rootAt,CurrentRecursionBaseProgram.openCall,
  substituteFormula,substitute,CurrentRecursionBaseProgram.TagSyntax.plug,liftSubstitute,
  CurrentCalculationFormulaProgram.NativeProof.substPair,CurrentCalculationFormulaProgram.NativeProof.substTuple,
  SixSol20261112.Fuel.Logic.substNumeral,← List.Vector.toList_map,List.Vector.map_cons,List.Vector.map_nil,
  Fin.cases_zero,Fin.cases_succ,SyntaxProof.renameNumeral,call,GorbowRegistryTuple.headerTerm]
 all_goals rfl

theorem allRoot (tag offset : Nat) : FourPlugProof.plugged (.all rootTemplate) tag (tag+1) (tag+2) (tag+offset) =
 .all (SyntaxProof.rootAt tag offset) := by
 change Formula.all (FourPlugProof.plugged rootTemplate tag (tag+1) (tag+2) (tag+offset)) = _
 rw [root]

theorem rawFour {ctx : Nat} (a b c d : Term ctx) : FourPlugProof.appended nil a b c d = (a ::ᵥ b ::ᵥ c ::ᵥ d ::ᵥ nil) := by
 apply List.Vector.ext
 intro i
 refine Fin.cases ?_ (fun i => ?_) i
 · rfl
 · refine Fin.cases ?_ (fun i => ?_) i
   · rfl
   · refine Fin.cases ?_ (fun i => ?_) i
     · rfl
     · have hi : i = 0 := Fin.eq_zero i
       subst i
       rfl

theorem rawFive {ctx : Nat} (x a b c d : Term ctx) : FourPlugProof.appended (x ::ᵥ nil) a b c d = (x ::ᵥ a ::ᵥ b ::ᵥ c ::ᵥ d ::ᵥ nil) := by
 apply List.Vector.ext
 intro i
 refine Fin.cases ?_ (fun i => ?_) i
 · rfl
 · refine Fin.cases ?_ (fun i => ?_) i
   · rfl
   · refine Fin.cases ?_ (fun i => ?_) i
     · rfl
     · refine Fin.cases ?_ (fun i => ?_) i
       · rfl
       · have hi : i = 0 := Fin.eq_zero i
         subst i
         rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourSyntaxProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourSyntaxProof
