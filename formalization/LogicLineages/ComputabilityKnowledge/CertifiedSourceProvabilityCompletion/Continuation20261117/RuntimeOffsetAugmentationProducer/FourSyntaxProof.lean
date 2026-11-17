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
 have h10 : CurrentRecursionBaseProgram.TagSyntax.plug 1 (tag) (0 : Fin 2) = .var 0 := CurrentRecursionBaseProgram.TagSyntax.plugCast 1 (tag) (0 : Fin 1)
 have h11 : CurrentRecursionBaseProgram.TagSyntax.plug 1 (tag) (1 : Fin 2) = Term.numeral (tag) := CurrentRecursionBaseProgram.TagSyntax.plugLast 1 (tag)
 have h20 : CurrentRecursionBaseProgram.TagSyntax.plug 2 (tag+1) (0 : Fin 3) = .var 0 := CurrentRecursionBaseProgram.TagSyntax.plugCast 2 (tag+1) (0 : Fin 2)
 have h21 : CurrentRecursionBaseProgram.TagSyntax.plug 2 (tag+1) (1 : Fin 3) = .var 1 := CurrentRecursionBaseProgram.TagSyntax.plugCast 2 (tag+1) (1 : Fin 2)
 have h22 : CurrentRecursionBaseProgram.TagSyntax.plug 2 (tag+1) (2 : Fin 3) = Term.numeral (tag+1) := CurrentRecursionBaseProgram.TagSyntax.plugLast 2 (tag+1)
 have h30 : CurrentRecursionBaseProgram.TagSyntax.plug 3 (tag+2) (0 : Fin 4) = .var 0 := CurrentRecursionBaseProgram.TagSyntax.plugCast 3 (tag+2) (0 : Fin 3)
 have h31 : CurrentRecursionBaseProgram.TagSyntax.plug 3 (tag+2) (1 : Fin 4) = .var 1 := CurrentRecursionBaseProgram.TagSyntax.plugCast 3 (tag+2) (1 : Fin 3)
 have h32 : CurrentRecursionBaseProgram.TagSyntax.plug 3 (tag+2) (2 : Fin 4) = .var 2 := CurrentRecursionBaseProgram.TagSyntax.plugCast 3 (tag+2) (2 : Fin 3)
 have h33 : CurrentRecursionBaseProgram.TagSyntax.plug 3 (tag+2) (3 : Fin 4) = Term.numeral (tag+2) := CurrentRecursionBaseProgram.TagSyntax.plugLast 3 (tag+2)
 have h40 : CurrentRecursionBaseProgram.TagSyntax.plug 4 (tag+offset) (0 : Fin 5) = .var 0 := CurrentRecursionBaseProgram.TagSyntax.plugCast 4 (tag+offset) (0 : Fin 4)
 have h41 : CurrentRecursionBaseProgram.TagSyntax.plug 4 (tag+offset) (1 : Fin 5) = .var 1 := CurrentRecursionBaseProgram.TagSyntax.plugCast 4 (tag+offset) (1 : Fin 4)
 have h42 : CurrentRecursionBaseProgram.TagSyntax.plug 4 (tag+offset) (2 : Fin 5) = .var 2 := CurrentRecursionBaseProgram.TagSyntax.plugCast 4 (tag+offset) (2 : Fin 4)
 have h43 : CurrentRecursionBaseProgram.TagSyntax.plug 4 (tag+offset) (3 : Fin 5) = .var 3 := CurrentRecursionBaseProgram.TagSyntax.plugCast 4 (tag+offset) (3 : Fin 4)
 have h44 : CurrentRecursionBaseProgram.TagSyntax.plug 4 (tag+offset) (4 : Fin 5) = Term.numeral (tag+offset) := CurrentRecursionBaseProgram.TagSyntax.plugLast 4 (tag+offset)
 simp only [FourPlugProof.plugged,rootTemplate,SyntaxProof.rootAt,CurrentRecursionBaseProgram.openCall,
  substituteFormula,substitute,h10,h11,h20,h21,h22,h30,h31,h32,h33,h40,h41,h42,h43,h44,
  CurrentCalculationFormulaProgram.NativeProof.substPair,CurrentCalculationFormulaProgram.NativeProof.substTuple,
  SixSol20261112.Fuel.Logic.substNumeral,← List.Vector.toList_map,List.Vector.map_cons,List.Vector.map_nil,
  call,GorbowRegistryTuple.headerTerm]
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
