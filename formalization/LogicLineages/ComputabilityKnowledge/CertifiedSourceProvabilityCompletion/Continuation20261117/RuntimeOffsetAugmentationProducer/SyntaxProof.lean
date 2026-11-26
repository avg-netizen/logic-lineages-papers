module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TagSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SyntaxProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open GorbowSubstitution GorbowFormulaSubstitution

theorem renameNumeral {m n : Nat} (rho : Fin m → Fin n) (x : Nat) :
 renameTerm rho (Term.numeral x) = Term.numeral x := by
 induction x with
 | zero => rfl
 | succ x ih => exact congrArg Term.succ ih

def addresses (tag offset : Nat) : List.Vector (Term 0) 4 :=
 Term.numeral tag ::ᵥ Term.numeral (tag+1) ::ᵥ Term.numeral (tag+2) ::ᵥ Term.numeral (tag+offset) ::ᵥ nil
def rootAt (tag offset : Nat) : Formula 1 :=
 .equal (call tag (.var 0 ::ᵥ nil))
  (call (tag+1) (call (tag+2) (.var 0 ::ᵥ nil) ::ᵥ call (tag+offset) (.var 0 ::ᵥ nil) ::ᵥ nil))
theorem root (tag offset : Nat) :
 substituteFormula (liftSubstitute (addresses tag offset).get) rootTemplate = rootAt tag offset := by
 have h0 : liftSubstitute (addresses tag offset).get (0 : Fin 5) = .var 0 := rfl
 have h1 : liftSubstitute (addresses tag offset).get (1 : Fin 5) = Term.numeral tag := by
  change renameTerm Fin.succ (Term.numeral tag) = _
  exact renameNumeral _ _
 have h2 : liftSubstitute (addresses tag offset).get (2 : Fin 5) = Term.numeral (tag+1) := by
  change renameTerm Fin.succ (Term.numeral (tag+1)) = _
  exact renameNumeral _ _
 have h3 : liftSubstitute (addresses tag offset).get (3 : Fin 5) = Term.numeral (tag+2) := by
  change renameTerm Fin.succ (Term.numeral (tag+2)) = _
  exact renameNumeral _ _
 have h4 : liftSubstitute (addresses tag offset).get (4 : Fin 5) = Term.numeral (tag+offset) := by
  change renameTerm Fin.succ (Term.numeral (tag+offset)) = _
  exact renameNumeral _ _
 simp only [rootTemplate,rootAt,CurrentRecursionBaseProgram.openCall,
  substituteFormula,substitute,h0,h1,h2,h3,h4,
  CurrentCalculationFormulaProgram.NativeProof.substPair,CurrentCalculationFormulaProgram.NativeProof.substTuple,
  SixSol20261112.Fuel.Logic.substNumeral,← List.Vector.toList_map,List.Vector.map_cons,List.Vector.map_nil,
  call,GorbowRegistryTuple.headerTerm]
 all_goals rfl

theorem projection (tag : Nat) :
 substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug 2 (tag+1)) projectionTemplate =
 CorrectedAugmentationErasure.projectionFormula tag := by
 have h0 : CurrentRecursionBaseProgram.TagSyntax.plug 2 (tag+1) (0 : Fin 3) = .var 0 :=
  CurrentRecursionBaseProgram.TagSyntax.plugCast 2 (tag+1) (0 : Fin 2)
 have h1 : CurrentRecursionBaseProgram.TagSyntax.plug 2 (tag+1) (1 : Fin 3) = .var 1 :=
  CurrentRecursionBaseProgram.TagSyntax.plugCast 2 (tag+1) (1 : Fin 2)
 have h2 : CurrentRecursionBaseProgram.TagSyntax.plug 2 (tag+1) (2 : Fin 3) = Term.numeral (tag+1) :=
  CurrentRecursionBaseProgram.TagSyntax.plugLast 2 (tag+1)
 simp only [projectionTemplate,CorrectedAugmentationErasure.projectionFormula,
  CurrentRecursionBaseProgram.openCall,substituteFormula,substitute,h0,h1,h2,
  CurrentCalculationFormulaProgram.NativeProof.substPair,CurrentCalculationFormulaProgram.NativeProof.substTuple,
  SixSol20261112.Fuel.Logic.substNumeral,← List.Vector.toList_map,List.Vector.map_cons,List.Vector.map_nil,
  call,GorbowRegistryTuple.headerTerm]
 all_goals rfl

theorem firstOffset {n : Nat} (p : Program 1) (q : Program n) :
 argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 0 = 2 := rfl

theorem actualRoot {n : Nat} (p : Program 1) (q : Program n) (tag offset : Nat)
 (h : offset = argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1) :
 rootAt tag offset = CurrentCompositionCertificate.rootFormula (.projection (0 : Fin 2))
  (CorrectedAugmentationErasure.branches p q) tag := by
 subst offset
 congr 2

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SyntaxProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SyntaxProof
