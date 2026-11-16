module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SyntaxSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.PublishedSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution SyntaxSupport
abbrev argument (pF : Program 1) (c : Code) (sigma : Sentence) : Term 0 :=
 GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))

theorem renameEmpty {n : Nat} (r : Fin 0 → Fin n) (u : Term 0) : renameTerm r u = closed u := by
 unfold closed renameTerm
 congr 1
 funext i
 exact Fin.elim0 i

theorem renameVar {m n : Nat} (r : Fin m → Fin n) (i : Fin m) : renameTerm r (.var i) = .var (r i) := rfl

theorem applyProvShape (pF : Program 1) (c : Code) (u : Term 0) :
 applyProv pF c u = Formula.ex (Formula.ex (checkerBody (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c) u)) := by
 simp only [applyProv,provability,substituteFormula,callSubstitute,substitute,
  List.Vector.map_cons,List.Vector.map_nil,SixSol20261112.Fuel.Logic.substNumeral,liftSubstitute,
  Fin.cases_zero,Fin.cases_succ,renameVar,renameEmpty,renameClosed]
 simp only [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
  show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
  show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
  Fin.cases_succ,Fin.cases_zero,renameVar,renameClosed]
 rfl

attribute [local irreducible] GorbowPublishedDCB.rho GorbowBooleanTruth.binaryCodeTerm GorbowSortedSyntaxCode.formulaCode

theorem outer (pF : Program 1) (c : Code) (sigma : Sentence) :
 outerMatrix pF c sigma = Formula.ex (checkerBody (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c) (argument pF c sigma)) := by
 unfold outerMatrix
 change (match applyProv pF c (argument pF c sigma) with
  | .ex a => a
  | _ => .equal .zero .zero) = _
 rw [applyProvShape]

theorem instantiateBody (tag index fuel : Nat) (u : Term 0) :
 GorbowStandardInstances.instantiate (.ex (checkerBody tag index u)) (Term.numeral fuel) =
 Formula.ex (checkerInner tag index fuel u) := by
 simp only [GorbowStandardInstances.instantiate,checkerBody,substituteFormula,callSubstitute,substitute,
  List.Vector.map_cons,List.Vector.map_nil,SixSol20261112.Fuel.Logic.substNumeral,liftSubstitute,
  Fin.cases_zero,Fin.cases_succ,renameVar,renameEmpty,renameClosed,substituteClosed,closedNumeral]
 simp only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
  Fin.cases_succ,Fin.cases_zero,closedNumeral]
 rfl

theorem inner (pF : Program 1) (c : Code) (sigma : Sentence) (fuel : Nat) :
 innerMatrix pF c sigma fuel = checkerInner (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c) fuel (argument pF c sigma) := by
 unfold innerMatrix
 rw [outer,instantiateBody]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.PublishedSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.PublishedSyntax
