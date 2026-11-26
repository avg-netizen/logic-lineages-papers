module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBQuantifierSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericEliminationProof
open GorbowSyntax GorbowTheoryProof GorbowPublishedDCB GorbowSubstitution GorbowFormulaSubstitution
/-- Closed conclusions do not retain either locally bound input witness. -/
theorem doubleEliminate (U : Sentence → Prop) (A : Formula 2) (B : Sentence)
 (h : Nonempty (Derivation U (.imp A (GorbowPACore.weaken (GorbowPACore.weaken B))))) :
 Nonempty (Derivation U (.imp (.ex (.ex A)) B)) := by
 obtain ⟨hi⟩ := HBQuantifier.existentialElimination U A (GorbowPACore.weaken B) h
 exact HBQuantifier.existentialElimination U (.ex A) B ⟨hi⟩

theorem weakenApply {ctx : Nat} (pF : GorbowPRProgram.Program 1) (c : Code) (u : Term ctx) :
 GorbowPACore.weaken (applyProv pF c u) =
 applyProv pF c (substitute (fun i : Fin ctx => Term.var i.succ) u) := by
 unfold GorbowPACore.weaken applyProv
 rw [GorbowFormulaCompositionProof.composition]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericEliminationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericEliminationProof
