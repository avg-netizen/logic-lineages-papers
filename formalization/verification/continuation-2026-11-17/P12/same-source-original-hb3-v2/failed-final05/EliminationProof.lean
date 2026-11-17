module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ExistentialSyntax
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericEliminationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.EliminationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open SixSol20261112.Fuel NamedArithmeticGraph
open GorbowSubstitution GorbowFormulaSubstitution
open CurrentPublishedProvabilityIntroduction.SyntaxSupport
attribute [local irreducible] GorbowPublishedDCB.rho GorbowPublishedDCB.prD
 GorbowSortedSyntaxCode.formulaCode GorbowBooleanTruth.binaryCodeTerm
/-- Closed conclusions do not retain either locally bound input witness. -/
theorem doubleEliminate (U : Sentence → Prop) (A : Formula 2) (B : Sentence)
 (h : Nonempty (Derivation U (.imp A (GorbowPACore.weaken (GorbowPACore.weaken B))))) :
 Nonempty (Derivation U (.imp (.ex (.ex A)) B)) := GenericEliminationProof.doubleEliminate U A B h

theorem closedValue {ctx : Nat} (pF : Program 1) (c : Code) (sigma : Sentence) :
 closed (n := ctx) (CurrentPublishedProvabilityIntroduction.PublishedSyntax.argument pF c sigma) =
 LiteralCheckerSuccessBridge.value pF c sigma := by
 change substitute (Fin.elim0 : Fin 0 → Term ctx) (LiteralCheckerSuccessBridge.value (ctx := 0) pF c sigma) = _
 exact LiteralCheckerSuccessBridge.LiteralNaturality.valueSubst (m := 0) (ctx := ctx) Fin.elim0 pF c sigma

theorem inputBody (pF : Program 1) (c : Code) (sigma : Sentence) :
 checkerBody (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c)
  (CurrentPublishedProvabilityIntroduction.PublishedSyntax.argument pF c sigma) =
 CurrentCheckerSuccessCertificate.success pF c (.var (1 : Fin 2))
  (LiteralCheckerSuccessBridge.value pF c sigma) (.var 0) := by
 unfold checkerBody CurrentCheckerSuccessCertificate.success CurrentCheckerSuccessCertificate.checkerInputs
 rw [closedValue]

theorem weakenProv {ctx : Nat} (pF : Program 1) (c : Code) (sigma : Sentence) :
 GorbowPACore.weaken (applyProv pF c (LiteralCheckerSuccessBridge.value (ctx := ctx) pF c sigma)) =
 applyProv pF c (LiteralCheckerSuccessBridge.value (ctx := ctx+1) pF c sigma) := by
 rw [GenericEliminationProof.weakenApply,LiteralCheckerSuccessBridge.LiteralNaturality.valueSubst]

theorem assemble (U : Sentence → Prop) (pF : Program 1) (c : Code) (sigma : Sentence)
 (h : Nonempty (Derivation U (.imp
  (CurrentCheckerSuccessCertificate.success pF c (.var (1 : Fin 2))
   (LiteralCheckerSuccessBridge.value pF c sigma) (.var 0))
  (applyProv pF c (LiteralCheckerSuccessBridge.value (ctx := 2) pF c (prD pF c sigma)))))) :
 Nonempty (Derivation U (GorbowPublishedLobReduction.hb3 pF c sigma)) := by
 have hd := doubleEliminate U
  (checkerBody (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c)
   (CurrentPublishedProvabilityIntroduction.PublishedSyntax.argument pF c sigma))
  (prD pF c (prD pF c sigma)) ?_
 · simpa only [← SameSourcePublishedWitness.AlignmentProof.originalSyntax pF c sigma,
    GorbowPublishedLobReduction.hb3] using hd
 · change Nonempty (Derivation U (.imp _ (GorbowPACore.weaken (GorbowPACore.weaken
    (applyProv pF c (LiteralCheckerSuccessBridge.value (ctx := 0) pF c (prD pF c sigma)))))))
   rw [weakenProv,weakenProv,inputBody]
   exact h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.EliminationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.EliminationProof
