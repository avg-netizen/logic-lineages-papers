module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open SixSol20261113.HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)

theorem closedIdentity (u : Term 0) :
 GorbowFormulaSubstitution.renameTerm (Fin.elim0 : Fin 0 → Fin 0) u = u := by
 induction u with
 | var i => exact Fin.elim0 i
 | zero => rfl
 | succ t ih => simp_all [GorbowFormulaSubstitution.renameTerm,GorbowSubstitution.substitute]
 | add t v ht hv => simp_all [GorbowFormulaSubstitution.renameTerm,GorbowSubstitution.substitute]
 | mul t v ht hv => simp_all [GorbowFormulaSubstitution.renameTerm,GorbowSubstitution.substitute]
 | universalFunction t ih => simp_all [GorbowFormulaSubstitution.renameTerm,GorbowSubstitution.substitute]

theorem assignmentClosed (u : Term 0) :
 FixedFormulaSubstitution.assignment environment (fun _ => u) = (Fin.cases u Term.var : Fin 1 → Term 0) := by
 funext i
 have hi : i = 0 := Fin.eq_zero i
 subst i
 exact closedIdentity u

theorem formulaEval (f : Formula 1) (u : Term 0) :
 evaluate (formulaProgram f) (Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) =
 Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.allInstantiate f u))) := by
 have hraw : FixedFormulaSubstitution.rawInputs (fun _ : Fin 1 => u) =
  Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [FixedFormulaSubstitution.rawInputs]
 have hi := FixedFormulaSubstitution.NativeProof.nativeFormula 1 0 1 environment f (fun _ => u)
 rw [hraw,assignmentClosed] at hi
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 have hall : evaluate (applyTwo HistoryCodec.cons (constant 1 10) (constant 1 (templateCode f)))
  (Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) =
  Encodable.encode (10 :: GorbowFormulaPrefixCode.encode f) := by
  simp only [twoEval,constantEval,hc,templateCode]
  rfl
 have hf := RawUniversalReplace.NativeProof.binaryEval 7 _ _ _ _ _ hall hi
 simpa only [formulaProgram,instanceProgram,GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,
  GorbowFormulaPrefixCode.encode,GorbowCodeConstructors.binary] using hf

theorem nativeLine : Targets.NativeLine := by
 intro f u
 have hp (a b : Nat) : evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) = Nat.pair a b := HistoryCodec.NativeProof.nativePair _
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ := HistoryCodec.NativeProof.nativeConsAllVectors _
 have hf := formulaEval f u
 have hnil : Encodable.encode ([] : List (List Nat)) = 0 := rfl
 simp only [line,twoEval,constantEval,hf,hp,hc,FullFormulaInstantiation.nativeLine,templateCode,encodeProd,encodeNat,
  HistoryLookup.NativeProof.encodeCons,hnil]
 rfl

theorem nativeAcceptance : Targets.NativeAcceptance := by
 intro f u
 have hc : GorbowLogicalAxiomCode.compile 0
  (13,[GorbowFormulaPrefixCode.encode f,GorbowTermPrefixCode.encode u]) =
  some (GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.allInstantiate f u))) := by
  apply (GorbowLogicalAxiomCodeProof.exactCompilation 0 _ _).mpr
  exact ⟨.allInstantiate f u,rfl,rfl⟩
 simp [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,FullFormulaInstantiation.nativeLine,HistoryDispatcher.truth,hc]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof.assignmentClosed
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof.formulaEval
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof.nativeLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof.nativeAcceptance
