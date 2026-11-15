module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalReplace.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open SixSol20261113.HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)

theorem closedInstance (a b : Term 1) (u : Term 0) :
 GorbowStandardInstances.instantiate (template a b) u =
 .equal (GorbowSubstitution.substitute (fun _ => u) a) (GorbowSubstitution.substitute (fun _ => u) b) := by
 have hs : (Fin.cases u Term.var : Fin 1 → Term 0) = (fun _ => u) := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl
 simp only [GorbowStandardInstances.instantiate,template,GorbowFormulaSubstitution.substituteFormula,hs]

theorem formulaEval (a b : Term 1) (u : Term 0) :
 evaluate (formulaProgram a b) (Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) =
 Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.allInstantiate (template a b) u))) := by
 have ha := RawUnarySubstitution.StatementChecks.exactNative a u
 have hb := RawUnarySubstitution.StatementChecks.exactNative b u
 have hi := RawUniversalReplace.NativeProof.binaryEval 0 _ _ _ _ _ ha hb
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 have hall : evaluate (applyTwo HistoryCodec.cons (constant 1 10) (constant 1 (templateCode a b)))
  (Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) =
  Encodable.encode (10 :: GorbowFormulaPrefixCode.encode (template a b)) := by
  simp only [twoEval,constantEval,hc,templateCode]
  rfl
 have hf := RawUniversalReplace.NativeProof.binaryEval 7 _ _ _ _ _ hall hi
 simpa only [formulaProgram,instanceProgram,GorbowPACore.logicalFormula,closedInstance,
  GorbowFormulaPrefixCode.encode,GorbowCodeConstructors.binary] using hf

theorem nativeLine : Targets.NativeLine := by
 intro a b u
 have hp (a b : Nat) : evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) = Nat.pair a b := HistoryCodec.NativeProof.nativePair _
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ := HistoryCodec.NativeProof.nativeConsAllVectors _
 have hf := formulaEval a b u
 have hnil : Encodable.encode ([] : List (List Nat)) = 0 := rfl
 simp only [line,twoEval,constantEval,hf,hp,hc,nativeLine,templateCode,encodeProd,encodeNat,
  HistoryLookup.NativeProof.encodeCons,hnil]
 rfl

theorem nativeAcceptance : Targets.NativeAcceptance := by
 intro a b u
 have hc : GorbowLogicalAxiomCode.compile 0
  (13,[GorbowFormulaPrefixCode.encode (template a b),GorbowTermPrefixCode.encode u]) =
  some (GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.allInstantiate (template a b) u))) := by
  apply (GorbowLogicalAxiomCodeProof.exactCompilation 0 _ _).mpr
  exact ⟨.allInstantiate (template a b) u,rfl,rfl⟩
 simp [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,nativeLine,HistoryDispatcher.truth,hc]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.NativeProof.closedInstance
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.NativeProof.formulaEval
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.NativeProof.nativeLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.NativeProof.nativeAcceptance
