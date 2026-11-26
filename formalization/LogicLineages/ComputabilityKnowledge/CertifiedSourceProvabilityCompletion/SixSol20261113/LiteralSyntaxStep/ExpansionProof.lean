module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.ExpansionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.ExpansionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof ExpansionSupportProof

theorem binaryAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) (token : Nat)
 (hl : 7 ≤ token) (hu : token ≤ 9) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral token ::ᵥ nil)
 (.succ (HistoryLookup.consCall ctag (taskCall ptag 1 binder)
   (HistoryLookup.consCall ctag (taskCall ptag 1 binder) .zero))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral token ::ᵥ nil
 obtain ⟨hk,hn⟩ := taskFields p G ptag hp binder token
 have ht : Computes p G (.projection 1) args (Term.numeral token) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 1 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ token 0 _ (by omega) ht
 apply whenNe p G args _ _ _ token 4 _ (by omega) ht
 apply whenNe p G args _ _ _ token 1 _ (by omega) ht
 apply whenNe p G args _ _ _ token 2 _ (by omega) ht
 apply whenNe p G args _ _ _ token 3 _ (by omega) ht
 apply whenNe p G args _ _ _ token 5 _ (by omega) ht
 apply whenNe p G args _ _ _ token 6 _ (by omega) ht
 by_cases h7 : token=7
 · subst token
   exact whenEq p G args _ _ _ 7 _ ht hout
 · apply whenNe p G args _ _ _ token 7 _ h7 ht
   by_cases h8 : token=8
   · subst token
     exact whenEq p G args _ _ _ 8 _ ht hout
   · apply whenNe p G args _ _ _ token 8 _ h8 ht
     have h9 : token=9 := by omega
     subst token
     exact whenEq p G args _ _ _ 9 _ ht hout

theorem quantifierAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) (token : Nat)
 (hl : 10 ≤ token) (hu : token ≤ 11) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral token ::ᵥ nil)
 (.succ (HistoryLookup.consCall ctag (taskCall ptag 1 (.succ binder)) .zero)) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral token ::ᵥ nil
 obtain ⟨hk,hn⟩ := taskFields p G ptag hp binder token
 have ht : Computes p G (.projection 1) args (Term.numeral token) := projection p G args 1
 have hsucc := unary p G args .succ context binder (.succ binder) hn (StepSupportProof.successor p G binder)
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _
   (taskValue p G args ptag hp 1 (applyOne .succ context) (.succ binder) hsucc))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ token 0 _ (by omega) ht
 apply whenNe p G args _ _ _ token 4 _ (by omega) ht
 apply whenNe p G args _ _ _ token 1 _ (by omega) ht
 apply whenNe p G args _ _ _ token 2 _ (by omega) ht
 apply whenNe p G args _ _ _ token 3 _ (by omega) ht
 apply whenNe p G args _ _ _ token 5 _ (by omega) ht
 apply whenNe p G args _ _ _ token 6 _ (by omega) ht
 apply whenNe p G args _ _ _ token 7 _ (by omega) ht
 apply whenNe p G args _ _ _ token 8 _ (by omega) ht
 apply whenNe p G args _ _ _ token 9 _ (by omega) ht
 by_cases h10 : token=10
 · subst token
   exact whenEq p G args _ _ _ 10 _ ht hout
 · apply whenNe p G args _ _ _ token 10 _ h10 ht
   have h11 : token=11 := by omega
   subst token
   exact whenEq p G args _ _ _ 11 _ ht hout

theorem internalFormulaBinary : Targets.InternalFormulaBinary := by
 intro n p etag ptag ctag he hp hc ctx binder i
 obtain ⟨h⟩ := binaryAt p [] ptag ctag hp hc binder (7+i.val) (by omega) (by omega) etag he
 exact ⟨Hilbert.Local.finish h⟩

theorem internalQuantifier : Targets.InternalQuantifier := by
 intro n p etag ptag ctag he hp hc ctx binder i
 obtain ⟨h⟩ := quantifierAt p [] ptag ctag hp hc binder (10+i.val) (by omega) (by omega) etag he
 exact ⟨Hilbert.Local.finish h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.ExpansionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.ExpansionProof
