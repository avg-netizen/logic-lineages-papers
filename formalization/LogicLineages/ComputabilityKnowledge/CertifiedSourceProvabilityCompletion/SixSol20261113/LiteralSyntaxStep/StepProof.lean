module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open StepSupportProof

theorem internalNone : Targets.InternalNone := by
 intro n p stag hs ctx token
 let args := (.zero ::ᵥ token ::ᵥ nil)
 have h : Computes p [] stepCode args .zero :=
  chooseZero p [] args (.projection 0) (constant 2 0) _ .zero
    (projection p [] args 0) (constantValue p [] args 0)
 obtain ⟨he⟩ := h stag hs
 exact ⟨Hilbert.Local.finish he⟩

theorem internalEmpty : Targets.InternalEmpty := by
 intro n p stag hs ctx token
 let args := (.succ .zero ::ᵥ token ::ᵥ nil)
 have hstack : Computes p [] stack args .zero :=
  unary p [] args HistoryCodec.predecessor (.projection 0) (.succ .zero) .zero
    (projection p [] args 0) (predecessor p [] .zero)
 have h : Computes p [] stepCode args .zero :=
  choosePositive p [] args (.projection 0) (constant 2 0) _ .zero .zero
    (projection p [] args 0)
    (chooseZero p [] args stack (constant 2 0) _ .zero hstack (constantValue p [] args 0))
 obtain ⟨he⟩ := h stag hs
 exact ⟨Hilbert.Local.finish he⟩

theorem internalPrepend : Targets.InternalPrepend := by
 intro n p stag etag ctag atag hs he hc ha ctx t rest token added
 let T := GorbowPRNumeralCalculation.Theory p
 let A := Formula.equal (expandCall etag t token) (.succ added)
 let G := [A]
 let row := HistoryLookup.consCall ctag t rest
 let args := (.succ row ::ᵥ token ::ᵥ nil)
 have hstack : Computes p G stack args row :=
  unary p G args HistoryCodec.predecessor (.projection 0) (.succ row) row
    (projection p G args 0) (predecessor p G row)
 have hhead : Computes p G headTask args t :=
  unary p G args HistoryLookup.head stack row t hstack (headCons p G ctag hc t rest)
 have htail : Computes p G restTasks args rest :=
  unary p G args HistoryLookup.tail stack row rest hstack (tailCons p G ctag hc t rest)
 have hexpand : Computes p G expanded args (.succ added) := by
  apply binary p G args expandCode headTask (.projection 1) t token (.succ added) hhead (projection p G args 1)
  exact changeValue p G expandCode (t ::ᵥ token ::ᵥ nil) (expandCall etag t token) (.succ added)
    (copies p G expandCode etag he _) (.hypothesis List.mem_cons_self)
 have hadded := unary p G args HistoryCodec.predecessor expanded (.succ added) added hexpand (predecessor p G added)
 have happ : Computes p G appended args (HistoryAppend.appendCall atag added rest) :=
  binary p G args HistoryAppend.append (applyOne HistoryCodec.predecessor expanded) restTasks added rest
    (HistoryAppend.appendCall atag added rest) hadded htail (copies p G HistoryAppend.append atag ha _)
 have hsuccess : Computes p G (success appended) args (.succ (HistoryAppend.appendCall atag added rest)) :=
  unary p G args .succ appended (HistoryAppend.appendCall atag added rest) _ happ (successor p G _)
 let pairTag := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let pairValue := call pairTag (t ::ᵥ rest ::ᵥ nil)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx t rest
 have hpositive : Computes p G stack args (.succ pairValue) := changeValue p G stack args row _ hstack (.base hcons)
 have h : Computes p G stepCode args (.succ (HistoryAppend.appendCall atag added rest)) :=
  choosePositive p G args (.projection 0) (constant 2 0) _ row _ (projection p G args 0)
   (choosePositive p G args stack (constant 2 0) _ pairValue _ hpositive
    (choosePositive p G args expanded (constant 2 0) _ added _ hexpand hsuccess))
 obtain ⟨hout⟩ := h stag hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepProof
