module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepRejectionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep LiteralSyntaxStep.StepSupportProof

/-- Rejected actual expansion forces the original step to NONE on a genuine
cons stack; this is derived through all original select branches. -/
theorem stepReject {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (etag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (t rest tok : Term ctx)
 (hz : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (expandCall etag t tok) .zero)) :
 Computes p G stepCode (.succ (HistoryLookup.consCall ctag t rest) ::ᵥ tok ::ᵥ nil) .zero := by
 let row := HistoryLookup.consCall ctag t rest
 let args := .succ row ::ᵥ tok ::ᵥ nil
 have hstack : Computes p G stack args row :=
  unary p G args HistoryCodec.predecessor (.projection 0) (.succ row) row
   (projection p G args 0) (predecessor p G row)
 have hhead : Computes p G headTask args t :=
  unary p G args HistoryLookup.head stack row t hstack (headCons p G ctag hc t rest)
 have hexpand : Computes p G expanded args .zero :=
  binary p G args expandCode headTask (.projection 1) t tok .zero hhead (projection p G args 1)
   (changeValue p G expandCode (t ::ᵥ tok ::ᵥ nil) (expandCall etag t tok) .zero
    (copies p G expandCode etag he _) hz)
 let cp := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let pv := call cp (t ::ᵥ rest ::ᵥ nil)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx t rest
 have hpositive : Computes p G stack args (.succ pv) := changeValue p G stack args row _ hstack (.base hcons)
 exact choosePositive p G args (.projection 0) (constant 2 0) _ row .zero (projection p G args 0)
  (choosePositive p G args stack (constant 2 0) _ pv .zero hpositive
   (chooseZero p G args expanded (constant 2 0) _ .zero hexpand (constantValue p G args 0)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepRejectionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepRejectionProof
