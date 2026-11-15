module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTaskProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open ConstructorStepTargets LiteralRawMP.DispatcherSupportProof
/-- Internal decoder reconstruction at an arbitrary literal kind, including index
kind2. There is no native canonical-task/image assumption. -/
theorem canonical {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r k : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (task : Term ctx)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral k))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal task (LiteralSyntaxStep.taskCall ptag k (call r (task ::ᵥ nil))))) := by
 obtain ⟨heta⟩ := ExpansionPairProof.pairEta p ptag l r hp hl hr task
 have hpair := callCongruence ptag
  (call l (task ::ᵥ nil) ::ᵥ call r (task ::ᵥ nil) ::ᵥ nil)
  (Term.numeral k ::ᵥ call r (task ::ᵥ nil) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hk
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive _))
     | succ i => exact Fin.elim0 i)
 exact ⟨localTrans _ _ _ (.base (Support.equalitySymmetry _ _ heta)) hpair⟩
/-- Original step-call equality after reconstructing one arbitrary raw head and
identifying its literal constructor token. Both successor and cons layers remain
in the actual runtime argument; this is congruence, not a transfer assumption. -/
theorem constructorInput {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (stag ptag ctag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (head tail tok : Term ctx) (ctor : Constructor)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (head ::ᵥ nil)) (Term.numeral (kind ctor))))
 (ht : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal tok (Term.numeral (token ctor)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag head tail)) tok)
   (LiteralSyntaxStep.stepCall stag (input ptag ctag ctor (call r (head ::ᵥ nil)) tail)
    (Term.numeral (token ctor))))) := by
 obtain ⟨hh⟩ := canonical p G ptag l r (kind ctor) hp hl hr head hk
 have hc := callCongruence ctag (head ::ᵥ tail ::ᵥ nil)
  (LiteralSyntaxStep.taskCall ptag (kind ctor) (call r (head ::ᵥ nil)) ::ᵥ tail ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hh
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive tail))
     | succ i => exact Fin.elim0 i)
 have hs := localUnary (.succ (.var 0)) _ _ hc
 exact ⟨callCongruence stag
  (.succ (HistoryLookup.consCall ctag head tail) ::ᵥ tok ::ᵥ nil)
  (input ptag ctag ctor (call r (head ::ᵥ nil)) tail ::ᵥ Term.numeral (token ctor) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => simpa only [input,HistoryLookup.consCall,GorbowStandardInstances.instantiate,
       GorbowSubstitution.substitute,Fin.cases_zero,List.Vector.get_cons_zero] using hs
   | succ i => cases i using Fin.cases with
     | zero => exact ht
     | succ i => exact Fin.elim0 i)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTaskProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTaskProof
