module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeAtomsProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)
open LiteralRawMP.NativeProof (pairEval appendLists)

theorem whenEqualEval (x yes no : Program 2) (k : Nat) (v : List.Vector Nat 2) :
 evaluate (whenEqual x k yes no) v = if evaluate x v = k then evaluate yes v else evaluate no v := by
 simp only [whenEqual,chooseEval,twoEval,equalEval,constantEval]
 split <;> simp_all

theorem consEval (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
 HistoryCodec.NativeProof.nativeConsAllVectors _
theorem successEval (a : Program 2) (v : List.Vector Nat 2) : evaluate (success a) v = (evaluate a v).succ := rfl

theorem contextAt (k n token : Nat) : evaluate context (Nat.pair k n ::ᵥ token ::ᵥ nil) = n := by
 rw [context,oneEval,projectionEval,get2_0,HistoryDecoder.NativeProof.evaluateDecoder,Nat.unpair_pair]
 rfl

theorem kindAt (k n token : Nat) : evaluate kind (Nat.pair k n ::ᵥ token ::ᵥ nil) = k := by
 rw [kind,oneEval,projectionEval,get2_0,HistoryDecoder.NativeProof.evaluateDecoder,Nat.unpair_pair]
 rfl

theorem taskAt (i k n token : Nat) : evaluate (task i context) (Nat.pair k n ::ᵥ token ::ᵥ nil) = Nat.pair i n := by
 rw [task,twoEval,constantEval,contextAt,pairEval]

theorem oneAt (i k n token : Nat) : evaluate (success (singleton (task i context))) (Nat.pair k n ::ᵥ token ::ᵥ nil) = Encodable.encode (some [(i,n)]) := by
 rw [successEval,singleton,twoEval,taskAt,constantEval,consEval]
 rfl

theorem twoAt (i k n token : Nat) : evaluate (success (double (task i context))) (Nat.pair k n ::ᵥ token ::ᵥ nil) = Encodable.encode (some [(i,n),(i,n)]) := by
 simp only [successEval,double,singleton,twoEval,taskAt,constantEval,consEval]
 rfl

theorem binderAt (k n token : Nat) : evaluate (success (singleton (task 1 (HistoryRuleSuffix.applyOne .succ context))))
 (Nat.pair k n ::ᵥ token ::ᵥ nil) = Encodable.encode (some [(1,n+1)]) := by
 have hs : evaluate (HistoryRuleSuffix.applyOne .succ context) (Nat.pair k n ::ᵥ token ::ᵥ nil) = n+1 := by
   change (evaluate context (Nat.pair k n ::ᵥ token ::ᵥ nil)).succ = n+1
   rw [contextAt]
 simp only [successEval,singleton,twoEval,task,constantEval,hs,pairEval,consEval]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeAtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeAtomsProof
