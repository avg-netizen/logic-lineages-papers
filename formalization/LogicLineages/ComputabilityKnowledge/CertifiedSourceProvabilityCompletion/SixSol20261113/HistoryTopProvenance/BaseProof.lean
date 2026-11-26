module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.BaseProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem zeroCount {n ctx : Nat} (p : Program n) itag ptag ctag vtag leftTag rightTag
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (lines context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (provenance itag ptag ctag vtag leftTag rightTag .zero lines context raw tail remaining index fuel)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let entry := HistoryKernel.pairCall ptag context raw
 let history := HistoryLookup.consCall ctag entry tail
 let E := Formula.equal (HistoryRunSplice.run itag ptag .zero (.succ .zero) lines index fuel)
   (HistoryRunSplice.state ptag (.succ history) remaining)
 let Q := topWitness vtag leftTag rightTag context raw
 obtain ⟨hz⟩ := SixSol20261113.HistoryMachine.Equations.zero p itag (HistoryKernel.kernel v l a x) hi
   (HistoryRunSplice.state ptag (.succ .zero) lines) index fuel
 obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx
   (.succ .zero) lines (.succ history) remaining
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have heq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hz)) he
 have hs := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (Hilbert.Local.mp (.base hinj) heq)
 have h0 := Hilbert.Local.mp (.base (.arithmetic (.succInjective .zero history))) hs
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx entry tail
 have bad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hcons))
   (HistoryOrder.StepProof.localSym _ _ h0)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
   (Hilbert.Local.explosion Q bad (.base (.arithmetic (.succNotZero _)))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.BaseProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.BaseProof
