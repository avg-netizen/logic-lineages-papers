module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.BaseProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionBinding
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ZeroAllProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution
open SixSol20261112.Fuel Induction

theorem zeroAll {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (allLines (ctx := ctx) itag ptag ctag (validityTag itag v l a x) leftTag rightTag .zero)) := by
 obtain ⟨hz⟩ := BaseProof.zeroCount (ctx := ctx+7) p itag ptag ctag
   (validityTag itag v l a x) leftTag rightTag v l a x hi hp hc
   (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)
 refine ⟨?_⟩
 simpa only [allLines,allContext,allRaw,allTail,allRemaining,allIndex,allFuel,
   liftTerm,renameTerm,substitute,Fin.succ] using
   (Derivation.generalize (Derivation.generalize (Derivation.generalize
   (Derivation.generalize (Derivation.generalize (Derivation.generalize
   (Derivation.generalize hz)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ZeroAllProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ZeroAllProof
