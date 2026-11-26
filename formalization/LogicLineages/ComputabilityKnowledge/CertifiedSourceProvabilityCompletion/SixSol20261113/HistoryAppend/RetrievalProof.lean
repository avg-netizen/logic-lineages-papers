module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.ValueEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.RetrievalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open TableEquationsProof TableLookupProof TableGapProof

def retrieved {ctx : Nat} (ttag ltag dtag ptag : Nat) (count child right : Term ctx) : Term ctx :=
  call ptag (HistoryLookup.lookupCall ltag (HistoryDifference.differenceCall dtag child count)
    (tableCall ttag count right) ::ᵥ nil)

/-- Bounded retrieval is genuinely SOME before predecessor removes its tag.
No failed Option reference is treated as a successful payload. -/
theorem tableRetrieve {n ctx : Nat} (p : Program n) ttag ltag htag dtag ptag
    (ht : (nodes p)[ttag]? = some ⟨2,table⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
    (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
    (hp : (nodes p)[ptag]? = some ⟨1,HistoryCodec.predecessor⟩) (count child right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryBounds.weakBound child count)
        (.equal (retrieved ttag ltag dtag ptag count child right) (headCall htag (tableCall ttag child right))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := Formula.equal (retrieved ttag ltag dtag ptag count child right) (headCall htag (tableCall ttag child right))
  let H := HistoryOrder.upperBody count child
  let N := liftTerm count
  let B := liftTerm child
  let R := liftTerm right
  let x : Term (ctx+1) := .var 0
  have he : Hilbert.Local T (ctx+1) [H] (.equal N (.add B x)) := .hypothesis List.mem_cons_self
  obtain ⟨hdiff⟩ := HistoryDifference.ArithmeticProof.differenceCancel n p dtag hd (ctx+1) B x
  have hdc := localUnary (HistoryDifference.differenceCall dtag (liftTerm B) (.var 0)) _ _ he
  simp only [HistoryDifference.ShiftProof.substituteDifference,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hdc
  have hindex := localTrans _ _ _ hdc (.base hdiff)
  have htab := localUnary (tableCall ttag (.var 0) (liftTerm R)) _ _ he
  simp only [substTable,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at htab
  have hli := localUnary (HistoryLookup.lookupCall ltag (.var 0) (liftTerm (tableCall ttag N R))) _ _ hindex
  simp only [substLookup,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hli
  have hlc := localUnary (HistoryLookup.lookupCall ltag (liftTerm x) (.var 0)) _ _ htab
  simp only [substLookup,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hlc
  obtain ⟨hgap⟩ := tableLookupGap p ttag ltag htag ht hl hh B x R
  have hsome := localTrans _ _ _ hli (localTrans _ _ _ hlc (.base hgap))
  have hpred := localUnary (call ptag (.var 0 ::ᵥ nil)) _ _ hsome
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hpred
  obtain ⟨hps⟩ := HistoryDifference.EquationsProof.predecessorSuccessor n p ptag hp (ctx+1) (headCall htag (tableCall ttag B R))
  have hout := localTrans _ _ _ hpred (.base hps)
  have hbody : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,retrieved,N,B,R,GorbowPACore.weaken,substituteFormula,Logic.substCall,
      List.Vector.map_cons,List.Vector.map_nil,substLookup,HistoryDifference.ShiftProof.substituteDifference,
      substTable,substHead,substitute,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H Q ⟨hbody⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.RetrievalProof
