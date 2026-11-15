module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportIndexProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportGapProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open SubstitutionProof StepTransportWitnessProof

def positiveClaim {ctx : Nat} (stag ctag dtag len q l r : Nat)
 (oh ot nh nt tok result og : Term ctx) : Formula ctx :=
 .imp (taskRelation l r oh nh)
  (.imp (stackRelation len q l r ot nt)
   (.imp (.equal (call l (oh ::ᵥ nil)) (Term.numeral 2))
    (.imp (.equal (HistoryDifference.differenceCall dtag tok (call r (oh ::ᵥ nil))) (.succ og))
     (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))
      (StepTransportTargets.witnesses stag len q l r (HistoryLookup.consCall ctag nh nt) tok result)))))
theorem substPositive {m n : Nat} (s : Fin m → Term n) stag ctag dtag len q l r
 (oh ot nh nt tok result og : Term m) :
 substituteFormula s (positiveClaim stag ctag dtag len q l r oh ot nh nt tok result og) =
 positiveClaim stag ctag dtag len q l r (substitute s oh) (substitute s ot) (substitute s nh)
  (substitute s nt) (substitute s tok) (substitute s result) (substitute s og) := by
 simp only [positiveClaim,substituteFormula,substTask,substStack,substWitnesses,
  HistoryDifference.ShiftProof.substituteDifference,HistoryLookup.DropEquationsProof.substCons,
  LiteralSyntaxStep.stepCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  LiteralSyntaxStep.ExpansionSupportProof.substituteNumeral,substitute]

/-- Eliminate the NEW positive-gap witness internally at the original registry. -/
theorem eliminateNew {n ctx : Nat} (p : Program n) (stag etag ctag atag dtag len q l r : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nh nt tok result og : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.ex (HistoryOrder.SupportProof.predBody
   (HistoryDifference.differenceCall dtag tok (call r (nh ::ᵥ nil)))))
   (positiveClaim stag ctag dtag len q l r oh ot nh nt tok result og))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.SupportProof.predBody (HistoryDifference.differenceCall dtag tok (call r (nh ::ᵥ nil)))
 let A := taskRelation l r (liftTerm oh) (liftTerm nh)
 let B := stackRelation len q l r (liftTerm ot) (liftTerm nt)
 let C := Formula.equal (call l (liftTerm oh ::ᵥ nil)) (Term.numeral 2)
 let D := Formula.equal (HistoryDifference.differenceCall dtag (liftTerm tok) (call r (liftTerm oh ::ᵥ nil))) (.succ (liftTerm og))
 let E := Formula.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag (liftTerm oh) (liftTerm ot))) (liftTerm tok)) (.succ (liftTerm result))
 let G := [E,D,C,B,A,H]
 have hh : Hilbert.Local T (ctx+1) G A := .hypothesis (by simp [G])
 have ht : Hilbert.Local T (ctx+1) G B := .hypothesis (by simp [G])
 have hk : Hilbert.Local T (ctx+1) G C := .hypothesis (by simp [G])
 have hog : Hilbert.Local T (ctx+1) G D := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+1) G E := .hypothesis (by simp [G])
 have hng : Hilbert.Local T (ctx+1) G
  (.equal (HistoryDifference.differenceCall dtag (liftTerm tok) (call r (liftTerm nh ::ᵥ nil))) (.succ (.var 0))) := by
  have h : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
  simpa only [H,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,
   HistoryDifference.ShiftProof.substituteDifference,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil] using h
 obtain ⟨hout⟩ := StepTransportIndexProof.positiveTransport p G stag etag ctag atag dtag len q l r
  hs he hc ha hd hl hr (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt)
  (liftTerm tok) (liftTerm result) (liftTerm og) (.var 0) hh ht hk hog hng hold
 have hb : Derivation T (.imp H (GorbowPACore.weaken (positiveClaim stag ctag dtag len q l r oh ot nh nt tok result og))) := by
  rw [GorbowPACore.weaken,substPositive]
  simpa only [G,A,B,C,D,E,positiveClaim,liftTerm,renameTerm] using
   hout.discharge.discharge.discharge.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H (positiveClaim stag ctag dtag len q l r oh ot nh nt tok result og) ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportGapProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportGapProof
