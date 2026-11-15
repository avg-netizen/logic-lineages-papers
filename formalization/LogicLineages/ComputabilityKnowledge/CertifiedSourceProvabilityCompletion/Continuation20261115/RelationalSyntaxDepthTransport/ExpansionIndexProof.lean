module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRuntimeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionIndexProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof ExpansionCasesSupportProof ExpansionCasesTargets

def positiveClaim {ctx : Nat} (etag l : Nat) (task tok added : Term ctx) : Formula ctx :=
 .imp (.equal (call l (task ::ᵥ nil)) (Term.numeral 2))
  (.imp (.equal (LiteralSyntaxStep.expandCall etag task tok) (.succ added)) (.equal added .zero))
theorem substClaim {m n : Nat} (s : Fin m → Term n) etag l (task tok added : Term m) :
 substituteFormula s (positiveClaim etag l task tok added) =
 positiveClaim etag l (substitute s task) (substitute s tok) (substitute s added) := by
 simp only [positiveClaim,substituteFormula,LiteralSyntaxStep.expandCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,LiteralSyntaxStep.ExpansionSupportProof.substituteNumeral,substitute]

theorem positiveOutput {n ctx : Nat} (p : Program n) (etag l r dtag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (task tok added : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.ex (HistoryOrder.SupportProof.predBody
   (HistoryDifference.differenceCall dtag tok (call r (task ::ᵥ nil)))))
   (positiveClaim etag l task tok added))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.SupportProof.predBody (HistoryDifference.differenceCall dtag tok (call r (task ::ᵥ nil)))
 let K := Formula.equal (call l (liftTerm task ::ᵥ nil)) (Term.numeral 2)
 let E := Formula.equal (LiteralSyntaxStep.expandCall etag (liftTerm task) (liftTerm tok)) (.succ (liftTerm added))
 let G := [E,K,H]
 have hk : Hilbert.Local T (ctx+1) G K := .hypothesis (by simp [G])
 have hs : Hilbert.Local T (ctx+1) G E := .hypothesis (by simp [G])
 have hg : Hilbert.Local T (ctx+1) G
  (.equal (HistoryDifference.differenceCall dtag (liftTerm tok) (call r (liftTerm task ::ᵥ nil))) (.succ (.var 0))) := by
  have h : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
  simpa only [H,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,
   HistoryDifference.ShiftProof.substituteDifference,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil] using h
 obtain ⟨hx⟩ := ExpansionRuntimeProof.indexPositive p G l r dtag hl hr hd
  (liftTerm task) (liftTerm tok) (.var 0) hk hg etag he
 have hsucc := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hs) hx
 have hout := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) hsucc
 have hb : Derivation T (.imp H (GorbowPACore.weaken (positiveClaim etag l task tok added))) := by
  rw [GorbowPACore.weaken, substClaim]
  simpa only [G,K,E,GorbowPACore.weaken,substClaim,positiveClaim,liftTerm] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))
 exact HBQuantifier.existentialElimination T H (positiveClaim etag l task tok added) ⟨hb⟩

/-- A positive observed result cannot equal the actual rejected output zero. -/
theorem rejectSuccess {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (etag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩) (task tok added : Term ctx) (Q : Formula ctx)
 (hs : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.expandCall etag task tok) (.succ added)))
 (hz : Computes p G LiteralSyntaxStep.expandCode (task ::ᵥ tok ::ᵥ nil) .zero) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G Q) := by
 obtain ⟨hzero⟩ := hz etag he
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hs) hzero
 exact ⟨Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero added)))⟩

/-- Original index success classification for arbitrary runtime token, bound
and output, including the zero branch contradiction and positive witness. -/
theorem indexCaseAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (etag l r dtag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (task tok added : Term ctx)
 (hs : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.expandCall etag task tok) (.succ added)))
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral 2))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (indexCase dtag l r task tok added)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let D := HistoryDifference.differenceCall dtag tok (call r (task ::ᵥ nil))
 let Z := Formula.equal D .zero
 let P := Formula.ex (HistoryOrder.SupportProof.predBody D)
 let Q := indexCase dtag l r task tok added
 have hz : Hilbert.Local T ctx (Z :: G) Z := .hypothesis List.mem_cons_self
 have hc0 := ExpansionRuntimeProof.indexZero p (Z :: G) l r dtag hl hr hd task tok (push Z hk) hz
 obtain ⟨hzero⟩ := rejectSuccess p (Z :: G) etag he task tok added Q (push Z hs) hc0
 obtain ⟨hpos⟩ := positiveOutput p etag l r dtag he hl hr hd task tok added
 have hp : Hilbert.Local T ctx (P :: G) P := .hypothesis List.mem_cons_self
 have ha := Hilbert.Local.mp (.mp (.mp (.base hpos) hp) (push P hk)) (push P hs)
 have hpositive : Hilbert.Local T ctx (P :: G) Q :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (push P hk))
   (.mp (.mp (.base (.logical (.andIntro _ _))) hp) ha)
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T D
 exact ⟨.mp (.mp (.mp (.base (.logical (.orElim Z P Q)))
  (Hilbert.Local.discharge hzero)) (Hilbert.Local.discharge hpositive)) (.base hcases)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionIndexProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionIndexProof
