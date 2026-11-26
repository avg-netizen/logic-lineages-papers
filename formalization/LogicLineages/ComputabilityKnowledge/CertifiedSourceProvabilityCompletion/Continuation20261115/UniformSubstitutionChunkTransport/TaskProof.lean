module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TaskProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

/-- Actual original pair/decoder equations, no native task image assumption. -/
theorem term {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (depth : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (taskRelation l r (LiteralSyntaxStep.taskCall ptag 0 (.succ depth))
   (LiteralSyntaxStep.taskCall ptag 0 depth))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := LiteralSyntaxStep.taskCall ptag 0 (.succ depth)
 let B := LiteralSyntaxStep.taskCall ptag 0 depth
 obtain ⟨hla⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral 0) (.succ depth)
 obtain ⟨hlb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral 0) depth
 obtain ⟨hra⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral 0) (.succ depth)
 obtain ⟨hrb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral 0) depth
 have hb : Hilbert.Local T ctx G
  (.equal (call r (A ::ᵥ nil)) (.succ (call r (B ::ᵥ nil)))) :=
  localTrans _ _ _ (.base hra) (HistoryOrder.StepProof.localSym _ _ (localUnary (.succ (.var 0)) _ _ (.base hrb)))
 have hk : Hilbert.Local T ctx G (.equal (call l (A ::ᵥ nil)) (call l (B ::ᵥ nil))) :=
  localTrans _ _ _ (.base hla) (HistoryOrder.StepProof.localSym _ _ (.base hlb))
 have hc : Hilbert.Local T ctx G
  (.disj (.equal (call l (A ::ᵥ nil)) .zero) (.equal (call l (A ::ᵥ nil)) (Term.numeral 1))) :=
  .mp (.base (.logical (.orLeft _ _))) (.base hla)
 have hs := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hk) hc
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hb) (.mp (.base (.logical (.orLeft _ _))) hs)⟩

/-- Actual original pair/decoder equations, no native task image assumption. -/
theorem formula {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (depth : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (taskRelation l r (LiteralSyntaxStep.taskCall ptag 1 (.succ depth))
   (LiteralSyntaxStep.taskCall ptag 1 depth))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := LiteralSyntaxStep.taskCall ptag 1 (.succ depth)
 let B := LiteralSyntaxStep.taskCall ptag 1 depth
 obtain ⟨hla⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral 1) (.succ depth)
 obtain ⟨hlb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral 1) depth
 obtain ⟨hra⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral 1) (.succ depth)
 obtain ⟨hrb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral 1) depth
 have hb : Hilbert.Local T ctx G
  (.equal (call r (A ::ᵥ nil)) (.succ (call r (B ::ᵥ nil)))) :=
  localTrans _ _ _ (.base hra) (HistoryOrder.StepProof.localSym _ _ (localUnary (.succ (.var 0)) _ _ (.base hrb)))
 have hk : Hilbert.Local T ctx G (.equal (call l (A ::ᵥ nil)) (call l (B ::ᵥ nil))) :=
  localTrans _ _ _ (.base hla) (HistoryOrder.StepProof.localSym _ _ (.base hlb))
 have hc : Hilbert.Local T ctx G
  (.disj (.equal (call l (A ::ᵥ nil)) .zero) (.equal (call l (A ::ᵥ nil)) (Term.numeral 1))) :=
  .mp (.base (.logical (.orRight _ _))) (.base hla)
 have hs := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hk) hc
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hb) (.mp (.base (.logical (.orLeft _ _))) hs)⟩

/-- Actual original pair/decoder equations, no native task image assumption. -/
theorem index {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (depth : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (taskRelation l r (LiteralSyntaxStep.taskCall ptag 2 (.succ depth))
   (LiteralSyntaxStep.taskCall ptag 0 depth))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := LiteralSyntaxStep.taskCall ptag 2 (.succ depth)
 let B := LiteralSyntaxStep.taskCall ptag 0 depth
 obtain ⟨hla⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral 2) (.succ depth)
 obtain ⟨hlb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral 0) depth
 obtain ⟨hra⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral 2) (.succ depth)
 obtain ⟨hrb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral 0) depth
 have hb : Hilbert.Local T ctx G
  (.equal (call r (A ::ᵥ nil)) (.succ (call r (B ::ᵥ nil)))) :=
  localTrans _ _ _ (.base hra) (HistoryOrder.StepProof.localSym _ _ (localUnary (.succ (.var 0)) _ _ (.base hrb)))
 have hs : Hilbert.Local T ctx G
  (.conj (.equal (call l (A ::ᵥ nil)) (Term.numeral 2)) (.equal (call l (B ::ᵥ nil)) .zero)) :=
  Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.base hla)) (.base hlb)
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hb) (.mp (.base (.logical (.orRight _ _))) hs)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TaskProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TaskProof
