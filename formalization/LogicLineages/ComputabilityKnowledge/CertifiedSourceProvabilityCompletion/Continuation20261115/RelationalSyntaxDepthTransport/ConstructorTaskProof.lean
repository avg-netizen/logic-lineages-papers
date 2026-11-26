module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.MonotonicityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorTaskProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.PairProof HistoryCancellation.MonotonicityProof ConstructorStepTargets

/-- Actual cross-tag decoder inverses relate original pair-coded tasks. -/
theorem taskPair {n ctx : Nat} (p : Program n) (ptag l r k : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (a b : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (weakBound a b)
  (taskRelation l r (LiteralSyntaxStep.taskCall ptag k a) (LiteralSyntaxStep.taskCall ptag k b)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := weakBound a b
 let A := LiteralSyntaxStep.taskCall ptag k a
 let B := LiteralSyntaxStep.taskCall ptag k b
 obtain ⟨hla⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral k) a
 obtain ⟨hlb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral k) b
 obtain ⟨hra⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral k) a
 obtain ⟨hrb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral k) b
 have hk : Derivation T (.equal (call l (A ::ᵥ nil)) (call l (B ::ᵥ nil))) :=
  Logic.trans _ _ _ hla (Support.equalitySymmetry _ _ hlb)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hfirst := Hilbert.Local.mp (.mp (.base (weakChildTransport (call r (A ::ᵥ nil)) a b)) (.base hra)) hh
 have hbound := Hilbert.Local.mp (.mp (.base (weakTransport (call r (A ::ᵥ nil)) (call r (B ::ᵥ nil)) b)) (.base hrb)) hfirst
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (.logical (.andIntro _ _))) (.base hk)) hbound))⟩

/-- Every explicit constructor expansion row has aligned internally related
tasks. Binder rows use the paid successor-bound theorem, not native order. -/
theorem taskRows {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ctor : Constructor) (a b : Term ctx)
 (hab : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (weakBound a b)) :
 List.Forall₂ (fun x y => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (taskRelation l r x y))) (tasks ptag a ctor) (tasks ptag b ctor) := by
 obtain ⟨p0⟩ := taskPair p ptag l r 0 hp hl hr a b
 obtain ⟨p1⟩ := taskPair p ptag l r 1 hp hl hr a b
 obtain ⟨p2⟩ := taskPair p ptag l r 2 hp hl hr a b
 obtain ⟨ps⟩ := taskPair p ptag l r 1 hp hl hr (.succ a) (.succ b)
 obtain ⟨hs⟩ := BoundArithmeticProof.successorBounds (GorbowPRNumeralCalculation.Theory p) ctx a b
 have h0 := Hilbert.Local.mp (.base p0) hab
 have h1 := Hilbert.Local.mp (.base p1) hab
 have h2 := Hilbert.Local.mp (.base p2) hab
 have hsucc := Hilbert.Local.mp (.base ps) (.mp (.base hs) hab)
 cases ctor with
 | term i =>
  simp only [tasks]
  split <;> first
   | exact .nil
   | exact .cons ⟨h0⟩ .nil
   | exact .cons ⟨h2⟩ .nil
   | exact .cons ⟨h0⟩ (.cons ⟨h0⟩ .nil)
 | formula i =>
  simp only [tasks]
  split <;> first
   | exact .cons ⟨h0⟩ .nil
   | exact .cons ⟨h1⟩ .nil
   | exact .cons ⟨hsucc⟩ .nil
   | exact .cons ⟨h0⟩ (.cons ⟨h0⟩ .nil)
   | exact .cons ⟨h1⟩ (.cons ⟨h1⟩ .nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorTaskProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorTaskProof
