module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionPairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryIteratorSuffix.WitnessProof LiteralRawMP.DispatcherSupportProof

def property {ctx : Nat} (ptag l r : Nat) (code : Term ctx) : Formula ctx :=
 .equal (HistoryKernel.pairCall ptag (call l (code ::ᵥ nil)) (call r (code ::ᵥ nil))) code
theorem substProperty {m n : Nat} (s : Fin m → Term n) ptag l r (code : Term m) :
 substituteFormula s (property ptag l r code) = property ptag l r (substitute s code) := by
 simp only [property,substituteFormula,substPair,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem weakenProperty {ctx : Nat} ptag l r (code : Term ctx) :
 GorbowPACore.weaken (property ptag l r code) = property ptag l r (liftTerm code) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl

/-- Reconstruct under genuine internal pair witnesses using original decoder
copies, uniformly in arbitrary runtime terms and local assumptions. -/
theorem reconstructAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (a b code : Term ctx)
 (he : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryKernel.pairCall ptag a b) code)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (property ptag l r code)) := by
 obtain ⟨hla⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp a b
 obtain ⟨hrb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp a b
 have hleft := localUnary (call l (.var 0 ::ᵥ nil)) _ _ (HistoryOrder.StepProof.localSym _ _ he)
 have hright := localUnary (call r (.var 0 ::ᵥ nil)) _ _ (HistoryOrder.StepProof.localSym _ _ he)
 simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hleft hright
 have ha := localTrans _ _ _ hleft (.base hla)
 have hb := localTrans _ _ _ hright (.base hrb)
 have hpair := callCongruence ptag (call l (code ::ᵥ nil) ::ᵥ call r (code ::ᵥ nil) ::ᵥ nil)
  (a ::ᵥ b ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact ha
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 exact ⟨localTrans _ _ _ hpair he⟩

/-- ALL raw codes admit original pair reconstruction in PA, without native
unpairing, list images, semantic reflection or additional registry programs. -/
theorem pairEta {n ctx : Nat} (p : Program n) (ptag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ptag l r code)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property ptag l r code
 let H := secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm code)
 let C := liftTerm (liftTerm code)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall ptag A B) C) :=
  .hypothesis List.mem_cons_self
 obtain ⟨hout⟩ := reconstructAt p [H] ptag l r hp hl hr A B C hh
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,C,weakenProperty] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hi⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨he⟩ := HBQuantifier.existentialElimination T (firstBody ptag code) Q ⟨hi⟩
 obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p ptag hp ctx code
 exact ⟨.mp he hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionPairProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionPairProof
