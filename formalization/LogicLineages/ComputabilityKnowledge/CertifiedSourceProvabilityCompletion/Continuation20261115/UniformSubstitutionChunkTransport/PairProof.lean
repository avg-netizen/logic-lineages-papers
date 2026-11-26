module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.KindProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.PairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralRawMP.DispatcherSupportProof
/-- Arbitrary raw heads are reconstructed internally from original decoder
graphs. The old bound is forced to successor of the new decoded bound by the
actual relation, not a chosen native image. Kind equations come from checked
classification and KindProof at the eventual caller. -/
theorem canonical {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r k j : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (old new : Term ctx)
 (hrel : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (taskRelation l r old new))
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (old ::ᵥ nil)) (Term.numeral k)))
 (hj : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (new ::ᵥ nil)) (Term.numeral j))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj (.equal old (LiteralSyntaxStep.taskCall ptag k (.succ (call r (new ::ᵥ nil)))))
   (.equal new (LiteralSyntaxStep.taskCall ptag j (call r (new ::ᵥ nil)))))) := by
 obtain ⟨ho⟩ := RelationalSyntaxDepthTransport.ExpansionPairProof.pairEta p ptag l r hp hl hr old
 obtain ⟨hn⟩ := RelationalSyntaxDepthTransport.ExpansionPairProof.pairEta p ptag l r hp hl hr new
 have hb := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrel
 have hpo := callCongruence ptag
  (call l (old ::ᵥ nil) ::ᵥ call r (old ::ᵥ nil) ::ᵥ nil)
  (Term.numeral k ::ᵥ .succ (call r (new ::ᵥ nil)) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hk
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 have hpn := callCongruence ptag
  (call l (new ::ᵥ nil) ::ᵥ call r (new ::ᵥ nil) ::ᵥ nil)
  (Term.numeral j ::ᵥ call r (new ::ᵥ nil) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hj
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive _))
     | succ i => exact Fin.elim0 i)
 have heo := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ ho)) hpo
 have hen := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hn)) hpn
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) heo) hen⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.PairProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.PairProof
