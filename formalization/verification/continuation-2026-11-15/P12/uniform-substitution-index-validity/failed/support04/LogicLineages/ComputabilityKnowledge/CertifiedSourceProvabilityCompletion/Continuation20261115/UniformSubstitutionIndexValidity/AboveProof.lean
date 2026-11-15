module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.AboveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
theorem differenceZeroAbove {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (dtag : Nat)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (index depth gap : Term ctx)
 (hgap : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal index (.add depth (.succ gap)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag index (.succ depth)) .zero)) := by
 have hindex := localTrans _ _ _ hgap
  (localTrans _ _ _ (.base (.arithmetic (.addSucc depth gap)))
   (.base (Support.equalitySymmetry _ _ (successorLeft depth gap))))
 have hcong := callCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := G) dtag
  (index ::ᵥ .succ depth ::ᵥ nil) (.add (.succ depth) gap ::ᵥ .succ depth ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hindex
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive (.succ depth)))
     | succ i => exact Fin.elim0 i)
 obtain ⟨hz⟩ := HistoryDifference.ArithmeticProof.differenceSaturate n p dtag hd ctx (.succ depth) gap
 exact ⟨localTrans _ _ _ hcong (.base hz)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.AboveProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.AboveProof
