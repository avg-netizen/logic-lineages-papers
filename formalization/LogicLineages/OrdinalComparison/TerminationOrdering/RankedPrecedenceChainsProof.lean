module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsProof
open Source Source.SourceMarkedSyntax RankedPrecedenceCertificate

theorem telescope (values : Nat → Nat) (length : Nat)
    (h : ∀ i, i < length → values (i+1) < values i) : length + values length ≤ values 0 := by
  induction length with
  | zero => simp
  | succ length ih =>
    have hp := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self length)))
    have hl := h length (Nat.lt_succ_self length)
    omega

theorem actualSymbolChainBound : RankedPrecedenceChainsTargets.ActualSymbolChainBound := by
  intro n table rank hc length values he
  have hr := ((RankedPrecedenceCertificateProof.actualRankCertificateTest n table rank).mp hc).2
  have ht := telescope (fun i => (rank (values i)).val) length (fun i hi => (hr _ _).mp (he i hi))
  have hb := (rank (values 0)).isLt
  exact ⟨ht,by omega⟩

theorem headBound {n : Nat} (rank : Fin n → Fin n) (f : Head (Fin n)) : headRank rank f ≤ n+1 := by
  cases f <;> simp only [headRank]
  all_goals first | omega | rename_i f; have h := (rank f).isLt; omega

theorem actualHeadChainBound : RankedPrecedenceChainsTargets.ActualHeadChainBound := by
  intro n table rank hc length values he
  have ht := telescope (fun i => headRank rank (values i)) length (fun i hi =>
    (RankedPrecedenceCertificateProof.actualHeadRankCalibration n table rank hc _ _).mp (he i hi))
  have hb := headBound rank (values 0)
  exact ⟨ht,by omega⟩

theorem actualHeadClassRank : RankedPrecedenceChainsTargets.ActualHeadClassRank := by
  intro n table rank hc f g
  have hi := ((RankedPrecedenceCertificateProof.actualRankCertificateTest n table rank).mp hc).1
  have hr (f g : Fin n) : (rank f).val = (rank g).val ↔ f = g := by
    constructor
    · intro h; exact hi (Fin.ext h)
    · intro h; subst g; rfl
  cases f <;> cases g <;>
    simp [RecursiveComparison.headEquivalent,RecursiveComparison.headClass,headRank,hr]

theorem actualHeadPrecedenceCompatibility : RankedPrecedenceChainsTargets.ActualHeadPrecedenceCompatibility := by
  intro n table rank hc f f' g g' hf hg
  have hfr := (actualHeadClassRank n table rank hc f f').mp hf
  have hgr := (actualHeadClassRank n table rank hc g g').mp hg
  rw [RankedPrecedenceCertificateProof.actualHeadRankCalibration n table rank hc f g,
    RankedPrecedenceCertificateProof.actualHeadRankCalibration n table rank hc f' g',hfr,hgr]

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsProof
