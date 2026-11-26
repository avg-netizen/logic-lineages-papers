module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExtraInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityOrdinaryStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityJointInductionProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceConstructorComputability SourceConstructorComputabilityMembersProof
open SourceConstructorComputabilityExpansionProof SourceConstructorComputabilityOrdinaryStepProof
open SourceConstructorComputabilityExtraInductionProof SourceConstructorComputabilityInduction RankedPrecedenceCertificate

variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

/-- The original lexicographic proof: head rank, accessible actual base
multiset, every finite label, accessible extra multiset, then ordinary omega. -/
theorem jointByRank
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true) :
    ∀ head : Nat, ∀ values : List Nat, Acc (Descent arity Gamma ctx) values →
      AtBase arity Gamma context ctx scalar rank head values := by
  intro head
  induction head using Nat.strong_induction_on with
  | h head ihhead =>
    intro values hacc
    induction hacc with
    | intro values hacc ihbase =>
      have hfinite : ∀ k : Nat, NumberedAt arity Gamma context ctx scalar rank head values k := by
        intro k
        induction k with
        | zero =>
          intro f tau base types extras hhead hbase hg hb he
          apply SourceZeroNumberedComputabilityProof.actualZeroNumberedComputable
            n arity Gamma context ctx scalar hc hclosed hcal f tau base types extras hg
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact (argumentsC_iff base).mp hb p hp
          · exact (argumentsC_iff extras).mp he p hp
        | succ k ihk =>
          exact numberedAtSuccessor hc hclosed hcal rank hrank head values k ihhead ihbase ihk
      refine ⟨hfinite,?_⟩
      intro f base hhead hbase hg hb
      apply ordinaryExpansion hc hclosed hcal rank hrank f base hg hb
      intro g base' hr hp hgood hcb
      have hghead : headRank rank g = head := hr.trans hhead
      have hgbase : (ArgumentValues ctx base').Perm values := hp.trans hbase
      apply ordinaryStep hc hclosed hcal g base' hgood hcb
      · intro k hk
        exact hfinite k g (headResult g) base' [] .nil hghead hgbase hk hcb (by intro p hp; cases hp)
      · intro target hd ht hct
        exact (ihbase (ArgumentValues ctx target) (descentPerm hgbase hd)).2
          g target hghead (List.Perm.refl _) ht hct
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityJointInductionProof
