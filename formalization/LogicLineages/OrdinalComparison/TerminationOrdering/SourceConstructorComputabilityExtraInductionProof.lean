module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySuccessorStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExtraInductionProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedFiniteUniverse
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceConstructorComputability SourceConstructorComputabilityMembersProof
open SourceConstructorComputabilityExpansionProof SourceConstructorComputabilitySuccessorStepProof
open SourceConstructorComputabilityInduction RankedPrecedenceCertificate

variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

theorem numberedAtSuccessor
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true)
    (head : Nat) (values : List Nat) (k : Nat)
    (hlowerHead : ∀ head' : Nat, head' < head → ∀ values' : List Nat,
      Acc (Descent arity Gamma ctx) values' → AtBase arity Gamma context ctx scalar rank head' values')
    (hlowerBase : ∀ values' : List Nat, Descent arity Gamma ctx values' values →
      AtBase arity Gamma context ctx scalar rank head values')
    (hlowerLabel : NumberedAt arity Gamma context ctx scalar rank head values k) :
    NumberedAt arity Gamma context ctx scalar rank head values (k+1) := by
  have extraInduction : ∀ extraValues : List Nat, Acc (Descent arity Gamma ctx) extraValues →
      ∀ (f : Head (Fin n)) (tau : Ty)
        (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
        (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types),
        headRank rank f = head → (ArgumentValues ctx base).Perm values →
        ArgumentValues ctx extras = extraValues →
        InUniverse ctx.1.1 ctx.1.2 (.numbered (k+1) f tau base types extras) →
        ArgumentsC context ctx scalar base → ArgumentsC context ctx scalar extras →
        TermC context ctx scalar (.numbered (k+1) f tau base types extras) := by
    intro extraValues hacc
    induction hacc with
    | intro extraValues hacc ihe =>
      intro f tau base types extras hhead hbase hextra hg hb he
      apply numberedExpansion hc hclosed hcal rank hrank (k+1) f tau base types extras hg hb he
      intro g base' types' extras' hr hbperm heq hgood hcb hce
      have hghead : headRank rank g = head := hr.trans hhead
      have hgbase : (ArgumentValues ctx base').Perm values := hbperm.trans hbase
      apply numberedSuccessorStep hc hclosed hcal rank hrank k g tau base' types' extras' hgood hcb hce
      · intro smaller args hlt hargs hca
        have hlt' : headRank rank smaller < head := by rw [←hghead]; exact hlt
        exact (hlowerHead (headRank rank smaller) hlt' (ArgumentValues ctx args)
          (argumentsAccessible hc hclosed hcal hca)).2 smaller args rfl (List.Perm.refl _) hargs hca
      · intro same args hrankeq hd hargs hca
        exact (hlowerBase (ArgumentValues ctx args) (descentPerm hgbase hd)).2
          same args (hrankeq.trans hghead) (List.Perm.refl _) hargs hca
      · intro args hd hargs hca
        exact (hlowerBase (ArgumentValues ctx args) (descentPerm hgbase hd)).1 (k+1)
          g tau args types' extras' hghead (List.Perm.refl _) hargs hca hce
      · intro upsilon extraTypes more hmore hcmore
        exact hlowerLabel g upsilon base' extraTypes more hghead hgbase hmore hcb hcmore
      · intro more hd hmore hcmore
        have hd' : Descent arity Gamma ctx (ArgumentValues ctx more) extraValues :=
          descentPerm (List.Perm.of_eq (heq.trans hextra)) hd
        exact ihe _ hd' g tau base' types' more hghead hgbase rfl hmore hcb hcmore
  intro f tau base types extras hhead hbase hg hb he
  exact extraInduction (ArgumentValues ctx extras) (argumentsAccessible hc hclosed hcal he)
    f tau base types extras hhead hbase rfl hg hb he
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExtraInductionProof
