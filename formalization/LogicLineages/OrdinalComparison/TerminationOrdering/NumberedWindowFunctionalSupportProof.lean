module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalCasesTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates NumberedFiniteUniverse NumberedWindowOccurrenceTargets

theorem finiteWeakBudget {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop} {Gamma : List Ty}
    (xs : List (OriginalPacked Symbol arity Gamma)) (source : OriginalPacked Symbol arity Gamma → OriginalPacked Symbol arity Gamma)
    (h : ∀ p∈xs,WeakCertificate symbols S above (source p) p) : ∃ B,∀ p∈xs,WeakAt symbols S above B (source p) p := by
  exact OriginalDerivationBudgetSupportProof.finiteBounds (fun B p => WeakAt symbols S above B (source p) p)
    (fun n m hnm p hp => NumberedWindowListCasesProof.weakRaise hnm hp) xs h

theorem selfTargetsTrace {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop} {Gamma types : List Ty}
    (B k : Nat) (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (values : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes) (extraValues : AuxArguments Symbol arity Gamma extraTypes)
    (target : Arguments Symbol arity Gamma types) (hk : B≤k)
    (hb : ArgumentsRepresent Symbol arity B Gamma (headArguments arity f) base values)
    (he : ArgumentsRepresent Symbol arity B Gamma extraTypes extras extraValues)
    (hf : HeadInWindow arity symbols S f)
    (hvg : NumberedUniverseBindingTargets.GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) values)
    (heg : NumberedUniverseBindingTargets.GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) extraValues)
    (ht : argumentTypesAllowed (fun t => t∈S) target)
    (hh : argumentsAllowed (HeadInWindow arity symbols S) target)
    (h : ∀ p∈RecursiveComparison.argumentList target,WeakAt symbols S above B ⟨p.1,.marked f p.1 base extraTypes extras⟩ p) :
    PointwiseWindowTrace symbols S above (argumentList (NumberedRewriteReduction.selfArguments k f values extraTypes extraValues types))
      (canonicalList 0 (RecursiveComparison.argumentList target)) := by
  induction types with
  | nil => cases target; exact .nil
  | cons sigma types ih => cases target with
    | cons q rest =>
      have hrep : Represents Symbol arity B Gamma sigma (.marked f sigma base extraTypes extras)
          (.numbered k f sigma values extraTypes extraValues) := .numbered f sigma base values extraTypes extras extraValues k hk hb he
      have hroot := FiniteQueryPrimitivesSupportProof.rootType q ht.1
      have hgood : InUniverse symbols S (.numbered k f sigma values extraTypes extraValues) :=
        ⟨⟨hroot,hvg.1,heg.1⟩,hf,hvg.2,heg.2⟩
      exact .cons (h ⟨sigma,q⟩ (List.mem_cons_self ..) _ hrep hgood ⟨ht.1,hh.1⟩)
        (ih rest ht.2 hh.2 (fun p hp => h p (List.mem_cons_of_mem _ hp)))


end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalSupportProof
