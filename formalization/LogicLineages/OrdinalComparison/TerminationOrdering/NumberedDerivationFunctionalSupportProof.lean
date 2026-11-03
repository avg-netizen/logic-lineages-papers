module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationWeakBasicCasesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationFunctionalSupportProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedDerivationCertificates

theorem renamedArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (n : Nat) (args : Arguments Symbol arity Gamma types) (values : AuxArguments Symbol arity Gamma types)
    (rho : Renaming Gamma Delta) (h : ArgumentsRepresent Symbol arity n Gamma types args values) :
    ArgumentsRepresent Symbol arity n Delta types (Source.SourceMarkedBinding.renameArguments args rho)
      (NumberedRewriteSyntax.renameArguments values rho) := by
  induction types with
  | nil => cases h; exact .nil
  | cons sigma types ih => cases h with
    | cons q Q rest values hq hr =>
      exact .cons _ _ _ _
        (NumberedRewriteSyntaxProof.renamingCorrespondence Symbol arity n Gamma Delta sigma q Q rho hq)
        (ih rest values hr)

theorem selfRepresentation {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (B k : Nat) (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (values : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes) (extraValues : AuxArguments Symbol arity Gamma extraTypes)
    (hk : B≤k) (hb : ArgumentsRepresent Symbol arity B Gamma (headArguments arity f) base values)
    (he : ArgumentsRepresent Symbol arity B Gamma extraTypes extras extraValues) (types : List Ty) :
    ArgumentsRepresent Symbol arity B Gamma types (RecursiveComparison.selfArguments f base extraTypes extras types)
      (NumberedRewriteReduction.selfArguments k f values extraTypes extraValues types) := by
  induction types with
  | nil => exact .nil
  | cons sigma types ih => exact .cons _ _ _ _ (.numbered f sigma base values extraTypes extras extraValues k hk hb he) ih

theorem openedRepresentation {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (B k : Nat) (f : Head Symbol) (sigma tau : Ty)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (values : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types) (extraValues : AuxArguments Symbol arity Gamma types)
    (hk : B≤k) (hb : ArgumentsRepresent Symbol arity B Gamma (headArguments arity f) base values)
    (he : ArgumentsRepresent Symbol arity B Gamma types extras extraValues) :
    Represents Symbol arity B (sigma::Gamma) tau (RecursiveComparison.openMarked f sigma tau base types extras)
      (openNumbered k f sigma tau values types extraValues) := by
  refine .numbered f tau _ _ (types++[sigma]) _ _ k hk ?_ ?_
  · exact renamedArguments B base values (Renaming.weaken Gamma sigma) hb
  · exact NumberedOriginalAngleSupportProof.appendRepresentation _ _ _ _
      (renamedArguments B extras extraValues (Renaming.weaken Gamma sigma) he) (.cons _ _ _ _ (.var .here) .nil)

theorem selectedRepresentation {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (B : Nat) (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (values : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types) (extraValues : AuxArguments Symbol arity Gamma types)
    (hb : ArgumentsRepresent Symbol arity B Gamma (headArguments arity f) base values)
    (he : ArgumentsRepresent Symbol arity B Gamma types extras extraValues)
    (q : MarkedTerm Symbol arity Gamma tau) (hq : (⟨tau,q⟩ : OriginalPacked Symbol arity Gamma)∈
      RecursiveComparison.argumentList base++RecursiveComparison.argumentList extras) :
    ∃ Q : AuxTerm Symbol arity Gamma tau,(⟨tau,Q⟩ : Packed Symbol arity Gamma)∈argumentList values++argumentList extraValues ∧
      Represents Symbol arity B Gamma tau q Q := by
  have hcombined := NumberedDerivationListCasesProof.appendRelation
    (NumberedOccurrenceTransportProof.argumentsToList Symbol arity B Gamma _ base values hb)
    (NumberedOccurrenceTransportProof.argumentsToList Symbol arity B Gamma _ extras extraValues he)
  obtain ⟨Q,hQ,hrel⟩ := NumberedDerivationListCasesProof.representedMember hcombined ⟨tau,q⟩ hq
  obtain ⟨A,rfl,hA⟩ := hrel
  exact ⟨A,hQ,hA⟩

theorem finiteWeakBudget {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop} {Gamma : List Ty}
    (xs : List (OriginalPacked Symbol arity Gamma)) (source : OriginalPacked Symbol arity Gamma → OriginalPacked Symbol arity Gamma)
    (h : ∀ p∈xs,WeakCertificate above (source p) p) : ∃ B,∀ p∈xs,WeakAt above B (source p) p := by
  exact OriginalDerivationBudgetSupportProof.finiteBounds (fun B p => WeakAt above B (source p) p)
    (fun n m hnm p hp => NumberedDerivationListCasesProof.weakRaise hnm hp) xs h

theorem selfTargetsTrace {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop} {Gamma types : List Ty}
    (B k : Nat) (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (values : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes) (extraValues : AuxArguments Symbol arity Gamma extraTypes)
    (target : Arguments Symbol arity Gamma types) (hk : B≤k)
    (hb : ArgumentsRepresent Symbol arity B Gamma (headArguments arity f) base values)
    (he : ArgumentsRepresent Symbol arity B Gamma extraTypes extras extraValues)
    (h : ∀ p∈RecursiveComparison.argumentList target,WeakAt above B ⟨p.1,.marked f p.1 base extraTypes extras⟩ p) :
    PointwiseTrace above (argumentList (NumberedRewriteReduction.selfArguments k f values extraTypes extraValues types))
      (canonicalList 0 (RecursiveComparison.argumentList target)) := by
  induction types with
  | nil => cases target; exact .nil
  | cons sigma types ih => cases target with
    | cons q rest =>
      have hrep : Represents Symbol arity B Gamma sigma (.marked f sigma base extraTypes extras)
          (.numbered k f sigma values extraTypes extraValues) := .numbered f sigma base values extraTypes extras extraValues k hk hb he
      exact .cons (h ⟨sigma,q⟩ (List.mem_cons_self ..) _ hrep)
        (ih rest (fun p hp => h p (List.mem_cons_of_mem _ hp)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationFunctionalSupportProof
