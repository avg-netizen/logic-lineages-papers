module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationFunctionalSupportProof

@[expose] public section
/-! Remaining literal Select/F-Abs/Copy constructor cases. All assumptions
are explicit constructor induction hypotheses; no unconditional simulation or
termination claim is made by this module alone.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationFunctionalCasesProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedDerivationCertificates NumberedDerivationFunctionalSupportProof

theorem fAbsCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {sigma tau : Ty} (f : Head Symbol)
    (ss : Arguments Symbol arity Gamma (headArguments arity f)) (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (t : MarkedTerm Symbol arity (sigma::Gamma) tau)
    (ih : WeakCertificate above ⟨tau,RecursiveComparison.openMarked f sigma tau ss types extras⟩ ⟨tau,t⟩) :
    WeakCertificate above ⟨.arrow sigma tau,.marked f (.arrow sigma tau) ss types extras⟩ ⟨.arrow sigma tau,.lam t⟩ := by
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+1,?_⟩
  intro Q hQ
  obtain ⟨k,base,extraValues,hk,he,hbase,hextra⟩ := NumberedOriginalAngleSupportProof.numberedRepresentation f ss types extras Q hQ
  subst Q
  have hkB : B≤k-1 := by omega
  have hbody := openedRepresentation B (k-1) f sigma tau ss base types extras extraValues hkB
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase)
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) extras extraValues hextra)
  obtain ⟨n,hn⟩ := hB (openNumbered (k-1) f sigma tau base types extraValues) hbody
  have htyped := (NumberedTraceContextsProof.typedPresentation Symbol arity above (sigma::Gamma) tau n _ (canonical 0 t)).mp hn
  have hfinish := NumberedTraceContextsProof.typedToPacked
    (NumberedTraceContextsProof.lambdaContext Symbol arity above Gamma sigma tau n _ (canonical 0 t) htyped)
  have hraw := RawStep.abs (Symbol:=Symbol) (arity:=arity) (above:=above) (Gamma:=Gamma) (sigma:=sigma) (tau:=tau) (k-1) f base types extraValues
  have hk' : (k-1)+1=k := by omega
  rw [hk'] at hraw
  exact ⟨1+n,.trans (.raw _ _ hraw) hfinish⟩

theorem copyCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} (f g : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (ts : Arguments Symbol arity Gamma (headArguments arity g)) (hhead : RecursiveComparison.headAbove above f g)
    (ih : ∀ p∈RecursiveComparison.argumentList ts,WeakCertificate above ⟨p.1,.marked f p.1 ss types extras⟩ p) :
    WeakCertificate above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩ := by
  obtain ⟨B,hB⟩ := finiteWeakBudget (RecursiveComparison.argumentList ts) (fun p => ⟨p.1,.marked f p.1 ss types extras⟩) ih
  refine ⟨B+1,?_⟩
  intro Q hQ
  obtain ⟨k,base,extraValues,hk,he,hbase,hextra⟩ := NumberedOriginalAngleSupportProof.numberedRepresentation f ss types extras Q hQ
  subst Q
  have hkB : B≤k-1 := by omega
  have hpoint := selfTargetsTrace B (k-1) f ss base types extras extraValues ts hkB
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase)
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) extras extraValues hextra) hB
  obtain ⟨n,target,htarget,htr⟩ := NumberedOccurrenceTransportProof.pointwiseTupleTrace Symbol arity above Gamma _
    (NumberedRewriteReduction.selfArguments (k-1) f base types extraValues (headArguments arity g))
    (canonicalList 0 (RecursiveComparison.argumentList ts)) hpoint
  have hperm : (argumentList target).Perm (argumentList (canonicalArguments 0 ts)) := by
    rw [htarget,NumberedDerivationWeakBasicCasesProof.canonicalArgumentList]
  have hfinish := NumberedTraceContextsProof.typedToPacked (NumberedTraceContextsProof.ordinaryContext Symbol arity above Gamma g n _ target htr)
  have hraw := RawStep.copy (Symbol:=Symbol) (arity:=arity) (above:=above) (Gamma:=Gamma) (k-1) f g base types extraValues hhead
  have hk' : (k-1)+1=k := by omega
  rw [hk'] at hraw
  exact ⟨(1+n)+0,.trans (.trans (.raw _ _ hraw) hfinish)
    (.equivalent (.ordinary g g target (canonicalArguments 0 ts) rfl rfl hperm))⟩

theorem selectCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {sigma tau : Ty} (f : Head Symbol)
    (ss : Arguments Symbol arity Gamma (headArguments arity f)) (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes)
    (types : List Ty) (q : MarkedTerm Symbol arity Gamma sigma) (r t : MarkedTerm Symbol arity Gamma tau)
    (suffix : sigma=arrows types tau)
    (hq : (⟨sigma,q⟩ : OriginalPacked Symbol arity Gamma)∈RecursiveComparison.argumentList ss++RecursiveComparison.argumentList extras)
    (happly : applyOriginalWith q (fun v => .var v) (RecursiveComparison.selfArguments f ss extraTypes extras types) suffix=some r)
    (ih : WeakCertificate above ⟨tau,r⟩ ⟨tau,t⟩) :
    WeakCertificate above ⟨tau,.marked f tau ss extraTypes extras⟩ ⟨tau,t⟩ := by
  cases suffix
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+types.length+1,?_⟩
  intro Q hQ
  obtain ⟨k,base,extraValues,hk,he,hbase,hextra⟩ := NumberedOriginalAngleSupportProof.numberedRepresentation f ss extraTypes extras Q hQ
  subst Q
  obtain ⟨A,hAmem,hA⟩ := selectedRepresentation (B+types.length+1) f ss base extraTypes extras extraValues hbase hextra q hq
  have hbase' := NumberedPositiveMarkProof.lowerArguments (Nat.le_succ (B+types.length)) ss base hbase
  have hextra' := NumberedPositiveMarkProof.lowerArguments (Nat.le_succ (B+types.length)) extras extraValues hextra
  have hkB : B+types.length≤k-1 := by omega
  have hself := selfRepresentation (B+types.length) (k-1) f ss base extraTypes extras extraValues hkB hbase' hextra' types
  have hA' := NumberedRewriteSyntaxProof.budgetLowering Symbol arity (B+types.length+1) (B+types.length)
    (Nat.le_succ (B+types.length)) Gamma (arrows types tau) q A hA
  have hAsub : Represents Symbol arity (B+types.length) Gamma (arrows types tau)
      (Source.SourceMarkedBinding.substituteTerm q (fun v => .var v)) A := by
    rw [SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Gamma (arrows types tau) q]
    exact hA'
  obtain ⟨R,hpath,hR⟩ := NumberedOriginalAngleProof.generalOriginalAngle Symbol arity above B Gamma Gamma
    (arrows types tau) q (fun v => .var v) types tau (RecursiveComparison.selfArguments f ss extraTypes extras types) rfl r happly
    A (NumberedRewriteReduction.selfArguments (k-1) f base extraTypes extraValues types) hAsub hself
  obtain ⟨m,hm⟩ := NumberedPrimaryEquivalenceProof.rawPathTrace Symbol arity above Gamma tau _ R hpath
  obtain ⟨n,hn⟩ := hB R hR
  have hraw := RawStep.select (Symbol:=Symbol) (arity:=arity) (above:=above) (Gamma:=Gamma)
    (k-1) f base extraTypes extraValues types A hAmem
  have hk' : (k-1)+1=k := by omega
  rw [hk'] at hraw
  exact ⟨(1+m)+n,.trans (.trans (.raw _ _ hraw) hm) hn⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationFunctionalCasesProof
