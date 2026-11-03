module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationListCasesProof

@[expose] public section
/-! Actual Var/Abs/Fun/Put/Stat induction cases. Certificate premises below
are EXPLICIT induction hypotheses, not assumed source suppliers; the final
five-relation induction remains necessary for an unconditional theorem.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationWeakBasicCasesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedTraceContexts NumberedOccurrenceTransport NumberedDerivationSimulation NumberedDerivationCertificates

theorem canonicalArgumentList {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (n : Nat) (args : Arguments Symbol arity Gamma types) :
    argumentList (canonicalArguments n args)=canonicalList n (RecursiveComparison.argumentList args) := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest => exact congrArg (List.cons (canonicalPacked n ⟨sigma,q⟩)) (ih rest)

theorem pointwiseTupleSource {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma types : List Ty} (target : AuxArguments Symbol arity Gamma types) (values : List (Packed Symbol arity Gamma))
    (h : PointwiseTrace above values (argumentList target)) :
    ∃ (n : Nat) (source : AuxArguments Symbol arity Gamma types),argumentList source=values ∧
      TupleTrace Symbol arity above Gamma types n source target := by
  induction types generalizing values with
  | nil => cases target; cases h; exact ⟨0,.nil,rfl,.equivalent .nil⟩
  | cons sigma types ih => cases target with
    | cons q rest => cases h with
      | @cons R _ values _ hq hr =>
        rcases R with ⟨tau,R⟩
        obtain ⟨m,hm⟩ := hq
        have ht : tau=sigma := NumberedPrimaryEquivalenceProof.traceTypePreservation Symbol arity above Gamma m _ _ hm
        cases ht
        obtain ⟨n,source,he,hsource⟩ := ih rest values hr
        exact ⟨m+n,.cons R source,congrArg (List.cons (⟨sigma,R⟩ : Packed Symbol arity Gamma)) he,
          NumberedTraceContextsProof.tupleCons Symbol arity above Gamma types sigma m n R q source rest
            ((NumberedTraceContextsProof.typedPresentation Symbol arity above Gamma sigma m R q).mp hm) hsource⟩

theorem varCase {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} {tau : Ty} (v : Variable Gamma tau) : WeakCertificate (arity:=arity) above ⟨tau,.var v⟩ ⟨tau,.var v⟩ := by
  refine ⟨0,?_⟩
  intro Q hQ
  have he : Q=AuxTerm.var v := NumberedRepresentationRigidityProof.unmarkedRepresentation Symbol arity 0 Gamma tau (.var v) Q (.var v) hQ
  subst Q
  exact ⟨0,.equivalent (.refl _)⟩

theorem absCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {sigma tau : Ty} (s t : MarkedTerm Symbol arity (sigma::Gamma) tau)
    (ih : WeakCertificate above ⟨tau,s⟩ ⟨tau,t⟩) : WeakCertificate above ⟨.arrow sigma tau,.lam s⟩ ⟨.arrow sigma tau,.lam t⟩ := by
  obtain ⟨B,hB⟩ := ih
  refine ⟨B,?_⟩
  intro Q hQ
  obtain ⟨body,he,hbody⟩ := NumberedPositiveMarkProof.lambdaRepresentation (.lam s) Q hQ sigma tau s rfl
  have hQeq : Q=AuxTerm.lam body := by injection he
  subst Q
  obtain ⟨n,hn⟩ := hB body hbody
  have ht := (NumberedTraceContextsProof.typedPresentation Symbol arity above (sigma::Gamma) tau n body (canonical 0 t)).mp hn
  exact ⟨n,NumberedTraceContextsProof.typedToPacked (NumberedTraceContextsProof.lambdaContext Symbol arity above Gamma sigma tau n body (canonical 0 t) ht)⟩

theorem funCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} (f g : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (ts : Arguments Symbol arity Gamma (headArguments arity g)) (matched : List (OriginalPacked Symbol arity Gamma))
    (heq : RecursiveComparison.headEquivalent f g) (hresult : headResult f=headResult g)
    (hp : (RecursiveComparison.argumentList ts).Perm matched)
    (ih : MatchCertificate above (RecursiveComparison.argumentList ss) matched) :
    WeakCertificate above ⟨headResult f,.ordinary f ss⟩ ⟨headResult g,.ordinary g ts⟩ := by
  obtain ⟨B,hB⟩ := ih
  refine ⟨B,?_⟩
  intro Q hQ
  obtain ⟨base,he,hbase⟩ := NumberedPositiveMarkProof.ordinaryRepresentation (.ordinary f ss) Q hQ f ss rfl
  have hQeq : Q=AuxTerm.ordinary f base := by injection he
  subst Q
  have hpoint := hB (argumentList base) (NumberedOccurrenceTransportProof.argumentsToList Symbol arity B Gamma _ ss base hbase)
  obtain ⟨n,target,htarget,htr⟩ := NumberedOccurrenceTransportProof.pointwiseTupleTrace Symbol arity above Gamma _ base (canonicalList 0 matched) hpoint
  have hp' : (argumentList target).Perm (argumentList (canonicalArguments 0 ts)) := by
    rw [htarget,canonicalArgumentList]
    exact (hp.map (canonicalPacked 0)).symm
  have hfirst := NumberedTraceContextsProof.typedToPacked (NumberedTraceContextsProof.ordinaryContext Symbol arity above Gamma f n base target htr)
  exact ⟨n+0,.trans hfirst (.equivalent (.ordinary f g target (canonicalArguments 0 ts) heq hresult hp'))⟩

theorem putCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} (f : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (t : MarkedTerm Symbol arity Gamma (headResult f))
    (ih : WeakCertificate above ⟨headResult f,.marked f (headResult f) ss [] .nil⟩ ⟨headResult f,t⟩) :
    WeakCertificate above ⟨headResult f,.ordinary f ss⟩ ⟨headResult f,t⟩ := by
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+1,?_⟩
  intro Q hQ
  obtain ⟨base,he,hbase⟩ := NumberedPositiveMarkProof.ordinaryRepresentation (.ordinary f ss) Q hQ f ss rfl
  have hQeq : Q=AuxTerm.ordinary f base := by injection he
  subst Q
  have hr : Represents Symbol arity B Gamma (headResult f) (.marked f (headResult f) ss [] .nil)
      (.numbered B f (headResult f) base [] .nil) := .numbered f (headResult f) ss base [] .nil .nil B (Nat.le_refl _)
        (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase) .nil
  obtain ⟨n,hn⟩ := hB _ hr
  exact ⟨1+n,.trans (.raw _ _ (.put B f base)) hn⟩

theorem statCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} (f g : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (ts : Arguments Symbol arity Gamma (headArguments arity g)) (heq : RecursiveComparison.headEquivalent f g)
    (ih : MultiCertificate above (RecursiveComparison.argumentList ss) (RecursiveComparison.argumentList ts)) :
    WeakCertificate above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩ := by
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+1,?_⟩
  intro Q hQ
  obtain ⟨k,base,extraValues,hk,he,hbase,hextra⟩ := NumberedOriginalAngleSupportProof.numberedRepresentation f ss types extras Q hQ
  subst Q
  have hbase' := NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase
  obtain ⟨middle,hmulti,hpoint⟩ := hB (argumentList base) (NumberedOccurrenceTransportProof.argumentsToList Symbol arity B Gamma _ ss base hbase')
  have hpoint' : PointwiseTrace above middle (argumentList (canonicalArguments 0 ts)) := by
    rw [canonicalArgumentList]
    exact hpoint
  obtain ⟨n,target,htarget,htr⟩ := pointwiseTupleSource (canonicalArguments 0 ts) middle hpoint'
  have hmulti' : PrimitiveMultiset (argumentList base) (argumentList target) := by rw [htarget]; exact hmulti
  have hk' : (k-1)+1=k := by omega
  have hraw := RawStep.mul (Symbol:=Symbol) (arity:=arity) (above:=above) (Gamma:=Gamma)
    (k-1) f g base types extraValues target heq hmulti'
  rw [hk'] at hraw
  have hfinish := NumberedTraceContextsProof.typedToPacked (NumberedTraceContextsProof.ordinaryContext Symbol arity above Gamma g n target (canonicalArguments 0 ts) htr)
  exact ⟨1+n,.trans (.raw _ _ hraw) hfinish⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationWeakBasicCasesProof
