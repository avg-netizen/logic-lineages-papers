module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowBasicCasesTargets

@[expose] public section
/-! Actual Var/Abs/Fun/Put/Stat induction cases. Certificate premises below
are EXPLICIT induction hypotheses, not assumed source suppliers; the final
five-relation induction remains necessary for an unconditional theorem.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowBasicCasesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedTraceContexts NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates NumberedFiniteUniverse NumberedWindowTraces NumberedWindowReduction NumberedWindowBasicCasesTargets

theorem canonicalArgumentList {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (n : Nat) (args : Arguments Symbol arity Gamma types) :
    argumentList (canonicalArguments n args)=canonicalList n (RecursiveComparison.argumentList args) := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest => exact congrArg (List.cons (canonicalPacked n ⟨sigma,q⟩)) (ih rest)

theorem sourceOccurrences {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma types : List Ty} (args : Arguments Symbol arity Gamma types)
    (ht : argumentTypesAllowed (fun t => t∈S) args)
    (hh : argumentsAllowed (HeadInWindow arity symbols S) args) :
    OriginalGoodList symbols S (RecursiveComparison.argumentList args) := by
  induction types with
  | nil => cases args; intro q hq; cases hq
  | cons sigma types ih => cases args with
    | cons q rest =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨ht.1,hh.1⟩
      · exact ih rest ht.2 hh.2 p hp

theorem auxOccurrences {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma types : List Ty} (args : AuxArguments Symbol arity Gamma types)
    (ht : auxArgumentTypesAllowed (fun t => t∈S) args)
    (hh : auxArgumentsAllowed (HeadInWindow arity symbols S) args) :
    GoodList symbols S (argumentList args) :=
  (NumberedUniverseOperationsProof.actualArgumentOccurrences Symbol arity (fun t => t∈S)
    (HeadInWindow arity symbols S) Gamma types args).mp ⟨ht,hh⟩

theorem varCase : ActualVariable := by
  intro Symbol arity symbols S above Gamma tau v
  refine ⟨0,?_⟩
  intro Q hQ hgood htarget
  have he : Q=AuxTerm.var v := NumberedRepresentationRigidityProof.unmarkedRepresentation Symbol arity 0 Gamma tau (.var v) Q (.var v) hQ
  subst Q
  exact ⟨0,.equivalent (.refl _)⟩

theorem absCase : ActualAbstraction := by
  intro Symbol arity symbols S above Gamma sigma tau s t ih
  obtain ⟨B,hB⟩ := ih
  refine ⟨B,?_⟩
  intro Q hQ hgood htarget
  obtain ⟨body,he,hbody⟩ := NumberedPositiveMarkProof.lambdaRepresentation (.lam s) Q hQ sigma tau s rfl
  have hQeq : Q=AuxTerm.lam body := by injection he
  subst Q
  obtain ⟨n,hn⟩ := hB body hbody ⟨hgood.1.2.2,hgood.2⟩ ⟨htarget.1.2.2,htarget.2⟩
  have ht := (NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above (sigma::Gamma) tau n body (canonical 0 t)).mp hn
  exact ⟨n,NumberedWindowTracesProof.typedToPacked (NumberedWindowTracesProof.lambdaContext Symbol arity symbols S above Gamma sigma tau n body (canonical 0 t) ht)⟩

theorem funCase : ActualFunction := by
  intro Symbol arity symbols S above Gamma f g ss ts matched heq hresult hp ih
  obtain ⟨B,hB⟩ := ih
  refine ⟨B,?_⟩
  intro Q hQ hgood htarget
  obtain ⟨base,he,hbase⟩ := NumberedPositiveMarkProof.ordinaryRepresentation (.ordinary f ss) Q hQ f ss rfl
  have hQeq : Q=AuxTerm.ordinary f base := by injection he
  subst Q
  have hpoint := hB (argumentList base) (NumberedOccurrenceTransportProof.argumentsToList Symbol arity B Gamma _ ss base hbase)
    (auxOccurrences symbols S base hgood.1.2 hgood.2.2)
    (fun p hpMem => sourceOccurrences symbols S ts htarget.1.2 htarget.2.2 p (hp.mem_iff.mpr hpMem))
  obtain ⟨n,target,htargetList,htr⟩ := NumberedWindowOccurrenceProof.pointwiseTupleTarget Symbol arity symbols S above Gamma _ base (canonicalList 0 matched) hpoint
  have hp' : (argumentList target).Perm (argumentList (canonicalArguments 0 ts)) := by
    rw [htargetList,canonicalArgumentList]
    exact (hp.map (canonicalPacked 0)).symm
  have hfirst := NumberedWindowTracesProof.typedToPacked (NumberedWindowTracesProof.ordinaryContext Symbol arity symbols S above Gamma f n base target htr)
  exact ⟨n+0,.trans hfirst (.equivalent (.ordinary f g target (canonicalArguments 0 ts) hgood.2.1 htarget.2.1 heq hresult hp'))⟩

theorem putCase : ActualPut := by
  intro Symbol arity symbols S above Gamma f ss t ih
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+1,?_⟩
  intro Q hQ hgood htarget
  obtain ⟨base,he,hbase⟩ := NumberedPositiveMarkProof.ordinaryRepresentation (.ordinary f ss) Q hQ f ss rfl
  have hQeq : Q=AuxTerm.ordinary f base := by injection he
  subst Q
  have hr : Represents Symbol arity B Gamma (headResult f) (.marked f (headResult f) ss [] .nil)
      (.numbered B f (headResult f) base [] .nil) := .numbered f (headResult f) ss base [] .nil .nil B (Nat.le_refl _)
        (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase) .nil
  obtain ⟨n,hn⟩ := hB _ hr ⟨⟨hgood.1.1,hgood.1.2,trivial⟩,hgood.2.1,hgood.2.2,trivial⟩ htarget
  exact ⟨1+n,.trans (.raw _ _ (.put B f base)) hn⟩

theorem statCase : ActualStatus := by
  intro Symbol arity symbols S above Gamma f g ss types extras ts heq ih
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+1,?_⟩
  intro Q hQ hgood htarget
  obtain ⟨k,base,extraValues,hk,he,hbase,hextra⟩ := NumberedOriginalAngleSupportProof.numberedRepresentation f ss types extras Q hQ
  subst Q
  have hbase' := NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase
  obtain ⟨middle,hmulti,hpoint⟩ := hB (argumentList base) (NumberedOccurrenceTransportProof.argumentsToList Symbol arity B Gamma _ ss base hbase')
    (auxOccurrences symbols S base hgood.1.2.1 hgood.2.2.1)
    (sourceOccurrences symbols S ts htarget.1.2 htarget.2.2)
  have hpoint' : NumberedWindowOccurrenceTargets.PointwiseWindowTrace symbols S above middle (argumentList (canonicalArguments 0 ts)) := by
    rw [canonicalArgumentList]
    exact hpoint
  obtain ⟨n,target,htargetList,htr⟩ := NumberedWindowOccurrenceProof.pointwiseTupleSource Symbol arity symbols S above Gamma _ (canonicalArguments 0 ts) middle hpoint'
  have hmulti' : PrimitiveMultiset (argumentList base) (argumentList target) := by rw [htargetList]; exact hmulti
  have hk' : (k-1)+1=k := by omega
  have hraw := WindowStep.mul (Symbol:=Symbol) (arity:=arity) (symbols:=symbols) (S:=S) (above:=above) (Gamma:=Gamma)
    (k-1) f g base types extraValues target heq hmulti' htarget.2.1
  rw [hk'] at hraw
  have hfinish := NumberedWindowTracesProof.typedToPacked (NumberedWindowTracesProof.ordinaryContext Symbol arity symbols S above Gamma g n target (canonicalArguments 0 ts) htr)
  exact ⟨1+n,.trans (.raw _ _ hraw) hfinish⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowBasicCasesProof
