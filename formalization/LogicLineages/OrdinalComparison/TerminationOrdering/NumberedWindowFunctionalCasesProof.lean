module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalSupportProof

@[expose] public section
/-! Remaining literal Select/F-Abs/Copy constructor cases. All assumptions
are explicit constructor induction hypotheses; no unconditional simulation or
termination claim is made by this module alone.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalCasesProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates NumberedDerivationFunctionalSupportProof NumberedFiniteUniverse NumberedWindowTraces NumberedWindowReduction NumberedWindowFunctionalCasesTargets

theorem fAbsCase : ActualFunctionalAbstraction := by
  intro Symbol arity symbols S above hc Gamma sigma tau f ss types extras t ih
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+1,?_⟩
  intro Q hQ hgood htarget
  obtain ⟨k,base,extraValues,hk,he,hbase,hextra⟩ := NumberedOriginalAngleSupportProof.numberedRepresentation f ss types extras Q hQ
  subst Q
  have hkB : B≤k-1 := by omega
  have hbody := openedRepresentation B (k-1) f sigma tau ss base types extras extraValues hkB
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase)
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) extras extraValues hextra)
  obtain ⟨n,hn⟩ := hB (openNumbered (k-1) f sigma tau base types extraValues) hbody
    (NumberedUniverseBindingProof.actualOpenedNumbered Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S)
      hc (k-1) k Gamma f sigma tau base types extraValues hgood)
    ⟨htarget.1.2.2,htarget.2⟩
  have htyped := (NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above (sigma::Gamma) tau n _ (canonical 0 t)).mp hn
  have hfinish := NumberedWindowTracesProof.typedToPacked
    (NumberedWindowTracesProof.lambdaContext Symbol arity symbols S above Gamma sigma tau n _ (canonical 0 t) htyped)
  have hraw := WindowStep.abs (Symbol:=Symbol) (arity:=arity) (symbols:=symbols) (S:=S) (above:=above) (Gamma:=Gamma) (sigma:=sigma) (tau:=tau) (k-1) f base types extraValues
  have hk' : (k-1)+1=k := by omega
  rw [hk'] at hraw
  exact ⟨1+n,.trans (.raw _ _ hraw) hfinish⟩

theorem copyCase : ActualCopy := by
  intro Symbol arity symbols S above Gamma f g ss types extras ts hhead ih
  obtain ⟨B,hB⟩ := NumberedWindowFunctionalSupportProof.finiteWeakBudget (RecursiveComparison.argumentList ts) (fun p => ⟨p.1,.marked f p.1 ss types extras⟩) ih
  refine ⟨B+1,?_⟩
  intro Q hQ hgood htarget
  obtain ⟨k,base,extraValues,hk,he,hbase,hextra⟩ := NumberedOriginalAngleSupportProof.numberedRepresentation f ss types extras Q hQ
  subst Q
  have hkB : B≤k-1 := by omega
  have hpoint := NumberedWindowFunctionalSupportProof.selfTargetsTrace B (k-1) f ss base types extras extraValues ts hkB
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) ss base hbase)
    (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ B) extras extraValues hextra) hgood.2.1 ⟨hgood.1.2.1,hgood.2.2.1⟩ ⟨hgood.1.2.2,hgood.2.2.2⟩ htarget.1.2 htarget.2.2 hB
  obtain ⟨n,target,htargetList,htr⟩ := NumberedWindowOccurrenceProof.pointwiseTupleTarget Symbol arity symbols S above Gamma _
    (NumberedRewriteReduction.selfArguments (k-1) f base types extraValues (headArguments arity g))
    (canonicalList 0 (RecursiveComparison.argumentList ts)) hpoint
  have hperm : (argumentList target).Perm (argumentList (canonicalArguments 0 ts)) := by
    rw [htargetList,NumberedDerivationWeakBasicCasesProof.canonicalArgumentList]
  have hfinish := NumberedWindowTracesProof.typedToPacked (NumberedWindowTracesProof.ordinaryContext Symbol arity symbols S above Gamma g n _ target htr)
  have hraw := WindowStep.copy (Symbol:=Symbol) (arity:=arity) (symbols:=symbols) (S:=S) (above:=above) (Gamma:=Gamma) (k-1) f g base types extraValues hhead htarget.2.1
  have hk' : (k-1)+1=k := by omega
  rw [hk'] at hraw
  exact ⟨(1+n)+0,.trans (.trans (.raw _ _ hraw) hfinish)
    (.equivalent (.ordinary g g target (canonicalArguments 0 ts) htarget.2.1 htarget.2.1 rfl rfl hperm))⟩

theorem selectCase : ActualSelect := by
  intro Symbol arity symbols S above hc Gamma sigma tau f ss extraTypes extras types q r t suffix hq happly ih
  cases suffix
  obtain ⟨B,hB⟩ := ih
  refine ⟨B+types.length+1,?_⟩
  intro Q hQ hgood htarget
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
  obtain ⟨R,m,hpath,hR⟩ := NumberedWindowAngleProof.generalOriginalAngle Symbol arity symbols S above B Gamma Gamma
    (arrows types tau) q (fun v => .var v) types tau (RecursiveComparison.selfArguments f ss extraTypes extras types) rfl r happly
    A (NumberedRewriteReduction.selfArguments (k-1) f base extraTypes extraValues types) hAsub hself
  have hm := NumberedWindowTracesProof.typedToPacked hpath
  have hselectGood := NumberedUniverseOperationsProof.actualSelect Symbol arity (fun t => t∈S)
    (HeadInWindow arity symbols S) hc (k-1) Gamma f tau base extraTypes extraValues types A hAmem
    (show NumberedUniverseBindingTargets.Good (fun t => t∈S) (HeadInWindow arity symbols S)
      (.numbered ((k-1)+1) f tau base extraTypes extraValues) from hgood)
  have hRgood := NumberedWindowTracesProof.endpoint hc hm hselectGood
  obtain ⟨n,hn⟩ := hB R hR hRgood htarget
  have hraw := WindowStep.select (Symbol:=Symbol) (arity:=arity) (symbols:=symbols) (S:=S) (above:=above) (Gamma:=Gamma)
    (k-1) f base extraTypes extraValues types A hAmem
  have hk' : (k-1)+1=k := by omega
  rw [hk'] at hraw
  exact ⟨(1+m)+n,.trans (.trans (.raw _ _ hraw) hm) hn⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalCasesProof
