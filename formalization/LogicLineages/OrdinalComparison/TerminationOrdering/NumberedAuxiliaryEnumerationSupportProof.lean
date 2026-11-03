module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedFiniteUniverse NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration

theorem typeListEnumeration : NumberedAuxiliaryEnumerationTargets.ActualTypeListEnumeration := by
  intro S bound
  induction bound with
  | zero => intro types; cases types <;> simp [typeLists]
  | succ bound ih =>
    intro types
    cases types with
    | nil => simp [typeLists]
    | cons tau types =>
      simp [typeLists,ih,List.length_cons,Nat.succ_le_succ_iff,and_assoc,and_left_comm,and_comm]

theorem depthPositive {Symbol : Type} (c : Code Symbol) : 0<depth c := by
  cases c <;> simp only [depth] <;> omega

theorem codeEnumeration : NumberedAuxiliaryEnumerationTargets.ActualCodeEnumeration := by
  intro Symbol S H labels tupleBound variableBound fuel
  induction fuel generalizing variableBound with
  | zero =>
    intro c
    have hp := depthPositive c
    simp only [enumerate,List.not_mem_nil,false_iff,not_and]
    intro _
    omega
  | succ fuel ih =>
    intro c
    have hsucc (a : Nat) : 1+a≤fuel+1 ↔ a≤fuel := by omega
    have htypes := typeListEnumeration S tupleBound
    cases c <;>
      simp [enumerate,Fields,depth,htypes,ih,hsucc,Nat.max_le,
        Nat.lt_succ_iff,and_assoc,and_left_comm,and_comm]

theorem sizePositive {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : 0<size q := by
  cases q <;> simp only [size] <;> omega

theorem argumentsLength {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : types.length≤argumentsSize args := by
  induction types with
  | nil => cases args; exact Nat.le_refl _
  | cons sigma types ih => cases args with
    | cons q rest =>
      have hp := sizePositive q
      have hr := ih rest
      simp only [List.length_cons,argumentsSize]
      omega

theorem sourceDepthBound : NumberedAuxiliaryEnumerationTargets.ActualSourceDepthBound := by
  intro Symbol arity Gamma tau q
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => depth (argumentsCode args)≤2*argumentsSize args+1)
  case var => simp [termCode,depth,size]
  case lam body ih => simp only [termCode,depth,size]; omega
  case app q a ihq iha => simp only [termCode,depth,size]; omega
  case bottom => simp [termCode,depth,size]
  case ordinary f base ih => simp only [termCode,depth,size]; omega
  case numbered k f tau base types extras ihb ihe => simp only [termCode,depth,size]; omega
  case nil => simp [argumentsCode,depth,argumentsSize]
  case cons Gamma sigma types q rest ihq ihr =>
    have hp := sizePositive q
    simp only [argumentsCode,depth,argumentsSize]
    omega

theorem argumentTypes {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (K : Ty → Prop) (H : Head Symbol → Prop) (args : AuxArguments Symbol arity Gamma types)
    (h : NumberedUniverseBindingTargets.GoodArguments K H args) : ∀ tau∈types,K tau := by
  induction types with
  | nil => intro tau ht; cases ht
  | cons sigma types ih => cases args with
    | cons q rest =>
      intro tau ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact NumberedUniverseOperationsProof.rootType K H q ⟨h.1.1,h.2.1⟩
      · exact ih rest ⟨h.1.2,h.2.2⟩ tau ht

theorem headMembership {Symbol : Type} [DecidableEq Symbol] (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun t => t∈S)) (f : Head Symbol)
    (h : HeadInWindow arity symbols S f) : headCode f∈sourceHeads arity symbols S := by
  exact List.mem_map.mpr ⟨f,(NumberedFiniteUniverseProof.headWindow Symbol inferInstance arity symbols S hc f).mpr h,rfl⟩

theorem sourceFields {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun t => t∈S)) (L : Nat)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ N,size q≤N → InUniverse symbols S q → LabelsAtMost L q →
      Fields S (sourceHeads arity symbols S) L N Gamma.length (termCode q) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ N,argumentsSize args≤N →
      NumberedUniverseBindingTargets.GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) args →
      ArgumentLabelsAtMost L args → Fields S (sourceHeads arity symbols S) L N Gamma.length (argumentsCode args))
  case var v =>
    intro N hn hg hl
    exact SourceTypedPortsProof.typedVariableIndex.1 _ _ v
  case lam body ih =>
    intro N hn hg hl
    exact ⟨hg.1.2.1,ih N (by simp only [size] at hn; omega) ⟨hg.1.2.2,hg.2⟩ hl⟩
  case app q a ihq iha =>
    intro N hn hg hl
    have hq := NumberedUniverseOperationsProof.rootType (fun t => t∈S) (HeadInWindow arity symbols S) q ⟨hg.1.2.1,hg.2.1⟩
    have hs := NumberedUniverseOperationsProof.arrowDomain (fun t => t∈S) hc _ _ hq
    exact ⟨hs,ihq N (by simp only [size] at hn; omega) ⟨hg.1.2.1,hg.2.1⟩ hl.1,
      iha N (by simp only [size] at hn; omega) ⟨hg.1.2.2,hg.2.2⟩ hl.2⟩
  case bottom tau => intro N hn hg hl; exact hg.1
  case ordinary f base ih =>
    intro N hn hg hl
    exact ⟨headMembership arity symbols S hc f hg.2.1,ih N (by simp only [size] at hn; omega) ⟨hg.1.2,hg.2.2⟩ hl⟩
  case numbered k f tau base types extras ihb ihe =>
    intro N hn hg hl
    have hb : NumberedUniverseBindingTargets.GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) base := ⟨hg.1.2.1,hg.2.2.1⟩
    have he : NumberedUniverseBindingTargets.GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) extras := ⟨hg.1.2.2,hg.2.2.2⟩
    have hel := argumentsLength extras
    refine ⟨hl.1,headMembership arity symbols S hc f hg.2.1,hg.1.1,
      ihb N (by simp only [size] at hn; omega) hb hl.2.1,?_,argumentTypes _ _ extras he,
      ihe N (by simp only [size] at hn; omega) he hl.2.2⟩
    simp only [size] at hn
    omega
  case nil => trivial
  case cons Gamma sigma types q rest ihq ihr N hn hg hl =>
    have hroot := NumberedUniverseOperationsProof.rootType (fun t => t∈S) (HeadInWindow arity symbols S) q ⟨hg.1.1,hg.2.1⟩
    exact ⟨hroot,ihq N (by simp only [argumentsSize] at hn; omega) ⟨hg.1.1,hg.2.1⟩ hl.1,
      ihr N (by simp only [argumentsSize] at hn; omega) ⟨hg.1.2,hg.2.2⟩ hl.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationSupportProof
