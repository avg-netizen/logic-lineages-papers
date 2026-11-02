module
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeTargets
public import LogicLineages.OrdinalComparison.SourceTypedPortsProof
public import LogicLineages.OrdinalComparison.TrackedSourceProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode.Proof
open SourceFreeOccurrences

private theorem mod_tag (a tag : Nat) (h : tag < 8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag < 8) : (8*a+tag)/8=a := by omega

private theorem occurs_var (i j : Nat) : occursCode i (8*j) = decide (j=i) := by
  rw [occursCode.eq_def]
  simp
private theorem occurs_app (i a b : Nat) :
    occursCode i (8*Nat.pair a b+5) = (occursCode i a || occursCode i b) := by
  rw [occursCode.eq_def]
  simp [mod_tag _ 5 (by decide),div_tag _ 5 (by decide)]
private theorem occurs_lam (i σ b : Nat) :
    occursCode i (8*Nat.pair σ b+6) = occursCode (i+1) b := by
  rw [occursCode.eq_def]
  simp [mod_tag _ 6 (by decide),div_tag _ 6 (by decide)]

 theorem exactFreeOccurrence : Targets.ExactFreeOccurrence := by
  intro Γ σ τ F t
  induction t generalizing σ with
  | var v =>
    change occursCode (SourceTypedPorts.variableIndex F) (8*SourceTypedPorts.variableIndex v) = true ↔ _
    rw [occurs_var]
    simp only [decide_eq_true_eq,freeOccurrences,List.mem_singleton]
    constructor
    · intro h
      exact (SourceTypedPortsProof.typedVariableIndex.2 _ ⟨_,v⟩ ⟨_,F⟩ h).symm
    · intro h
      exact (congrArg (fun x : PackedVariable _ => SourceTypedPorts.variableIndex x.2) h).symm
  | zeroC =>
    rw [occursCode.eq_def]
    simp [SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,freeOccurrences]
  | succC =>
    rw [occursCode.eq_def]
    simp [SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,freeOccurrences]
  | caseC τ =>
    rw [occursCode.eq_def]
    simp [SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,freeOccurrences,mod_tag _ 3 (by decide)]
  | recC τ =>
    rw [occursCode.eq_def]
    simp [SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,freeOccurrences,mod_tag _ 4 (by decide)]
  | app f a ihf iha =>
    change occursCode (SourceTypedPorts.variableIndex F)
      (8*Nat.pair (SyntaxCode.encodeTerm f) (SyntaxCode.encodeTerm a)+5) = true ↔ _
    rw [occurs_app]
    simp only [Bool.or_eq_true,freeOccurrences,List.mem_append,ihf,iha]
  | lam body ih =>
    change occursCode (SourceTypedPorts.variableIndex F)
      (8*Nat.pair _ (SyntaxCode.encodeTerm body)+6) = true ↔ _
    rw [occurs_lam]
    simpa only [SourceTypedPorts.variableIndex,freeOccurrences,TrackedSource.Proof.mem_dropBound]
      using (ih σ (.there F))
  | ranked s _ _ => cases s

private theorem arity_ground : arityCode (SyntaxCode.typeCode .ground) = some 0 := by
  rw [arityCode.eq_def]
  simp [SyntaxCode.typeCode]
private theorem arity_arrow (a b : Ty) :
    arityCode (SyntaxCode.typeCode (.arrow a b)) =
      if SyntaxCode.typeCode a=0 then (arityCode (SyntaxCode.typeCode b)).map Nat.succ else none := by
  rw [arityCode.eq_def]
  simp [SyntaxCode.typeCode,SyntaxCode.arrowCode]
private theorem type_zero (a : Ty) : SyntaxCode.typeCode a=0 ↔ a=.ground := by
  cases a <;> simp [SyntaxCode.typeCode,SyntaxCode.arrowCode]

theorem exactArity : Targets.ExactArity := by
  intro τ
  induction τ with
  | ground =>
    intro n
    rw [arity_ground]
    cases n <;> simp [Ty.curriedGround]
  | arrow a b iha ihb =>
    intro n
    rw [arity_arrow]
    by_cases ha : a=.ground
    · subst a
      simp only [SyntaxCode.typeCode,↓reduceIte]
      cases n with
      | zero => simp [Ty.curriedGround]
      | succ n =>
        rw [show (arityCode (SyntaxCode.typeCode b)).map Nat.succ = some (n+1) ↔
            arityCode (SyntaxCode.typeCode b)=some n by
              cases arityCode (SyntaxCode.typeCode b) <;> simp]
        simpa only [Ty.curriedGround,Ty.arrow.injEq,true_and] using ihb n
    · rw [if_neg (fun h => ha ((type_zero a).mp h))]
      cases n <;> simp [Ty.curriedGround,ha]

theorem actualGrammarInspection : Targets.ActualGrammarInspection := by
  intro k Γ F n e
  refine ⟨?_,?_,(exactArity _ n).mpr rfl⟩
  · apply Bool.eq_iff_iff.mpr
    exact (exactFreeOccurrence Γ _ _ F (TrackedSource.erase e)).trans
      (TrackedSource.Proof.exactActivity k Γ F n e).symm
  · exact (SyntaxCode.Proof.typedCheckExact Γ _ _).mpr ⟨TrackedSource.erase e,rfl⟩
end LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode.Proof
