module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesProof
public import LogicLineages.OrdinalComparison.SourceMarkedBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open ComparisonFreeVariables ComparisonFreeVariablesSyntaxProof FiniteQueryPrimitivesSupportProof OriginalApplicationTrace

private theorem supportMonotone {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (a b : Allowed Γ) (h : Supported q a)
    (hab : ∀ {σ} (v : Variable Γ σ),a v → b v) : Supported q b := by
  have hr := renameSupported q a h Γ (fun v => v) b hab
  rw [Source.SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Γ τ q] at hr
  exact hr

theorem exactExecutionEquation : OriginalApplicationTraceTargets.ExactExecutionEquation := by
  intro Symbol arity Δ τ c
  rcases c with ⟨Γ,σ,types,q,env,args,suffix⟩
  cases q <;> cases args <;> rfl

theorem recursiveStepFrame : OriginalApplicationTraceTargets.RecursiveStepFrame := by
  intro Symbol arity Δ τ K P a c d hc hf he
  rcases c with ⟨Γ,σ,types,q,env,args,suffix⟩
  cases q with
  | var v => cases he
  | ordinary hd base => cases he
  | marked hd out base types extras => cases he
  | lam body =>
      cases args with
      | nil => cases he
      | cons arg rest =>
          obtain ⟨h1,h2⟩ := Ty.arrow.inj suffix
          cases h1
          cases h2
          have hd : (⟨_,_,_,body,extendEnvironment env arg,rest,rfl⟩ : Configuration Symbol arity Δ τ)=d := Option.some.inj he
          subst d
          rcases hf with ⟨hqK,henvK,hargsK,hqP,henvP,hargsP,hqA,hargsA⟩
          refine ⟨hqK.2.2,?_,hargsK.2,hqP,?_,hargsP.2,?_,hargsA.2⟩
          · intro υ v hv
            cases v with
            | here => exact hargsK.1
            | there v => exact henvK v hv
          · intro υ v
            cases v with
            | here => exact hargsP.1
            | there v => exact henvP v
          · apply supportMonotone body _ _ hqA
            intro υ v hv
            cases v with
            | here => exact hargsA.1
            | there v => exact hv

private theorem appendFrames {Symbol : Type} {arity : Symbol → Nat} {Γ xs ys : List Ty}
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Γ)
    (left : Arguments Symbol arity Γ xs) (right : Arguments Symbol arity Γ ys)
    (hl : argumentTypesAllowed K left ∧ argumentsAllowed P left ∧ ArgumentsSupported left a)
    (hr : argumentTypesAllowed K right ∧ argumentsAllowed P right ∧ ArgumentsSupported right a) :
    argumentTypesAllowed K (appendArguments left right) ∧ argumentsAllowed P (appendArguments left right) ∧
    ArgumentsSupported (appendArguments left right) a := by
  induction xs with
  | nil => cases left; exact hr
  | cons σ xs ih => cases left with
    | cons q rest =>
        obtain ⟨hk,hp,ha⟩ := ih rest ⟨hl.1.2,hl.2.1.2,hl.2.2.2⟩
        exact ⟨⟨hl.1.1,hk⟩,⟨hl.2.1.1,hp⟩,⟨hl.2.2.1,ha⟩⟩

theorem payloadBounds {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Δ) (c : Configuration Symbol arity Δ τ)
    (hc : SubtypeClosed K) (hf : OriginalApplicationTrace.Frame K P a c) : PayloadBounds K P a c := by
  rcases hf with ⟨hqK,henvK,hargsK,hqP,henvP,hargsP,hqA,hargsA⟩
  have hs := rootType c.source hqK
  obtain ⟨htypes,hτ⟩ := suffixTypes hc c.suppliedTypes τ (c.suffix ▸ hs)
  have hsubK := TypeClosureProof.substitutionTypeClosure Symbol arity K c.sourceContext Δ c.sourceType c.source c.environment hqK henvK
  have hsubP := LogicLineages.OrdinalComparison.TerminationOrdering.Proof.substitutionHeadClosure Symbol arity P c.sourceContext Δ c.sourceType c.source c.environment hqP henvP
  have hsubA := substituteSupported c.source (fun v => Supported (c.environment v) a) hqA Δ c.environment a (fun _ hv => hv)
  have happend : argumentTypesAllowed K (appendedPayload c).2 ∧ argumentsAllowed P (appendedPayload c).2 ∧ ArgumentsSupported (appendedPayload c).2 a := by
    rcases c with ⟨Γ,σ,types,q,env,args,suffix⟩
    cases q with
    | var v => exact ⟨hargsK,hargsP,hargsA⟩
    | lam body => exact ⟨hargsK,hargsP,hargsA⟩
    | ordinary hd base => exact ⟨hargsK,hargsP,hargsA⟩
    | marked hd out base extraTypes extras =>
        exact appendFrames K P a (substituteArguments extras env) args
          ⟨hsubK.2.2,hsubP.2.2,hsubA.2⟩ ⟨hargsK,hargsP,hargsA⟩
  refine ⟨hs,htypes,hτ,hsubK,hsubP,hsubA,happend.1,happend.2.1,happend.2.2,?_⟩
  intro result he
  refine ⟨?_,?_,?_⟩
  · exact TypeClosureProof.simultaneousApplicationTypeClosure Symbol arity K c.sourceContext Δ c.sourceType τ c.suppliedTypes
      c.source c.environment c.arguments c.suffix result hc hqK henvK hargsK he
  · exact LogicLineages.OrdinalComparison.TerminationOrdering.Proof.simultaneousApplicationHeadClosure Symbol arity P c.sourceContext Δ c.sourceType τ c.suppliedTypes
      c.source c.environment c.arguments c.suffix result hqP henvP hargsP he
  · exact ComparisonFreeVariablesProof.originalApplyProvenance Symbol arity c.sourceContext Δ c.sourceType τ c.suppliedTypes
      c.source c.environment c.arguments c.suffix result (fun v => Supported (c.environment v) a) a hqA (fun _ hv => hv) hargsA he

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceSupportProof
