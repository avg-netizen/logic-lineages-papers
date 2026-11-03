module
public import LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport Source.SourceFreeOccurrences Source.SourcePortContexts Source.SourceOpenedObservations
open RecursiveComparison ComparisonFreeVariables FiniteQueryPrimitives GuardedQueryGraph

theorem zipMembers {α β : Type} {xs : List α} {ys : List β} {a : α} {b : β}
    (h : (a,b) ∈ xs.zip ys) : a ∈ xs ∧ b ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          rcases List.mem_cons.mp h with he | ht
          · cases he; exact ⟨List.mem_cons_self,List.mem_cons_self⟩
          · obtain ⟨ha,hb⟩ := ih ht
            exact ⟨List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb⟩

def ordinaryArguments {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} :
    Packed Symbol arity Γ → List (Packed Symbol arity Γ)
  | ⟨_,.ordinary _ base⟩ => argumentList base
  | _ => []

theorem groundPacked {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (n : Nat) (f : Fin n → MarkedTerm Symbol arity Γ .ground) :
    argumentList (groundArguments n f) = List.ofFn (fun i => (⟨.ground,f i⟩ : Packed Symbol arity Γ)) := by
  induction n with
  | zero => simp [groundArguments,argumentList]
  | succ n ih => simp only [groundArguments,argumentList,List.ofFn_succ,ih]; rfl

theorem plainChildFromArgument {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (P : PortContext B) {τ : Ty} (t : Term Symbol arity (portTypes P++Γ) τ)
    (p : Packed Symbol arity (portTypes P++Γ)) (hp : p ∈ ordinaryArguments ⟨τ,embed t⟩) :
    ∃ u : Term Symbol arity (portTypes P++Γ) p.1,p.2=embed u ∧
      (⟨P,p.1,u⟩ : Observation Symbol arity Γ B) ∈ plainChildren ⟨P,τ,t⟩ := by
  cases t with
  | var v => simp [embed,ordinaryArguments] at hp
  | lam body => simp [embed,ordinaryArguments] at hp
  | zeroC => simp [embed,ordinaryArguments,argumentList] at hp
  | succC => simp [embed,ordinaryArguments,argumentList] at hp
  | caseC τ => simp [embed,ordinaryArguments,argumentList] at hp
  | recC τ => simp [embed,ordinaryArguments,argumentList] at hp
  | app f a =>
      simp only [embed,ordinaryArguments,argumentList,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨f,rfl,by simp [plainChildren]⟩
      · exact ⟨a,rfl,by simp [plainChildren]⟩
  | ranked hd args =>
      change p ∈ argumentList (groundArguments (arity hd) (fun i => embed (args i))) at hp
      rw [groundPacked] at hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨i,rfl⟩ := hp
      exact ⟨args i,rfl,by simp [plainChildren,List.mem_ofFn]⟩

theorem targetChildObservation {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) (mode : Mode)
    (P : PortContext (lambdaDepth t)) (source : Packed Symbol arity (portTypes P++Γ))
    (g : Head Symbol) (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g))
    (hf : GuardedQueryGraph.Frame s t (queryAt mode P source ⟨_,.ordinary g ts⟩))
    (p : Packed Symbol arity (portTypes P++Γ)) (hp : p ∈ argumentList ts) :
    ∃ u : Term Symbol arity (portTypes P++Γ) p.1,p.2=embed u ∧
      (⟨P,p.1,u⟩ : Observation Symbol arity Γ (lambdaDepth t)) ∈ observations (lambdaDepth t) t := by
  obtain ⟨v,he,hv⟩ := hf.2.2.2
  have hp' : p ∈ ordinaryArguments ⟨_,embed v⟩ := by rw [←he]; exact hp
  obtain ⟨u,hu,hchild⟩ := plainChildFromArgument P v p hp'
  exact ⟨u,hu,Source.SourceOpenedObservationsProof.openedPlainChildClosure Symbol arity Γ τ t (lambdaDepth t) _ _ hv hchild⟩

theorem observationType {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ)
    (P : PortContext (lambdaDepth t)) (υ : Ty) (u : Term Symbol arity (portTypes P++Γ) υ)
    (h : (⟨P,υ,u⟩ : Observation Symbol arity Γ (lambdaDepth t)) ∈ observations (lambdaDepth t) t) : υ ∈ inputTypes s t := by
  exact Finset.mem_union_right _ ((Source.SourceOpenedObservationsProof.openedTypeSupport Symbol arity Γ τ t (lambdaDepth t) _ h)
    (Source.SourceTypeSupportProof.actualResultSupport Symbol arity _ υ u))

theorem freshOpeningAvailability : GuardedQueryGraphTargets.FreshOpeningAvailability := by
  intro Symbol arity Γ σ τ s t mode P source α β body hf
  obtain ⟨v,he,hv⟩ := hf.2.2.2
  cases v with
  | lam ordinary =>
      have hb : body=embed ordinary := MarkedTerm.lam.inj he
      exact ⟨ordinary,hb,Source.SourceOpenedObservationsProof.openedLambdaClosure Symbol arity Γ τ t (lambdaDepth t) P α β ordinary hv⟩
  | var v => cases he
  | app f a => cases he
  | succC => cases he
  | caseC υ => cases he
  | recC υ => cases he

end LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphSupportProof
