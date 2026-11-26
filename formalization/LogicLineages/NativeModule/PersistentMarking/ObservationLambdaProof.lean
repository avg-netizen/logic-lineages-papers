module

public import LogicLineages.NativeModule.PersistentMarking.ObservationPortUpdateProof
public import LogicLineages.NativeModule.PersistentMarking.ObservationOpeningProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionObservationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ObservationLambdaProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations ObservationLambda

theorem occurrenceTrans (stack : List Ty) (t : Expr) (locals : List Ty) (q : Expr)
    (h : Occurs stack t locals q) : ∀ next r, Occurs locals q next r → Occurs stack t next r := by
  induction h using Occurs.rec
    (motive_2 := fun stack ts locals q _ => ∀ next r, Occurs locals q next r → OccursArgs stack ts next r) with
  | root => intro next r h; exact h
  | lam h ih => intro next r hr; exact .lam (ih next r hr)
  | head h ih => intro next r hr; exact .head (ih next r hr)
  | markedBase h ih => intro next r hr; exact .markedBase (ih next r hr)
  | markedExtra h ih => intro next r hr; exact .markedExtra (ih next r hr)
  | here h ih => rename_i next r hr; exact .here (ih next r hr)
  | there h ih => rename_i next r hr; exact .there (ih next r hr)

theorem descent : ObservationLambdaTargets.LambdaDescent := by
  intro S K V B Γ t υ σ τ body ht ho hw hσ hobs
  have hout := DecisionObservationProof.paper S V B Γ t υ (.arrow σ τ) (.lam σ body) ht ho hobs
  have hbudget : 1 + lambdaDepth body + used Γ ≤ B := hout.2.2
  have hspare : used Γ < Γ.length := by have hl := hw.1; omega
  obtain ⟨i,hi⟩ := ObservationPortUpdateProof.firstComplete Γ hspare
  have hnone := ObservationPortUpdateProof.firstSound Γ i hi
  have hfill := ObservationPortUpdateProof.fillExact Γ i σ hnone
  refine ⟨i,hi,ObservationPortUpdateProof.fillWellFormed K B Γ i σ hw hnone hσ,hfill.2.1,hfill.2.2.2,?_⟩
  obtain ⟨stack,q,vs,hocc,hvs,hqtype,hdepth,heq⟩ := (DecisionObservationProof.enumeration V B Γ t (.arrow σ τ) (.lam σ body)).mp hobs
  have hfree : FreeValues vs := DecisionAssignmentProof.freeValues V Γ stack vs hvs
  obtain ⟨originalBody,rfl,hbody⟩ := ObservationOpeningProof.reflection vs q σ body hfree heq.symm
  have htype : originalBody.type = τ := (Ty.arrow.inj hqtype).2
  have hchild : Occurs [] t (σ::stack) originalBody := by
    /- Occurrence transitivity must use the actual original path, including all
       list positions, not infer descendants from annotation equality. -/
    exact occurrenceTrans [] t stack (.lam σ originalBody) hocc (σ::stack) originalBody (.lam .root)
  apply (DecisionObservationProof.enumeration V B (fillSlot Γ i σ) t τ _).mpr
  refine ⟨σ::stack,originalBody,.cons (.free σ (portName V i)) vs,hchild,
    ObservationPortUpdateProof.assignmentPrepend V Γ stack vs i σ hvs hnone,htype,?_,?_⟩
  · simp only [lambdaDepth] at hdepth
    rw [hfill.2.2.2]; omega
  · rw [hbody]
    exact ObservationOpeningProof.coherence vs σ (portName V i) 0 originalBody hfree
end LogicLineages.PersistentMarking.ObservationLambdaProof
