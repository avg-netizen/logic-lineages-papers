module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaDefinitions
open OriginalHereditaryWorkBound
/-- Native annotation-carrying work model. It does not execute result assembly. -/
structure Job (n : Nat) where
 role : Nat
 typ : Nat
 core : State (Fin n)
def child {n : Nat} (c : Nat) (parent : Job n) (index : Nat) (s : State (Fin n)) : Job n :=
 let value := OriginalHereditaryAnnotatedExpansion.decoratedValue index parent.role parent.typ
   (NumberedLeastCodeRepresentative.codeNumber parent.core.code) (OriginalHereditaryExpansion.jobNumber c s)
 ⟨(Nat.unpair value).1,(Nat.unpair (Nat.unpair value).2).1,s⟩
def decorate {n : Nat} (c : Nat) (parent : Job n) : Nat → List (State (Fin n)) → List (Job n)
 | _, [] => []
 | index, s :: tail => child c parent index s :: decorate c parent (index+1) tail
def jobs {n : Nat} (c : Nat) (parent : Job n) := decorate c parent 0 (successors parent.core)
inductive Frame (n : Nat) where
 | visit : Job n → Frame n
 | returning : Job n → Frame n
inductive Step {n : Nat} (c : Nat) : List (Frame n) → List (Frame n) → Prop where
 | visit (a : Job n) (suffix : List (Frame n)) :
   Step c (Frame.visit a :: suffix) ((jobs c a).map Frame.visit ++ Frame.returning a :: suffix)
 | returning (a : Job n) (suffix : List (Frame n)) : Step c (Frame.returning a :: suffix) suffix
inductive Trace {n : Nat} (c : Nat) : Nat → List (Frame n) → List (Frame n) → Prop where
 | refl (agenda) : Trace c 0 agenda agenda
 | step {k a b z} : Step c a b → Trace c k b z → Trace c (k+1) a z
/-- Explicit nontruncation condition at the selected recursion depth. -/
def FrontierTerminal {n : Nat} (depth : Nat) (a : Job n) : Prop :=
 ∀ t, Path depth a.core t → successors t = []
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaDefinitions
