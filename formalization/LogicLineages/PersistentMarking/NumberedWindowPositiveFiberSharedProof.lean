module
public import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberSharedSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberSharedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalityGraph equalityOfEqual)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowPositiveFiberPrograms NumberedWindowPositiveFiberOpenTargets
open NumberedWindowPositiveFiberSharedSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem knownAt (a : Program 1) (i : Fin 3) (n : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph a n ![xs i]))) :
    Nonempty (Derivation body Γ (programGraph (atInput a i) n xs)) := by
  apply compositionValue a (fun _ => .projection i) n xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem recoverAt (a : Program 1) (i : Fin 3) (n : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (atInput a i) n xs))) :
    Nonempty (Derivation body Γ (programGraph a n ![xs i])) := by
  apply compositionRecover a (fun _ => .projection i) n xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem tupleTwo {X : Type} (xs : Fin 2 → X) : ![xs 0,xs 1] = xs := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

private theorem extractShared (a : Program 1) (q w v : OTerm α)
    (h : Nonempty (Derivation body Γ (one (agree a) q w v))) :
    Nonempty (Derivation body Γ (shared a q v)) := by
  apply programCompositionCases equalityTest ![atInput a 0,atInput a 2]
    (suc z) ![q,w,v] (shared a q v) h
  intro β j values Δ _ hout hfields
  rw [sharedRename]
  rw [sucRelabel,zRelabel,← tupleTwo values] at hout
  have htest : Nonempty (Derivation body Δ (equalityGraph (suc z) (values 0) (values 1))) := hout
  obtain ⟨he⟩ := equalityOfAcceptance (values 0) (values 1) htest
  have hsource := hfields 0
  have htarget := hfields 1
  rw [tupleRename] at hsource htarget
  let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,v.relabel j]
  have hs := recoverAt a 0 (values 0) xs hsource
  have ht := recoverAt a 2 (values 1) xs htarget
  have target := outputTransport a (values 1) (values 0) ![v.relabel j] ⟨symm he⟩ ht
  exact sharedIntro a (q.relabel j) (v.relabel j) (values 0) hs target

private theorem acceptKnown (a : Program 1) (q w v n : OTerm α)
    (hq : Nonempty (Derivation body Γ (programGraph a n ![q])))
    (hv : Nonempty (Derivation body Γ (programGraph a n ![v]))) :
    Nonempty (Derivation body Γ (one (agree a) q w v)) := by
  apply compositionValue equalityTest ![atInput a 0,atInput a 2] (suc z) ![q,w,v] ![n,n]
    (equalityOfEqual n n ⟨refl n⟩)
  intro i
  exact Fin.cases (knownAt a 0 n ![q,w,v] hq)
    (Fin.cases (knownAt a 2 n ![q,w,v] hv) (fun k => Fin.elim0 k)) i

theorem openSharedTest : OpenSharedTest := by
  intro a body α Γ q w v
  constructor
  · exact extractShared a q w v
  · rintro ⟨h⟩
    apply Nonempty.intro
    unfold shared at h
    apply Derivation.existentialElimination h
    rw [oneRename]
    let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    let Q := programGraph a y ![q.relabel Sum.inl]
    let V := programGraph a y ![v.relabel Sum.inl]
    have hv : Derivation body ((Q ⊓ V) :: Γ.map weaken) (Q ⊓ V) :=
      Derivation.hypothesis List.mem_cons_self
    exact Classical.choice (acceptKnown a _ _ _ y ⟨Derivation.conjunctionLeft hv⟩
      ⟨Derivation.conjunctionRight hv⟩)
end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberSharedProof
