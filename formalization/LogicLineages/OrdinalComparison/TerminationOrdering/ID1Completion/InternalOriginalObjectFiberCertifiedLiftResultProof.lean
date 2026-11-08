module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftResultProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly InternalOriginalObjectFiberCertifiedLift
open InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
open InternalApplicationCertificateConstructors InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalCanonicalFixedWindowVertexDispatchInvariantProof
open InternalPositiveUnfoldingSupportProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem rawInvariant (K : Nat) (p : Selection) (sigma tau : Ty) (x u : OTerm α)
    (hx : Nonempty (Derivation body Delta (rawTyped p (.arrow sigma tau) x)))
    (hu : Nonempty (Derivation body Delta (rawTyped p sigma u))) :
    Nonempty (Derivation body Delta
      (InternalCanonicalFixedWindowVertexDispatch.invariantAccepted K p.canonical sigma tau
        (numeral K) (numeral (typeNumber sigma)) (numeral (typeNumber tau)) u x)) :=
  invariantAccept K p.canonical sigma tau _ _ _ u x
    (andIntro (equalReflexive _) (andIntro (equalReflexive _)
      (andIntro (equalReflexive _) (andIntro hx hu))))

theorem applicationResult (K : Nat) (Gamma : List Ty) (p : Selection)
    (hw : evaluate p.window (List.Vector.ofFn ![K]) = 1)
    (sigma tau : Ty) (f a x u out : OTerm α)
    (hd : Nonempty (Derivation body Delta
      (InternalComputabilityDownward.domain (comp K Gamma p) K sigma tau f a)))
    (hf : Nonempty (Derivation body Delta
      (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma f x)))
    (ha : Nonempty (Derivation body Delta
      (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma a u)))
    (ho : Nonempty (Derivation body Delta
      (InternalComputabilityApplication.accepted (comp K Gamma p) sigma tau (numeral K) f a out))) :
    Nonempty (Derivation body Delta
      (InternalOriginalObjectFiberSourceDispatch.pairedApplicationGraph Gamma p.canonical
        out (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x u)) := by
  have hfT := andLeft (andLeft hd)
  have haT := andRight (andLeft hd)
  have hactive := ApplicationGuardedActivationProof.activationAt p.window
    (baseComp K Gamma p).typed (baseComp K Gamma p).guard
    InternalOriginalObjectFiberSourceDispatch.arrow (numeral K)
    (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (numeral (typeNumber (.arrow sigma tau))) f a
    (GuardedSourceCertificateProof.windowNumeral p.window K hw)
    (ApplicationGuardedActivationProof.arrowNumeral _ sigma tau
      (InternalOriginalObjectFiberSourceAssemblyClosureProof.arrowEvaluation sigma tau))
    hfT haT (andRight hd)
  have hresult := InternalApplicationGraphProof.activeRecover
    (ApplicationDomain.activation p.window (baseComp K Gamma p).typed
      (baseComp K Gamma p).guard InternalOriginalObjectFiberSourceDispatch.arrow)
    (patchedResult K Gamma p) (baseComp K Gamma p).application
    (InternalComputabilityApplication.arguments (numeral K) sigma tau f a) out hactive ho
  have hx := typedRecover K Gamma p (.arrow sigma tau) f x hf hfT
  have hu := typedRecover K Gamma p sigma a u ha haT
  have hv := invariantActivation K p.canonical sigma tau _ _ _ u x
    (rawInvariant K p sigma tau x u hx hu)
  obtain ⟨hl⟩ := InternalOriginalObjectFiberSourceDispatchGraphProof.actualInternalOriginalObjectSourceResultGraph
    K Gamma p.canonical p.oldResult body α Delta (numeral K)
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) f a x u out
  obtain ⟨hp⟩ := andIntro hf (andIntro ha hv)
  obtain ⟨hr⟩ := hresult
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination hl hp)) hr⟩

theorem actualInternalOriginalObjectFiberApplicationResult :
    InternalOriginalObjectFiberCertifiedLiftTargets.ActualInternalOriginalObjectFiberApplicationResult := by
  intro K Gamma p hw body α Delta sigma tau f a x u out
  let pre := (InternalComputabilityDownward.domain (comp K Gamma p) K sigma tau f a ⊓
    (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma f x ⊓
      InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma a u)) ⊓
    InternalComputabilityApplication.accepted (comp K Gamma p) sigma tau (numeral K) f a out
  have h : Nonempty (Derivation body (pre :: Delta) pre) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := applicationResult K Gamma p hw sigma tau f a x u out
    (andLeft (andLeft h)) (andLeft (andRight (andLeft h)))
    (andRight (andRight (andLeft h))) (andRight h)
  exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftResultProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftResultProof
