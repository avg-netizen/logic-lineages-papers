module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftInputProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly InternalOriginalObjectFiberCertifiedLift
open InternalOriginalObjectFiberCertifiedLiftSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalComputabilityDownwardSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Every coordinate graph is recovered from original Program totality. -/
def inputQueries : Fin 3 → Program 3 :=
  ![rightOf (.projection 0),rightOf (.projection 1),rightOf (.projection 2)]

theorem inputAtCoordinates (K : Nat) (Gamma : List Ty) (p : Selection)
    (hw : evaluate p.window (List.Vector.ofFn ![K]) = 1) (sigma tau : Ty)
    (f g a witness x y u : OTerm α)
    (hd : Nonempty (Derivation body Delta (InternalComputabilityDownward.domain (comp K Gamma p) K sigma tau f a)))
    (hp : Nonempty (Derivation body Delta (InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness)))
    (ha : Nonempty (Derivation body Delta (argumentFiber Gamma a)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y g)))
    (hu : Nonempty (Derivation body Delta (graph1 InternalUnpair.right u a))) :
    Nonempty (Derivation body Delta (inputData Gamma p sigma tau f g a witness x y u)) := by
  have hf := InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof.functionFiber
    K Gamma p f a (andRight hd) ha
  have hg := InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof.targetFiber
    K Gamma p f g witness hp hf
  have hcf := andIntro hf hx
  have hcg := andIntro hg hy
  have hca := andIntro ha hu
  have htf := andLeft (andLeft hd)
  have hta := andRight (andLeft hd)
  have htg := certificateTyped K Gamma p hw (.arrow sigma tau) f g witness htf hp
  have hrx := InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof.typedRecover
    K Gamma p (.arrow sigma tau) f x hcf htf
  have hry := InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof.typedRecover
    K Gamma p (.arrow sigma tau) g y hcg htg
  have hru := InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof.typedRecover
    K Gamma p sigma a u hca hta
  have hrp := InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof.positiveRecover
    K Gamma p f g x y witness hcf hcg hp
  exact andIntro hcf (andIntro hcg (andIntro hca (andIntro hrx (andIntro hry (andIntro hru hrp)))))

theorem inputExtract (K : Nat) (Gamma : List Ty) (p : Selection)
    (hw : evaluate p.window (List.Vector.ofFn ![K]) = 1) (sigma tau : Ty)
    (f g a witness : OTerm α)
    (hd : Nonempty (Derivation body Delta (InternalComputabilityDownward.domain (comp K Gamma p) K sigma tau f a)))
    (hp : Nonempty (Derivation body Delta (InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness)))
    (ha : Nonempty (Derivation body Delta (argumentFiber Gamma a))) :
    Nonempty (Derivation body Delta (inputDataExists Gamma p sigma tau f g a witness)) := by
  apply queryCases inputQueries (Fin.cons f (Fin.cons g (Fin.cons a Fin.elim0))) _
  intro β j ys Theta hj hq
  rw [inputDataExistsRename]
  have hd' := renameInto hd j Theta hj
  have hp' := renameInto hp j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [domainRename] at hd'
  rw [certificateRename] at hp'
  rw [argumentFiberRename] at ha'
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 3 → OTerm β := Fin.cons (f.relabel j) (Fin.cons (g.relabel j) (Fin.cons (a.relabel j) Fin.elim0))
  have hx := InternalOriginalTypedCarrierSupportProof.atRecover InternalUnpair.right 0 (ys 0) xs (hq 0)
  have hy := InternalOriginalTypedCarrierSupportProof.atRecover InternalUnpair.right 1 (ys 1) xs (hq 1)
  have hu := InternalOriginalTypedCarrierSupportProof.atRecover InternalUnpair.right 2 (ys 2) xs (hq 2)
  exact inputIntro Gamma p sigma tau (f.relabel j) (g.relabel j) (a.relabel j)
    (witness.relabel j) (ys 0) (ys 1) (ys 2)
    (inputAtCoordinates K Gamma p hw sigma tau (f.relabel j) (g.relabel j) (a.relabel j)
      (witness.relabel j) (ys 0) (ys 1) (ys 2) hd' hp' ha' hx hy hu)

theorem actualInternalOriginalObjectFiberInputExtraction :
    InternalOriginalObjectFiberCertifiedLiftTargets.ActualInternalOriginalObjectFiberInputExtraction := by
  intro K Gamma p hw body α Delta sigma tau f g a witness
  let P := (InternalComputabilityDownward.domain (comp K Gamma p) K sigma tau f a ⊓
    InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness) ⊓ argumentFiber Gamma a
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := inputExtract K Gamma p hw sigma tau f g a witness
    (andLeft (andLeft hp)) (andRight (andLeft hp)) (andRight hp)
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftInputProof
