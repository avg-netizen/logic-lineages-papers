module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.FrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.ClauseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertionSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open FrameProof
open OriginalCodeValidityGuard.FieldProof
open OriginalHeadDecoderValidity.BackwardProof (orCases)
variable {n : Nat} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {raw : OTerm alpha}
def C0 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 0) ⊔ eqn f.tag (numeral 3)
def C1 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 1) ⊓ graph2 InternalRawListRecursion.lookup (suc z) f.first f.s1.previous
def C2 (f : Frame n body Delta raw) : Formula alpha := (eqn f.tag (numeral 2) ⊔ eqn f.tag (numeral 7)) ⊓
  (graph2 InternalRawListRecursion.lookup (suc z) f.first f.s1.previous ⊓ graph2 InternalRawListRecursion.lookup (suc z) f.second f.s1.previous)
def C4 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 4) ⊓
  (graph1 (OriginalHeadDecoderValidity.check n) (suc z) f.head ⊓ graph2 InternalRawListRecursion.lookup (suc z) f.first f.s1.previous)
def C5 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 5) ⊓
  ((graph1 (OriginalHeadDecoderValidity.check n) (suc z) f.head ⊓ graph2 InternalRawListRecursion.lookup (suc z) f.first f.s1.previous) ⊓
  graph2 InternalRawListRecursion.lookup (suc z) f.second f.s1.previous)
def C6 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 6) ⊓ eqn f.payload z
def goal (f : Frame n body Delta raw) : Formula alpha := graph2 (OriginalCodeDecoderStep.step n) (suc z) f.s2.previous raw

theorem at0 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C0 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  exact OriginalCodeDecoderStep.BackwardProof.clause0 n f.s2.previous raw f.tag f.payload f.first f.second f.head f.pair
    (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph)
    ha

theorem at1 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C1 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have hc := DescentProof.unary 1 (by decide) raw f.tag f.payload f.first f.pair (andLeft ha) f.firstGraph
  exact OriginalCodeDecoderStep.BackwardProof.clause1 n f.s2.previous raw f.tag f.payload f.first f.second f.head f.pair
    (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph)
    (andIntro (andLeft ha) (transferFirst f hc (andRight ha)))

theorem at2 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C2 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have hc : Nonempty (Derivation body Delta
      (InternalLessThan.strictLess f.first raw ⊓ InternalLessThan.strictLess f.second raw)) := by
    apply orCases (andLeft ha)
    · exact DescentProof.binary 2 (by decide) raw f.tag f.payload f.first f.second
        (withHyp f.pair _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp f.firstGraph _) (withHyp f.secondGraph _)
    · exact DescentProof.binary 7 (by decide) raw f.tag f.payload f.first f.second
        (withHyp f.pair _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp f.firstGraph _) (withHyp f.secondGraph _)
  exact OriginalCodeDecoderStep.BackwardProof.clause2 n f.s2.previous raw f.tag f.payload f.first f.second f.head f.pair
    (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph)
    (andIntro (andLeft ha) (andIntro (transferFirst f (andLeft hc) (andLeft (andRight ha))) (transferSecond f (andRight hc) (andRight (andRight ha)))))

theorem at4 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C4 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have hc := DescentProof.unary 4 (by decide) raw f.tag f.payload f.first f.pair (andLeft ha) f.firstGraph
  exact OriginalCodeDecoderStep.BackwardProof.clause3 n f.s2.previous raw f.tag f.payload f.first f.second f.head f.pair
    (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph)
    (andIntro (andLeft ha) (andIntro (andLeft (andRight ha)) (transferFirst f hc (andRight (andRight ha)))))

theorem at5 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C5 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have hc := DescentProof.binary 5 (by decide) raw f.tag f.payload f.first f.second
    f.pair (andLeft ha) f.firstGraph f.secondGraph
  exact OriginalCodeDecoderStep.BackwardProof.clause4 n f.s2.previous raw f.tag f.payload f.first f.second f.head f.pair
    (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph)
    (andIntro (andLeft ha) (andIntro (andIntro (andLeft (andLeft (andRight ha))) (transferFirst f (andLeft hc) (andRight (andLeft (andRight ha))))) (transferSecond f (andRight hc) (andRight (andRight ha)))))

theorem at6 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C6 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  exact OriginalCodeDecoderStep.BackwardProof.clause5 n f.s2.previous raw f.tag f.payload f.first f.second f.head f.pair
    (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph)
    ha

def R4 (f : Frame n body Delta raw) : Formula alpha := C5 f ⊔ C6 f
def R3 (f : Frame n body Delta raw) : Formula alpha := C4 f ⊔ R4 f
def R2 (f : Frame n body Delta raw) : Formula alpha := C2 f ⊔ R3 f
def R1 (f : Frame n body Delta raw) : Formula alpha := C1 f ⊔ R2 f

theorem tail4 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R4 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at5 (f.withHyp (C5 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact at6 (f.withHyp (C6 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem tail3 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R3 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at4 (f.withHyp (C4 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail4 (f.withHyp (R4 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem tail2 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R2 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at2 (f.withHyp (C2 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail3 (f.withHyp (R3 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem tail1 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R1 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at1 (f.withHyp (C1 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail2 (f.withHyp (R2 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem transportAllowed (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta
      (OriginalCodeDecoderStep.Targets.allowed n f.s1.previous f.tag f.payload f.first f.second f.head))) :
    Nonempty (Derivation body Delta (goal f)) := by
  change Nonempty (Derivation body Delta (C0 f ⊔ R1 f)) at ha
  apply orCases ha
  · exact at0 (f.withHyp (C0 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail1 (f.withHyp (R1 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.ClauseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.ClauseProof
