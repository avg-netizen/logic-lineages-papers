module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTermTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem termTags (H : Program 1) (M W : Program 2)
 (raw tag payload typ gamma c : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
 (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
 Nonempty (Derivation body Delta (equal tag (numeral 0) ⊔ (equal tag (numeral 1) ⊔ (equal tag (numeral 2) ⊔ (equal tag (numeral 3) ⊔ (equal tag (numeral 4) ⊔ equal tag (numeral 5))))))) := by
 let A0 := equal tag (numeral 0)
 let A1 := equal tag (numeral 1)
 let A2 := equal tag (numeral 2)
 let A3 := equal tag (numeral 3)
 let A4 := equal tag (numeral 4)
 let A5 := equal tag (numeral 5)
 let A6 := equal tag (numeral 6)
 let A7 := equal tag (numeral 7)
 apply formulaCases A0
 · exact ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
 ·
   apply formulaCases A1
   · exact ⟨orRight (orLeft (Derivation.hypothesis List.mem_cons_self))⟩
   ·
     apply formulaCases A2
     · exact ⟨orRight (orRight (orLeft (Derivation.hypothesis List.mem_cons_self)))⟩
     ·
       apply formulaCases A3
       · exact ⟨orRight (orRight (orRight (orLeft (Derivation.hypothesis List.mem_cons_self))))⟩
       ·
         apply formulaCases A4
         · exact ⟨orRight (orRight (orRight (orRight (orLeft (Derivation.hypothesis List.mem_cons_self)))))⟩
         ·
           apply formulaCases A5
           · exact ⟨orRight (orRight (orRight (orRight (orRight (Derivation.hypothesis List.mem_cons_self)))))⟩
           ·
             apply formulaCases A6
             · have hb : Nonempty (Derivation body (A6 :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) (equal tag (numeral 6) ⊔ (equal tag (numeral 7) ⊔ StepUnknownTag tag))) := ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
               obtain ⟨hf⟩ := OriginalUniverseDecoderInternalAcceptanceRejectedProof.termRejected H M W raw tag payload typ gamma c
                 (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp hp (A0.not)) (A1.not)) (A2.not)) (A3.not)) (A4.not)) (A5.not)) A6) hb (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp ha (A0.not)) (A1.not)) (A2.not)) (A3.not)) (A4.not)) (A5.not)) A6)
               exact ⟨Derivation.explosion hf⟩
             ·
               apply formulaCases A7
               · have hb : Nonempty (Derivation body (A7 :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) (equal tag (numeral 6) ⊔ (equal tag (numeral 7) ⊔ StepUnknownTag tag))) := ⟨orRight (orLeft (Derivation.hypothesis List.mem_cons_self))⟩
                 obtain ⟨hf⟩ := OriginalUniverseDecoderInternalAcceptanceRejectedProof.termRejected H M W raw tag payload typ gamma c
                   (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp hp (A0.not)) (A1.not)) (A2.not)) (A3.not)) (A4.not)) (A5.not)) (A6.not)) A7) hb (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp ha (A0.not)) (A1.not)) (A2.not)) (A3.not)) (A4.not)) (A5.not)) (A6.not)) A7)
                 exact ⟨Derivation.explosion hf⟩
               · have hu : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) (StepUnknownTag tag)) := by
                   have h0 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A0.not) := ⟨Derivation.hypothesis (by simp)⟩
                   have h1 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A1.not) := ⟨Derivation.hypothesis (by simp)⟩
                   have h2 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A2.not) := ⟨Derivation.hypothesis (by simp)⟩
                   have h3 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A3.not) := ⟨Derivation.hypothesis (by simp)⟩
                   have h4 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A4.not) := ⟨Derivation.hypothesis (by simp)⟩
                   have h5 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A5.not) := ⟨Derivation.hypothesis (by simp)⟩
                   have h6 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A6.not) := ⟨Derivation.hypothesis (by simp)⟩
                   have h7 : Nonempty (Derivation body (A7.not :: A6.not :: A5.not :: A4.not :: A3.not :: A2.not :: A1.not :: A0.not :: Delta) A7.not) := ⟨Derivation.hypothesis (by simp)⟩
                   exact andIntro h0 (andIntro h1 (andIntro h2 (andIntro h3 (andIntro h4 (andIntro h5 (andIntro h6 (h7)))))))
                 have hb := Nonempty.intro (orRight (orRight (Classical.choice hu)))
                 obtain ⟨hf⟩ := OriginalUniverseDecoderInternalAcceptanceRejectedProof.termRejected H M W raw tag payload typ gamma c
                   (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp hp (A0.not)) (A1.not)) (A2.not)) (A3.not)) (A4.not)) (A5.not)) (A6.not)) (A7.not)) hb (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp (withHyp ha (A0.not)) (A1.not)) (A2.not)) (A3.not)) (A4.not)) (A5.not)) (A6.not)) (A7.not))
                 exact ⟨Derivation.explosion hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTermTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTermTagsProof
