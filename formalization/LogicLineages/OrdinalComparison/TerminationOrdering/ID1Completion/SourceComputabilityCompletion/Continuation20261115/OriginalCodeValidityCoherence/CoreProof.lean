module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.ClauseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalOriginalOrderSyntaxProof
open OriginalContextInsertionSyntaxProof
open SideProof FrameProof InductionDefinitions InductionSyntaxProof
variable {n : Nat} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {raw : OTerm alpha}

theorem atSides (s1 s2 : Side n body Delta raw)
    (hi : Nonempty (Derivation body Delta (BelowRaw n raw)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) raw s1.table))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) raw s2.table)) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph2Rename,sucRelabel,zRelabel]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have hi' := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  rw [belowRawRename] at hi'
  have hl' := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hl'
  let f : Frame n body Theta (raw.relabel j) :=
    ⟨t1,t2,hi',tag,payload,first,second,head,hp,hf,hs,hh⟩
  have hstep := OriginalCodeDecoderTable.Proof.internalRowLookup n body beta Theta
    t1.bound t1.previous t1.table (raw.relabel j) (suc z) t1.row t1.bounded hl'
  have ha := OriginalCodeDecoderStep.ForwardProof.forward n t1.previous (raw.relabel j)
    tag payload first second head hp (OriginalCodeValidityGuard.FieldProof.firstAt _ _ _ hf)
    (OriginalCodeValidityGuard.FieldProof.secondAt _ _ _ hs) (OriginalCodeValidityGuard.FieldProof.headAt _ _ _ hh) hstep
  have hnew := ClauseProof.transportAllowed f ha
  exact OriginalCodeValidityGuard.TableSupportProof.rowLookupIntro n t2.bound t2.previous t2.table
    (raw.relabel j) (suc z) t2.row t2.bounded hnew

theorem rawStep (n : Nat) (raw fuel1 bound1 table1 fuel2 bound2 table2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw n raw)))
    (hf : Nonempty (Derivation body Delta (fields n raw fuel1 bound1 table1 fuel2 bound2 table2))) :
    Nonempty (Derivation body Delta (result n raw fuel1 bound1 table1 fuel2 bound2 table2)) := by
  have hb1 := andLeft (andLeft (andLeft hf))
  have hb2 := andRight (andLeft (andLeft hf))
  have hfu1 := andLeft (andRight (andLeft hf))
  have hfu2 := andRight (andRight (andLeft hf))
  have ht1 := andLeft (andLeft (andRight hf))
  have ht2 := andRight (andLeft (andRight hf))
  have hl := andRight (andRight hf)
  unfold result
  apply StageProof.stageCases n raw fuel1 bound1 table1 _ hfu1 ht1
  intro beta j Theta pred1 previous1 hj hfp1 hp1 hr1
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hb1' := InternalGraphCompositionFunctionalityProof.renameInto hb1 j Theta hj
  have hb2' := InternalGraphCompositionFunctionalityProof.renameInto hb2 j Theta hj
  have hfu2' := InternalGraphCompositionFunctionalityProof.renameInto hfu2 j Theta hj
  simp only [InternalLessThan.strictLess,orderRename,sucRelabel] at hb1' hb2' hfu2'
  have ht2' := InternalGraphCompositionFunctionalityProof.renameInto ht2 j Theta hj
  rw [graph2Rename] at ht2'
  have hi' := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  rw [belowRawRename] at hi'
  have hl' := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hl'
  let s1 : Side n body Theta (raw.relabel j) :=
    ⟨bound1.relabel j,pred1,previous1,table1.relabel j,hb1',hfp1,hp1,hr1⟩
  apply StageProof.stageCases n (raw.relabel j) (fuel2.relabel j) (bound2.relabel j) (table2.relabel j) _ hfu2' ht2'
  intro beta' k Xi pred2 previous2 hk hfp2 hp2 hr2
  simp only [graph2Rename,sucRelabel,zRelabel]
  let t1 := s1.rename k Xi hk
  have hb2'' := InternalGraphCompositionFunctionalityProof.renameInto hb2' k Xi hk
  simp only [orderRename,sucRelabel] at hb2''
  have hi'' := InternalGraphCompositionFunctionalityProof.renameInto hi' k Xi hk
  rw [belowRawRename] at hi''
  have hl'' := InternalGraphCompositionFunctionalityProof.renameInto hl' k Xi hk
  simp only [graph2Rename,sucRelabel,zRelabel] at hl''
  let t2 : Side n body Xi ((raw.relabel j).relabel k) :=
    ⟨(bound2.relabel j).relabel k,pred2,previous2,(table2.relabel j).relabel k,hb2'',hfp2,hp2,hr2⟩
  exact atSides t1 t2 hi'' hl''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.CoreProof
