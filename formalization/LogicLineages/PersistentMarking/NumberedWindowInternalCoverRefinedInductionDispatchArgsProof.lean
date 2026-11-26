module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchArgsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey OrdinaryOwnInputs)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets (NumberedOwnInputs)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof (ordinaryRename)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof (exact_OpenSelectedGrammarOrdinaryScratch)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof (exact_OpenSelectedGrammarNumberedScratch)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveMemberKey)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem atOrdinary (P : Programs) (s : Settings) (raw p vertices ctx result h a : OTerm α)
    (need : Obligations P s body)
    (row : PackedRow P s body Γ raw (ordinaryKey h a) p vertices ctx result 4 [h,a]) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  apply need.ordinary α Γ raw p vertices ctx result h a _ row
  intro β j Δ keep facts
  rw [graphRename]
  obtain ⟨d,width,da,wa,state,terms,args,pair,child,headHit⟩ := facts
  have parent := moveParent P.V P.R s j keep row.data.parent
  rw [ordinaryRename] at parent
  have packed := renameInto row.packed j Δ keep
  rw [eqnRelabel,ordinaryRename] at packed
  obtain ⟨packed⟩ := packed
  have input : OrdinaryOwnInputs P.V (selectedMeasure P.R) s body Δ (p.relabel j) d width
      da wa state terms args (h.relabel j) (a.relabel j) :=
    ⟨child.scope,child.hit,child.depth,child.width,headHit,parent.valid,parent.measured,pair⟩
  have hit := exact_OpenSelectedGrammarOrdinaryScratch P.V (selectedMeasure P.R) s body β Δ
    (p.relabel j) d width da wa state terms args (vertices.relabel j) (h.relabel j) (a.relabel j)
    input parent.held
  exact moveMemberKey (vertices.relabel j) (ordinaryKey (h.relabel j) (a.relabel j))
    (raw.relabel j) (symm packed) hit

theorem atNumbered (P : Programs) (s : Settings) (raw p vertices ctx result h ty k l r : OTerm α)
    (need : Obligations P s body)
    (row : PackedRow P s body Γ raw (numberedTerm h ty k l r) p vertices ctx result 5 [h,ty,k,l,r]) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  apply need.numbered α Γ raw p vertices ctx result h ty k l r _ row
  intro β j Δ keep facts
  rw [graphRename]
  obtain ⟨d,width,dl,wl,ls,lt,la,dr,wr,rs,rt,ra,pair,leftPart,rightPart,headHit,tyHit,idBound⟩ := facts
  have parent := moveParent P.V P.R s j keep row.data.parent
  rw [numberedRename] at parent
  have packed := renameInto row.packed j Δ keep
  rw [eqnRelabel,numberedRename] at packed
  obtain ⟨packed⟩ := packed
  have input : NumberedOwnInputs P.V (selectedMeasure P.R) s body Δ (p.relabel j) d width
      dl wl ls lt la dr wr rs rt ra (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) :=
    ⟨leftPart,rightPart,headHit,tyHit,idBound,parent.valid,parent.measured,pair⟩
  have hit := exact_OpenSelectedGrammarNumberedScratch P.V (selectedMeasure P.R) s body β Δ
    (p.relabel j) d width dl wl ls lt la dr wr rs rt ra (vertices.relabel j)
    (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) input parent.held
  exact moveMemberKey (vertices.relabel j)
    (numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j))
    (raw.relabel j) (symm packed) hit

#print axioms atOrdinary
#print axioms atNumbered

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchArgsProof
