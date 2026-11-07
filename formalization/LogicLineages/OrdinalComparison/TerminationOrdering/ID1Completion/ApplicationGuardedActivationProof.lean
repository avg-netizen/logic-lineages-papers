module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedActivationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open ApplicationGuarded InternalAcceptance InternalAcceptanceConjunctionProof InternalControlGraphSupportProof
open GuardedSourceCertificateProof GuardedSourceSyntaxProof GammaGuardedSourceSyntaxProof
open InternalPositiveUnfoldingSupportProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Every active conjunct is built with the literal original composition AST. -/
theorem activationAt (window : Program 1) (typed : Program 3) (guard arrow : Program 2)
    (c d e arrowType f a : OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph window (suc z) ![c])))
    (ha : Nonempty (Derivation body Gamma (programGraph arrow arrowType ![d,e])))
    (hf : Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,arrowType,f])))
    (ht : Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,d,a])))
    (hg : Nonempty (Derivation body Gamma (programGraph guard (suc z) ![f,a]))) :
    Nonempty (Derivation body Gamma
      (programGraph (ApplicationDomain.activation window typed guard arrow) (suc z) ![c,d,e,f,a])) := by
  let xs := ![c,d,e,f,a]
  let wp : Program 5 := .composition window (fun _ => .projection 0)
  let ap : Program 5 := .composition arrow ![.projection 1,.projection 2]
  let fp : Program 5 := .composition typed ![.projection 0,ap,.projection 3]
  let tp : Program 5 := .composition typed ![.projection 0,.projection 1,.projection 4]
  let gp : Program 5 := .composition guard ![.projection 3,.projection 4]
  have hwp : Nonempty (Derivation body Gamma (programGraph wp (suc z) xs)) := by
    apply compositionValue window (fun _ => .projection 0) (suc z) xs ![c] hw
    intro i
    exact Fin.cases (projectionValue 0 xs) (fun q => Fin.elim0 q) i
  have hap : Nonempty (Derivation body Gamma (programGraph ap arrowType xs)) := by
    apply compositionValue arrow ![.projection 1,.projection 2] arrowType xs ![d,e] ha
    intro i
    exact Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q)) i
  have hfp : Nonempty (Derivation body Gamma (programGraph fp (suc z) xs)) := by
    apply compositionValue typed ![.projection 0,ap,.projection 3] (suc z) xs ![c,arrowType,f] hf
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases hap (Fin.cases (projectionValue 3 xs) (fun q => Fin.elim0 q))) i
  have htp : Nonempty (Derivation body Gamma (programGraph tp (suc z) xs)) := by
    apply compositionValue typed ![.projection 0,.projection 1,.projection 4] (suc z) xs ![c,d,a] ht
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 4 xs) (fun q => Fin.elim0 q))) i
  have hgp : Nonempty (Derivation body Gamma (programGraph gp (suc z) xs)) := by
    apply compositionValue guard ![.projection 3,.projection 4] (suc z) xs ![f,a] hg
    intro i
    exact Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (fun q => Fin.elim0 q)) i
  exact conjunctionAccept wp (conjunction fp (conjunction tp gp)) xs hwp
    (conjunctionAccept fp (conjunction tp gp) xs hfp (conjunctionAccept tp gp xs htp hgp))

theorem arrowNumeral (arrow : Program 2) (sigma tau : Ty)
    (ha : evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau)) :
    Nonempty (Derivation body Gamma (programGraph arrow (numeral (typeNumber (.arrow sigma tau)))
      ![numeral (typeNumber sigma),numeral (typeNumber tau)])) := by
  have hv : (fun i => (numeral ((List.Vector.ofFn ![typeNumber sigma,typeNumber tau]).get i) : OTerm α)) =
      ![numeral (typeNumber sigma),numeral (typeNumber tau)] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  obtain ⟨d⟩ := InternalNumeralEvaluationProof.actualOriginalNumeralEvaluation
    body 2 arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) α
  rw [ha,hv] at d
  exact ⟨weakenClosed d Gamma⟩

/-- Current typed and guard Programs are used directly. Only W and the fixed
arrow-type constructor are evaluated at closed numeral inputs. -/
theorem activationClosure (comp : JointGammaComputability.Data) (window : Program 1) (arrow : Program 2)
    (context : Nat) (sigma tau : Ty)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (ha : evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau))
    (f a : OTerm α) (hd : Nonempty (Derivation body Gamma (domain comp context sigma tau f a))) :
    Nonempty (Derivation body Gamma
      (programGraph (ApplicationDomain.activation window comp.typed comp.guard arrow) (suc z)
        ![numeral context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a])) := by
  rw [domain,literalTypedGraph,literalTypedGraph,literalGuardGraph] at hd
  obtain ⟨d⟩ := hd
  exact activationAt window comp.typed comp.guard arrow (numeral context)
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) (numeral (typeNumber (.arrow sigma tau))) f a
    (windowNumeral window context hw) (arrowNumeral arrow sigma tau ha)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft d)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft d)⟩
    ⟨Derivation.conjunctionRight d⟩

theorem actualOriginalActivation : ApplicationGuardedTargets.ActualOriginalActivation := by
  intro body comp window arrow context sigma tau hw ha α f a
  obtain ⟨d⟩ := activationClosure (body := body) (Gamma := [domain comp context sigma tau f a])
    comp window arrow context sigma tau hw ha f a ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedActivationProof
