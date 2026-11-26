module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.TupleFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawMembershipProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atQueries (a b c d e f k h t base ts extra out code : OTerm alpha)
    (ys zs : Fin 5 → OTerm alpha)
    (hy : ∀ i, Nonempty (Derivation body Delta (programGraph (ProductFrameProof.queries i) (ys i) ![a,b,c,d,e,f])))
    (hz : ∀ i, Nonempty (Derivation body Delta (programGraph (TupleFrameProof.queries i) (zs i) ![k,h,t,base,ts,extra])))
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![a,b,c,d,e,f])))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,h,t,base,ts,extra]))) :
    (Nonempty (Derivation body Delta (RawValuesProof.fields a b c d e f k h t base ts extra)) ↔
     Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) := by
  have hg := ProductFrameProof.recover a b c d e f ys hy
  have hp := TupleFrameProof.recover k h t base ts extra zs hz
  have hmap := ProductFrameProof.rawBranchRecover a b c d e f out (ys 4) (hy 4) hv
  have hcode := TupleProof.constructorRecover k h t base ts extra (zs 4) code (hz 4) hc
  have hg0 := (andLeft (andLeft (andLeft (andLeft hg))))
  have hg1 := (andRight (andLeft (andLeft (andLeft hg))))
  have hg2 := (andRight (andLeft (andLeft hg)))
  have hg3 := (andRight (andLeft hg))
  have hg4 := (andRight hg)
  have hp0 := (andLeft (andLeft (andLeft (andLeft hp))))
  have hp1 := (andRight (andLeft (andLeft (andLeft hp))))
  have hp2 := (andRight (andLeft (andLeft hp)))
  have hp3 := (andRight (andLeft hp))
  have hp4 := (andRight hp)
  constructor
  · intro hm
    exact RawValuesProof.forward a b c d e f (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) k h t base ts extra (zs 0) (zs 1) (zs 2) (zs 3) (zs 4) out code hg0 hp0 hg1 hp1 hg2 hp2 hg3 hp3 hg4 hp4 hmap hcode hm
  · intro hm
    exact RawValuesProof.backward a b c d e f (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) k h t base ts extra (zs 0) (zs 1) (zs 2) (zs 3) (zs 4) out code hg0 hp0 hg1 hp1 hg2 hp2 hg3 hp3 hg4 hp4 hmap hcode hm

theorem forward (a b c d e f k h t base ts extra out code : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![a,b,c,d,e,f])))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,h,t,base,ts,extra])))
    (hm : Nonempty (Derivation body Delta (RawValuesProof.fields a b c d e f k h t base ts extra))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases ProductFrameProof.queries ![a,b,c,d,e,f] _
  intro beta j ys Theta hj hy
  have hx : (fun i => (![a,b,c,d,e,f] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hy
  simp only [RawValuesProof.fields,conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [InternalControlGraphSupportProof.programRename] at hvj
  have hxhv : (fun i => (![a,b,c,d,e,f] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxhv] at hvj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [InternalControlGraphSupportProof.programRename] at hcj
  have hxhc : (fun i => (![k,h,t,base,ts,extra] i).relabel j) = ![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxhc] at hcj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [RawValuesProof.fields,conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases TupleFrameProof.queries ![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] _
  intro gamma l zs Xi hl hz
  have hzxs : (fun i => (![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] i).relabel l) = ![(k.relabel j).relabel l,(h.relabel j).relabel l,(t.relabel j).relabel l,(base.relabel j).relabel l,(ts.relabel j).relabel l,(extra.relabel j).relabel l] := by
    funext i
    fin_cases i <;> rfl
  rw [hzxs] at hz
  simp only [conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvl := InternalGraphCompositionFunctionalityProof.renameInto hvj l Xi hl
  simp only [InternalControlGraphSupportProof.programRename] at hvl
  have hxxhv : (fun i => (![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] i).relabel l) = ![(a.relabel j).relabel l,(b.relabel j).relabel l,(c.relabel j).relabel l,(d.relabel j).relabel l,(e.relabel j).relabel l,(f.relabel j).relabel l] := by
    funext i
    fin_cases i <;> rfl
  rw [hxxhv] at hvl
  have hcl := InternalGraphCompositionFunctionalityProof.renameInto hcj l Xi hl
  simp only [InternalControlGraphSupportProof.programRename] at hcl
  have hxxhc : (fun i => (![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] i).relabel l) = ![(k.relabel j).relabel l,(h.relabel j).relabel l,(t.relabel j).relabel l,(base.relabel j).relabel l,(ts.relabel j).relabel l,(extra.relabel j).relabel l] := by
    funext i
    fin_cases i <;> rfl
  rw [hxxhc] at hcl
  have hml := InternalGraphCompositionFunctionalityProof.renameInto hmj l Xi hl
  simp only [conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hml
  have hyl : ∀ i, Nonempty (Derivation body Xi (programGraph (ProductFrameProof.queries i) ((ys i).relabel l)
    ![(a.relabel j).relabel l,(b.relabel j).relabel l,(c.relabel j).relabel l,(d.relabel j).relabel l,(e.relabel j).relabel l,(f.relabel j).relabel l])) := by
    intro i
    have hq := InternalGraphCompositionFunctionalityProof.renameInto (hy i) l Xi hl
    simp only [InternalControlGraphSupportProof.programRename] at hq
    have hh : (fun i => (![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] i).relabel l) = ![(a.relabel j).relabel l,(b.relabel j).relabel l,(c.relabel j).relabel l,(d.relabel j).relabel l,(e.relabel j).relabel l,(f.relabel j).relabel l] := by
      funext i
      fin_cases i <;> rfl
    rw [hh] at hq
    exact hq
  exact (atQueries ((a.relabel j).relabel l) ((b.relabel j).relabel l) ((c.relabel j).relabel l) ((d.relabel j).relabel l) ((e.relabel j).relabel l) ((f.relabel j).relabel l) ((k.relabel j).relabel l) ((h.relabel j).relabel l) ((t.relabel j).relabel l) ((base.relabel j).relabel l) ((ts.relabel j).relabel l) ((extra.relabel j).relabel l) ((out.relabel j).relabel l) ((code.relabel j).relabel l) (fun i => (ys i).relabel l) zs hyl hz hvl hcl).mp hml

theorem backward (a b c d e f k h t base ts extra out code : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![a,b,c,d,e,f])))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,h,t,base,ts,extra])))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (RawValuesProof.fields a b c d e f k h t base ts extra)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases ProductFrameProof.queries ![a,b,c,d,e,f] _
  intro beta j ys Theta hj hy
  have hx : (fun i => (![a,b,c,d,e,f] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hy
  simp only [RawValuesProof.fields,conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [InternalControlGraphSupportProof.programRename] at hvj
  have hxhv : (fun i => (![a,b,c,d,e,f] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxhv] at hvj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [InternalControlGraphSupportProof.programRename] at hcj
  have hxhc : (fun i => (![k,h,t,base,ts,extra] i).relabel j) = ![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxhc] at hcj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [RawValuesProof.fields,conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases TupleFrameProof.queries ![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] _
  intro gamma l zs Xi hl hz
  have hzxs : (fun i => (![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] i).relabel l) = ![(k.relabel j).relabel l,(h.relabel j).relabel l,(t.relabel j).relabel l,(base.relabel j).relabel l,(ts.relabel j).relabel l,(extra.relabel j).relabel l] := by
    funext i
    fin_cases i <;> rfl
  rw [hzxs] at hz
  simp only [conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvl := InternalGraphCompositionFunctionalityProof.renameInto hvj l Xi hl
  simp only [InternalControlGraphSupportProof.programRename] at hvl
  have hxxhv : (fun i => (![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] i).relabel l) = ![(a.relabel j).relabel l,(b.relabel j).relabel l,(c.relabel j).relabel l,(d.relabel j).relabel l,(e.relabel j).relabel l,(f.relabel j).relabel l] := by
    funext i
    fin_cases i <;> rfl
  rw [hxxhv] at hvl
  have hcl := InternalGraphCompositionFunctionalityProof.renameInto hcj l Xi hl
  simp only [InternalControlGraphSupportProof.programRename] at hcl
  have hxxhc : (fun i => (![k.relabel j,h.relabel j,t.relabel j,base.relabel j,ts.relabel j,extra.relabel j] i).relabel l) = ![(k.relabel j).relabel l,(h.relabel j).relabel l,(t.relabel j).relabel l,(base.relabel j).relabel l,(ts.relabel j).relabel l,(extra.relabel j).relabel l] := by
    funext i
    fin_cases i <;> rfl
  rw [hxxhc] at hcl
  have hml := InternalGraphCompositionFunctionalityProof.renameInto hmj l Xi hl
  simp only [conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hml
  have hyl : ∀ i, Nonempty (Derivation body Xi (programGraph (ProductFrameProof.queries i) ((ys i).relabel l)
    ![(a.relabel j).relabel l,(b.relabel j).relabel l,(c.relabel j).relabel l,(d.relabel j).relabel l,(e.relabel j).relabel l,(f.relabel j).relabel l])) := by
    intro i
    have hq := InternalGraphCompositionFunctionalityProof.renameInto (hy i) l Xi hl
    simp only [InternalControlGraphSupportProof.programRename] at hq
    have hh : (fun i => (![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] i).relabel l) = ![(a.relabel j).relabel l,(b.relabel j).relabel l,(c.relabel j).relabel l,(d.relabel j).relabel l,(e.relabel j).relabel l,(f.relabel j).relabel l] := by
      funext i
      fin_cases i <;> rfl
    rw [hh] at hq
    exact hq
  exact (atQueries ((a.relabel j).relabel l) ((b.relabel j).relabel l) ((c.relabel j).relabel l) ((d.relabel j).relabel l) ((e.relabel j).relabel l) ((f.relabel j).relabel l) ((k.relabel j).relabel l) ((h.relabel j).relabel l) ((t.relabel j).relabel l) ((base.relabel j).relabel l) ((ts.relabel j).relabel l) ((extra.relabel j).relabel l) ((out.relabel j).relabel l) ((code.relabel j).relabel l) (fun i => (ys i).relabel l) zs hyl hz hvl hcl).mpr hml
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawMembershipProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawMembershipProof
