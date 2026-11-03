module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecSupportProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration
open NumberedCodeAssemblyPrimrecProof NumberedEnumerationOperationsPrimrecProof

/-- The ordinary ordered list product, with every repeated occurrence retained. -/
def cross {A B : Type} (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap (fun a => ys.map (fun b => (a, b)))

theorem crossPrimitive {A B : Type} [Primcodable A] [Primcodable B] :
    Primrec₂ (@cross A B) :=
  Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂

theorem mapPrimitive {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {f : A → B} {values : C → List A} (hf : Primrec f) (hvalues : Primrec values) :
    Primrec (fun c => (values c).map f) :=
  Primrec.list_map hvalues (hf.comp Primrec.snd).to₂

abbrev Parameters (n : Nat) := List Ty × List (HeadCode (Fin n)) × Nat × Nat
abbrev LayerInput (n : Nat) := Parameters n × Nat × List (Code (Fin n)) × List (Code (Fin n))

/-- The original constructor layer with its ordered nested products exposed. -/
def layer (n : Nat) (p : LayerInput n) : List (Code (Fin n)) :=
  (List.range p.2.1).map Code.var ++
  (cross p.1.1 p.2.2.2).map (fun q => Code.lam q.1 q.2) ++
  (cross p.1.1 (cross p.2.2.1 p.2.2.1)).map (fun q => Code.app q.1 q.2.1 q.2.2) ++
  p.1.1.map Code.bottom ++
  (cross p.1.2.1 p.2.2.1).map (fun q => Code.ordinary q.1 q.2) ++
  (cross (List.range (p.1.2.2.1 + 1))
    (cross p.1.2.1 (cross p.1.1 (cross p.2.2.1
      (cross (typeLists p.1.1 p.1.2.2.2) p.2.2.1))))).map
        (fun q => Code.numbered q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) ++
  [Code.argumentsNil] ++
  (cross p.1.1 (cross p.2.2.1 p.2.2.1)).map (fun q => Code.argumentsCons q.1 q.2.1 q.2.2)

theorem layerPrimitive (n : Nat) : Primrec (layer n) := by
  have hs : Primrec (fun p : LayerInput n => p.1.1) := Primrec.fst.comp Primrec.fst
  have hh : Primrec (fun p : LayerInput n => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hl : Primrec (fun p : LayerInput n => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have ht : Primrec (fun p : LayerInput n => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hv : Primrec (fun p : LayerInput n => p.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : LayerInput n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ho : Primrec (fun p : LayerInput n => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hvar : Primrec (fun p : LayerInput n => (List.range p.2.1).map (Code.var : Nat → Code (Fin n))) :=
    mapPrimitive (varPrimitive n) (Primrec.list_range.comp hv)
  have hlam : Primrec (fun p : LayerInput n =>
      (cross p.1.1 p.2.2.2).map (fun q => Code.lam q.1 q.2)) :=
    mapPrimitive (lamPrimitive n) (crossPrimitive.comp hs ho)
  have hpairs : Primrec (fun p : LayerInput n => cross p.1.1 (cross p.2.2.1 p.2.2.1)) :=
    crossPrimitive.comp hs (crossPrimitive.comp hp hp)
  have happ : Primrec (fun p : LayerInput n =>
      (cross p.1.1 (cross p.2.2.1 p.2.2.1)).map (fun q => Code.app q.1 q.2.1 q.2.2)) :=
    mapPrimitive (appPrimitive n) hpairs
  have hbottom : Primrec (fun p : LayerInput n => p.1.1.map (Code.bottom : Ty → Code (Fin n))) :=
    mapPrimitive (bottomPrimitive n) hs
  have hord : Primrec (fun p : LayerInput n =>
      (cross p.1.2.1 p.2.2.1).map (fun q => Code.ordinary q.1 q.2)) :=
    mapPrimitive (ordinaryPrimitive n) (crossPrimitive.comp hh hp)
  have htypes : Primrec (fun p : LayerInput n => typeLists p.1.1 p.1.2.2.2) :=
    typeListsPrimitive.comp (hs.pair ht)
  have hnum : Primrec (fun p : LayerInput n =>
      (cross (List.range (p.1.2.2.1 + 1))
        (cross p.1.2.1 (cross p.1.1 (cross p.2.2.1
          (cross (typeLists p.1.1 p.1.2.2.2) p.2.2.1))))).map
            (fun q => Code.numbered q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)) :=
    mapPrimitive (numberedPrimitive n)
      (crossPrimitive.comp (Primrec.list_range.comp (Primrec.succ.comp hl))
        (crossPrimitive.comp hh (crossPrimitive.comp hs (crossPrimitive.comp hp
          (crossPrimitive.comp htypes hp)))))
  have hcons : Primrec (fun p : LayerInput n =>
      (cross p.1.1 (cross p.2.2.1 p.2.2.1)).map (fun q => Code.argumentsCons q.1 q.2.1 q.2.2)) :=
    mapPrimitive (argumentsConsPrimitive n) hpairs
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.list_append.comp
            (Primrec.list_append.comp (Primrec.list_append.comp hvar hlam) happ) hbottom) hord) hnum)
      (Primrec.const [Code.argumentsNil])) hcons

theorem layerCalibration (n : Nat) (data : Parameters n) (variableBound fuel : Nat) :
    layer n (data, variableBound,
      enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 variableBound fuel,
      enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 (variableBound + 1) fuel) =
    enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 variableBound (fuel + 1) := by
  simp [layer, cross, enumerate, List.map_flatMap, List.map_map, Function.comp_def]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecSupportProof
