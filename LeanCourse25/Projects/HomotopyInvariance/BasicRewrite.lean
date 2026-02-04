import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits Opposite
universe u v w

section General

variable {C D : Type*} [Category C] [Category D]

/-- The functor of points (generalized elements) represented by an object `T`.
For `T = ⊤_ C`, this is the global sections functor. -/
abbrev pointsFunctor (T : C) : C ⥤ Type _ := coyoneda.obj (op T)

/-- A functor `F` induces a map from `T`-points of `X` to `F(T)`-points of `F(X)`. -/
def pointsFunctorMap (F : C ⥤ D) (T : C) :
    pointsFunctor T ⟶ F ⋙ pointsFunctor (F.obj T) where
  app X f := F.map f
  naturality X Y f := by
    ext p
    dsimp [pointsFunctor]
    rw [← F.map_comp]

/-- If `D` is a concrete category, any element `pt : F(P)` induces a natural transformation
from `Hom(P, -)` (which is `pointsFunctor P`) to `F`. -/
def evaluationFromPoint {D : Type*} [Category D] {F : D ⥤ Type _} {P : D} (pt : F.obj P) :
    pointsFunctor P ⟶ F :=
  CategoryTheory.coyonedaEquiv.symm pt

/-- Given an initial object `I` in `C` and a functor `F : C ⥤ D`, we get a natural
transformation from the constant functor at `F(I)` to `F` itself. -/
def natTransFromInitial {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (I : C) (hI : IsInitial I) :
    (Functor.const C).obj (F.obj I) ⟶ F where
  app X := F.map (hI.to X)
  naturality X Y f := by
    dsimp
    simp only [Category.id_comp]
    rw [← F.map_comp, hI.hom_ext (hI.to X ≫ f) (hI.to Y)]

/-- The component of `natTransFromInitial` at the initial object is the identity. -/
@[simp]
lemma natTransFromInitial_app_self {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (I : C) (hI : IsInitial I) :
    (natTransFromInitial F I hI).app I = F.map (𝟙 I) := by
  simp only [natTransFromInitial]
  congr 1
  exact hI.hom_ext (hI.to I) (𝟙 I)

/-- The component of `natTransFromInitial` at the initial object is the identity
(in terms of the target category). -/
lemma natTransFromInitial_app_self' {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (I : C) (hI : IsInitial I) :
    (natTransFromInitial F I hI).app I = 𝟙 (F.obj I) := by
  rw [natTransFromInitial_app_self, F.map_id]

/-- **Uniqueness**: Any natural transformation from the constant functor at `F(I)` to `F`
(where `I` is initial) that acts as identity at `I` equals `natTransFromInitial`. -/
lemma natTransFromInitial_unique {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (I : C) (hI : IsInitial I)
    (α : (Functor.const C).obj (F.obj I) ⟶ F)
    (hα : α.app I = 𝟙 (F.obj I)) :
    α = natTransFromInitial F I hI := by
  apply NatTrans.ext
  funext X
  -- The component α.app X : F(I) ⟶ F(X) must equal F.map (hI.to X)
  have nat := α.naturality (hI.to X)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at nat
  simp only [natTransFromInitial]
  rw [hα] at nat
  simp only [Category.id_comp] at nat
  exact nat

/-- Variant: Any natural transformation from the constant functor at `F(I)` to `F`
(where `I` is initial) that acts as identity at `I` is determined by naturality. -/
lemma natTransFromInitial_ext {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (I : C) (hI : IsInitial I)
    (α β : (Functor.const C).obj (F.obj I) ⟶ F)
    (hα : α.app I = 𝟙 (F.obj I)) (hβ : β.app I = 𝟙 (F.obj I)) :
    α = β := by
  rw [natTransFromInitial_unique F I hI α hα, natTransFromInitial_unique F I hI β hβ]

/-- Uniqueness for `evaluationFromPoint`: any natural transformation `pointsFunctor P ⟶ F`
is determined by its value at `𝟙 P`. This is a consequence of the Yoneda lemma. -/
lemma evaluationFromPoint_unique {D : Type*} [Category D] {F : D ⥤ Type _} {P : D}
    (α : pointsFunctor P ⟶ F) :
    α = evaluationFromPoint (α.app P (𝟙 P)) := by
  dsimp [evaluationFromPoint]
  -- Use the equivalence property directly: α = symm x ↔ e α = x
  apply (CategoryTheory.coyonedaEquiv.eq_symm_apply).mpr
  rfl

/-- Two natural transformations `pointsFunctor P ⟶ F` are equal iff they agree at `𝟙 P`.
This is the "evaluation at identity" form of the Yoneda lemma. -/
lemma evaluationFromPoint_ext {D : Type*} [Category D] {F : D ⥤ Type _} {P : D}
    (α β : pointsFunctor P ⟶ F) (h : α.app P (𝟙 P) = β.app P (𝟙 P)) :
    α = β := by
  rw [evaluationFromPoint_unique α, evaluationFromPoint_unique β, h]

end General

noncomputable section

variable (C : Type*) [Category C] [Limits.HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C]

#check SSet.ι₀
#check Δ[1]

--  def zero_vertex : Δ[1] _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)

 def i_0 {X : SSet} : X ⟶ X ⨯ Δ[1] :=
  Limits.prod.lift (𝟙 X) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))

 def i_1 {X : SSet} : X ⟶ X ⨯ Δ[1] :=
  Limits.prod.lift (𝟙 X) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1))

-- @[simp]
-- lemma const_1_eq_deg_0 :
--   SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1 : Δ[1] _⦋0⦌) = SSet.stdSimplex.δ 0 := sorry

-- @[simp]
-- lemma const_0_eq_deg_1 :
--   SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌) = SSet.stdSimplex.δ 1 := sorry

noncomputable abbrev prod_iso {X Y : TopCat} :
  TopCat.toSSet.obj (X ⨯ Y) ≅ TopCat.toSSet.obj X ⨯ TopCat.toSSet.obj Y :=
    letI := Adjunction.rightAdjoint_preservesLimits sSetTopAdj
    PreservesLimitPair.iso TopCat.toSSet X Y

/--The product iso is induced by the projections -/
@[simp]
lemma prod_iso_hom {X Y : TopCat} :
  (prod_iso (X:=X) (Y:=Y)).hom =
    Limits.prod.lift (TopCat.toSSet.map Limits.prod.fst)
      (TopCat.toSSet.map Limits.prod.snd) := by
  have := Adjunction.rightAdjoint_preservesLimits sSetTopAdj
  exact PreservesLimitPair.iso_hom _ _ _

@[simp, reassoc]
lemma prod_iso_hom_fst {X Y : TopCat} :
  (prod_iso (X:=X) (Y:=Y)).hom ≫ Limits.prod.fst =
    TopCat.toSSet.map Limits.prod.fst := by
  have := Adjunction.rightAdjoint_preservesLimits sSetTopAdj
  exact prodComparison_fst _ _ _

@[simp, reassoc]
lemma prod_iso_hom_snd {X Y : TopCat} :
  (prod_iso (X:=X) (Y:=Y)).hom ≫ Limits.prod.snd =
    TopCat.toSSet.map Limits.prod.snd := by
  have := Adjunction.rightAdjoint_preservesLimits sSetTopAdj
  exact prodComparison_snd _ _ _

structure SimplicialHomotopy {X Y : SSet} (f g : X ⟶ Y) where
  hom : X ⨯ Δ[1] ⟶ Y
  comm0 : i_0 ≫ hom = f
  comm1 : i_1 ≫ hom = g

#check ContinuousMap.Homotopy

open unitInterval

def TopCat.I : TopCat.{u} := TopCat.of (ULift I)

def j_0 {X : TopCat}: X ⟶ X ⨯ TopCat.I :=
  Limits.prod.lift (𝟙 X) (TopCat.ofHom (ContinuousMap.const X (ULift.up 0)))

def j_1 {X : TopCat}: X ⟶ X ⨯ TopCat.I :=
  Limits.prod.lift (𝟙 X) (TopCat.ofHom (ContinuousMap.const X (ULift.up 1)))

/--We define our own Homotopy to make it more suitable for the cat theory application -/
structure MyHomotopy {X Y : TopCat} (f₀ f₁ : X ⟶ Y) where
  hom : X ⨯ TopCat.I ⟶ Y
  /-- value of the homotopy at 0 -/
  comm0 : j_0 ≫ hom = f₀
  /-- value of the homotopy at 1 -/
  comm1 : j_1 ≫ hom = f₁

#check MyHomotopy.hom

/-- Relate prodIsoProd to the bundled map constructor -/
lemma prodIsoProd_hom_comp_lift {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    Limits.prod.lift f g ≫ (TopCat.prodIsoProd Y Z).hom =
    TopCat.ofHom (ContinuousMap.prodMk (f.hom : C(X, Y)) (g.hom : C(X, Z))) := by
  rw [← Iso.eq_comp_inv]
  apply Limits.prod.hom_ext
  · rw [Category.assoc, TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
    rfl
  · rw [Category.assoc, TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
    rfl

@[simp]
lemma j_0_comp_to_bundled {X : TopCat.{u}} :
    j_0 ≫ (TopCat.prodIsoProd X TopCat.I).hom =
    TopCat.ofHom
    (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X (ULift.up 0))) := by
  dsimp [j_0]
  apply prodIsoProd_hom_comp_lift

@[simp]
lemma j_1_comp_to_bundled {X : TopCat.{u}} :
    j_1 ≫ (TopCat.prodIsoProd X TopCat.I).hom =
    TopCat.ofHom
    (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X (ULift.up 1))) := by
  dsimp [j_1]
  apply prodIsoProd_hom_comp_lift

/-- Coercion from Homeomorph to ContinuousMap -/
def Homeomorph.toContinuousMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : C(X, Y) :=
  ⟨e, e.continuous_toFun⟩

/-- Isomorphism unlifting the second component -/
def isoUnliftSecond (X : TopCat) : TopCat.of (X × ULift I) ≅ TopCat.of (X × I) :=
  TopCat.isoOfHomeo (Homeomorph.prodCongr (Homeomorph.refl X) Homeomorph.ulift)

/-- Isomorphism swapping product factors -/
def isoSwap (X Y : TopCat) : TopCat.of (X × Y) ≅ TopCat.of (Y × X) :=
  TopCat.isoOfHomeo (Homeomorph.prodComm X Y)

def ContinuousMap.Homotopy.toMyHomotopy {X Y : TopCat} (f₀ f₁ : X ⟶ Y)
  (H : ContinuousMap.Homotopy f₀.hom f₁.hom) :
  MyHomotopy f₀ f₁ where
  hom := (TopCat.prodIsoProd X TopCat.I).hom ≫
         (isoUnliftSecond X).hom ≫
         (isoSwap X (TopCat.of I)).hom ≫
         TopCat.ofHom H.toContinuousMap
  comm0 := by
    rw [←Category.assoc, j_0_comp_to_bundled]
    ext x
    dsimp [isoUnliftSecond, isoSwap]
    exact H.apply_zero x
  comm1 := by
    rw [←Category.assoc, j_1_comp_to_bundled]
    ext x
    dsimp [isoUnliftSecond, isoSwap]
    exact H.apply_one x


@[simp]
lemma j_0_map_comp_prod_iso {X : TopCat} :
    TopCat.toSSet.map j_0 ≫ (prod_iso (X:=X) (Y:=TopCat.I)).hom =
    Limits.prod.lift
    (𝟙 (TopCat.toSSet.obj X))
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const X (ULift.up 0)))) := by
  have := Adjunction.rightAdjoint_preservesLimits sSetTopAdj
  dsimp [j_0, prod_iso, PreservesLimitPair.iso_hom, prodComparison]
  rw [Limits.prod.comp_lift, ← Functor.map_comp, Limits.prod.lift_fst]
  rw [← Functor.map_comp, Limits.prod.lift_snd]
  simp
  rfl

@[simp]
lemma j_1_map_comp_prod_iso {X : TopCat} :
    TopCat.toSSet.map j_1 ≫ (prod_iso (X:=X) (Y:=TopCat.I)).hom =
    Limits.prod.lift
    (𝟙 (TopCat.toSSet.obj X))
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const X (ULift.up 1)))) := by
  have := Adjunction.rightAdjoint_preservesLimits sSetTopAdj
  dsimp [j_1, prod_iso, PreservesLimitPair.iso_hom, prodComparison]
  rw [Limits.prod.comp_lift, ← Functor.map_comp, Limits.prod.lift_fst]
  rw [← Functor.map_comp, Limits.prod.lift_snd]
  rfl


#check SimplexCategory.toTopObjOneHomeo
#check Iso.toEquiv
#check fun (n :  ℕ) => (SSet.toTopSimplex.app ⦋n⦌)
#check fun (n :  ℕ) => (TopCat.homeoOfIso (SSet.toTopSimplex.app ⦋n⦌))

open Simplicial

notation "|" X "|" => SSet.toTop.obj X
notation "∇[" n "]" => stdSimplex ℝ (Fin (n + 1))

namespace SimplexCategory

open SSet

noncomputable def toTopHomeo (n : SimplexCategory) :
    |stdSimplex.{u}.obj n| ≃ₜ stdSimplex ℝ (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (SSet.toTopSimplex.{u}.app n)).trans Homeomorph.ulift

lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    (toTopHomeo m).toFun.comp (SSet.toTop.{u}.map (SSet.stdSimplex.map f)) =
    (stdSimplex.map f).comp n.toTopHomeo := by
  ext x : 1
  exact ULift.up_injective (congr_fun ((forget _).congr_map
    (SSet.toTopSimplex.hom.naturality f)) x)

lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.{u}.map (SSet.stdSimplex.map f) x)) =
      (_root_.stdSimplex.map f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x

lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.invFun.comp (stdSimplex.map f) =
      (SSet.toTop.{u}.map (SSet.stdSimplex.map f)).hom.1.comp n.toTopHomeo.invFun := by
  ext x : 1
  exact congr_fun ((forget _).congr_map
    (SSet.toTopSimplex.inv.naturality f)) _

lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex ℝ (Fin (n.len + 1))) :
    m.toTopHomeo.symm (stdSimplex.map f x) =
      SSet.toTop.{u}.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

/- The topological standard simplex ∇[n] is homeomorph
to the topological realisation of the std n simplex -/
def toTopEquivStd (n : ℕ) : |Δ[n]| ≃ₜ ∇[n] :=
  (SimplexCategory.toTopHomeo (SimplexCategory.mk n))

#check (toTopEquivStd 1)
#check sSetTopAdj
#check stdSimplexHomeomorphUnitInterval

#check Homeomorph.refl
def unitIntervalToTopCat : I ≃ₜ TopCat.I := Homeomorph.ulift.symm

def stdSimplexHomeomorphUnitInterval' : ∇[1] ≃ₜ TopCat.I :=
  stdSimplexHomeomorphUnitInterval.trans (Homeomorph.ulift.symm)

def toTopEquivUnitInt : |Δ[1]| ≃ₜ TopCat.I :=
  (toTopEquivStd 1).trans stdSimplexHomeomorphUnitInterval'

instance : Subsingleton (∇[0]) := by
  change Subsingleton (stdSimplex ℝ (Fin 1))
  infer_instance

instance : Unique (SSet.toTop.obj Δ[0]) := by
  classical
  refine ⟨⟨(toTopEquivStd 0).symm (stdSimplex.vertex 0)⟩, ?_⟩
  intro x
  apply (toTopEquivStd 0).injective
  exact Subsingleton.elim _ _

instance : Unique ((SSet.toTop ⋙ forget TopCat).obj Δ[0]) :=
  inferInstanceAs (Unique (SSet.toTop.obj Δ[0]))

section RealizationPoints

def toTopObjMk {X : SSet} (x : X _⦋0⦌) : SSet.toTop.obj X :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x) default

namespace SSet

-- This lemma exists in `topcat-model-category` as `yonedaEquiv_symm_comp`.
-- Mathlib provides the forward direction `yonedaEquiv_comp`, from which we derive this.
lemma yonedaEquiv_symm_comp {X Y : SSet} (f : X ⟶ Y) (x : X _⦋0⦌) :
    yonedaEquiv.symm (f.app _ x) = yonedaEquiv.symm x ≫ f := by
  apply yonedaEquiv.injective
  -- both sides are morphisms `Δ[0] ⟶ Y`; evaluate via `yonedaEquiv`
  simp [yonedaEquiv_comp]

/-- Evaluation at `0`-simplices as a functor `SSet ⥤ Type`. -/
def eval₀ : SSet ⥤ Type u :=
  (evaluation (SimplexCategoryᵒᵖ) (Type u)).obj (op (SimplexCategory.mk 0))

end SSet

namespace SSet

/-- `eval₀` is naturally isomorphic to `pointsFunctor Δ[0]`.

The Yoneda lemma gives `(Δ[0] ⟶ X) ≃ X _⦋0⦌`, so the functor of points
`Hom(Δ[0], -)` is equivalent to evaluation at `0`-simplices. -/
def eval₀IsoPointsFunctor : eval₀ ≅ pointsFunctor Δ[0] :=
  NatIso.ofComponents
    (fun X => yonedaEquiv.symm.toIso)
    (fun {X Y} f => by
      ext x
      dsimp [eval₀, pointsFunctor]
      -- yonedaEquiv.symm (f.app _ x) = yonedaEquiv.symm x ≫ f
      exact yonedaEquiv_symm_comp f x)

/-- The map sending a `0`-simplex to the corresponding point in `|X|`, as a natural transformation.
-/
def toTopObjMkNat : eval₀ ⟶ (SSet.toTop ⋙ forget TopCat) :=
  eval₀IsoPointsFunctor.hom ≫
    evaluationFromPoint (P := Δ[0]) (F := SSet.toTop ⋙ forget TopCat) default

@[simp]
lemma toTopObjMkNat_app (X : SSet) (x : X _⦋0⦌) : toTopObjMkNat.app X x = toTopObjMk x := by
  dsimp [toTopObjMkNat, toTopObjMk, evaluationFromPoint, eval₀IsoPointsFunctor]
  rfl

@[simp]
lemma toTopObjMkNat_naturality_apply {X Y : SSet} (f : X ⟶ Y) (x : X _⦋0⦌) :
    toTopObjMkNat.app Y (f.app _ x) = (SSet.toTop.map f) (toTopObjMkNat.app X x) := by
    -- Naturality is automatic now
    exact congrFun (toTopObjMkNat.naturality f) x

/-!
## Connection to Abstract Framework
-/

/-- The naturality condition for `toTopObjMkNat` matches `evaluationFromPoint`. -/
lemma toTopObjMkNat_eq_evaluationFromPoint :
    let pt₀ : (SSet.toTop ⋙ forget TopCat).obj Δ[0] := default
    toTopObjMkNat = eval₀IsoPointsFunctor.hom ≫
      evaluationFromPoint (F := SSet.toTop ⋙ forget TopCat) (P := Δ[0]) pt₀ :=
  rfl

/-!
## Application of Uniqueness Lemmas

The uniqueness lemmas from the `General` section can be applied to show that
various constructions in this file are uniquely determined by their universal properties.
-/

/-- The identity on Δ[0] evaluated via yonedaEquiv gives the unique 0-simplex. -/
private lemma yonedaEquiv_id_eq_const :
    yonedaEquiv (𝟙 Δ[0]) = SSet.stdSimplex.const _ 0 _ := by
  simp only [yonedaEquiv, uliftYonedaEquiv, stdSimplex.const, stdSimplex.objMk]
  ext
  simp [OrderHom.const]

/-- `toTopObjMkNat` is uniquely determined: any natural transformation
`eval₀ ⟶ toTop ⋙ forget TopCat` that sends the identity simplex of `Δ[0]` to `default`
must equal `toTopObjMkNat`. -/
lemma toTopObjMkNat_unique (α : eval₀ ⟶ (SSet.toTop ⋙ forget TopCat))
    (hα : α.app Δ[0] (SSet.stdSimplex.const _ 0 _) = default) :
    α = toTopObjMkNat := by
  let α' : pointsFunctor Δ[0] ⟶ (SSet.toTop ⋙ forget TopCat) := eval₀IsoPointsFunctor.inv ≫ α
  have key : α' = evaluationFromPoint (P := Δ[0]) default := by
    rw [evaluationFromPoint_unique α']
    congr 1
    show (eval₀IsoPointsFunctor.inv ≫ α).app Δ[0] (𝟙 Δ[0]) = default
    simp only [NatTrans.comp_app, eval₀IsoPointsFunctor, NatIso.ofComponents_inv_app,
      Equiv.toIso_inv, Equiv.symm_symm]
    change α.app Δ[0] (yonedaEquiv (𝟙 Δ[0])) = default
    rw [yonedaEquiv_id_eq_const, hα]
  have hα_comp : α = eval₀IsoPointsFunctor.hom ≫ α' := by
    dsimp [α']
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hα_comp, key, ← toTopObjMkNat_eq_evaluationFromPoint]

/-- Two natural transformations `eval₀ ⟶ toTop ⋙ forget TopCat` that agree on the
identity simplex are equal. -/
lemma toTopObjMkNat_ext (α β : eval₀ ⟶ (SSet.toTop ⋙ forget TopCat))
    (h : α.app Δ[0] (SSet.stdSimplex.const _ 0 _) = β.app Δ[0] (SSet.stdSimplex.const _ 0 _)) :
    α = β := by
  let α' : pointsFunctor Δ[0] ⟶ _ := eval₀IsoPointsFunctor.inv ≫ α
  let β' : pointsFunctor Δ[0] ⟶ _ := eval₀IsoPointsFunctor.inv ≫ β
  have hα : α' = evaluationFromPoint (α'.app Δ[0] (𝟙 Δ[0])) := evaluationFromPoint_unique α'
  have hβ : β' = evaluationFromPoint (β'.app Δ[0] (𝟙 Δ[0])) := evaluationFromPoint_unique β'
  have heq : α'.app Δ[0] (𝟙 Δ[0]) = β'.app Δ[0] (𝟙 Δ[0]) := by
    show (eval₀IsoPointsFunctor.inv ≫ α).app Δ[0] (𝟙 Δ[0]) =
         (eval₀IsoPointsFunctor.inv ≫ β).app Δ[0] (𝟙 Δ[0])
    simp only [NatTrans.comp_app, eval₀IsoPointsFunctor, NatIso.ofComponents_inv_app,
      Equiv.toIso_inv, Equiv.symm_symm]
    change α.app Δ[0] (yonedaEquiv (𝟙 Δ[0])) = β.app Δ[0] (yonedaEquiv (𝟙 Δ[0]))
    simp only [yonedaEquiv_id_eq_const, h]
  have hα_eq : α = eval₀IsoPointsFunctor.hom ≫ α' := by
    dsimp [α']
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hβ_eq : β = eval₀IsoPointsFunctor.hom ≫ β' := by
    dsimp [β']
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hα_eq, hβ_eq, hα, hβ, heq]

/-- Naturality of `toTopObjMk`: the realization functor commutes with vertex maps. -/
@[simp]
lemma toTop_map_toTopObjMk {X Y : SSet} (f : X ⟶ Y) (x : X _⦋0⦌) :
    SSet.toTop.map f (toTopObjMk x) = toTopObjMk (f.app _ x) := by
  simp only [← toTopObjMkNat_app]
  exact (congrFun (toTopObjMkNat.naturality f) x).symm

end SSet

/-- The realization functor maps constant morphisms to constant functions. -/
@[simp]
lemma toTop_map_const_apply {X Y : SSet} (y : Y _⦋0⦌) (x : SSet.toTop.obj X) :
    SSet.toTop.map (SSet.const (X:=X) y) x = toTopObjMk y := by
  let p : X ⟶ Δ[0] := SSet.stdSimplex.isTerminalObj₀.from _
  have : (TopCat.Hom.hom (SSet.toTop.map p)) x = toTopObjMk (SSet.stdSimplex.const _ 0 _)
    := Subsingleton.elim _ _
  rw [← SSet.comp_const (f := p), Functor.map_comp]
  simp [this]


/-- The toTop homeomorphism preserves vertex images.
This is the key lemma connecting simplicial vertices to geometric vertices. -/
@[simp]
lemma SimplexCategory.toTopHomeo_toTopObjMk {n : ℕ} (i : Fin (n + 1)) :
    (SimplexCategory.toTopHomeo ⦋n⦌)
      (toTopObjMk (SSet.stdSimplex.const _ i _)) =
      stdSimplex.vertex i := by
  apply (SimplexCategory.toTopHomeo_naturality_apply
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) _).trans
  have : (SimplexCategory.toTopHomeo ⦋0⦌) default = stdSimplex.vertex 0 := by
    simpa using Subsingleton.elim _ _
  rw [this]
  simp [len_mk, Nat.reduceAdd, Fin.isValue, stdSimplex.map_vertex, Subtype.mk.injEq]
  rfl

end RealizationPoints

namespace SSet.stdSimplex

noncomputable def toTopObjHomeoUnitInterval :
    |Δ[1]| ≃ₜ I :=
  (SimplexCategory.toTopHomeo ⦋1⦌).trans stdSimplexHomeomorphUnitInterval

/-- Unified lemma: the homeomorphism sends vertices of Δ[1] to endpoints of I. -/
lemma toTopObjHomeoUnitInterval_vertex (i : Fin 2) :
    toTopObjHomeoUnitInterval (toTopObjMk (SSet.stdSimplex.const _ i _)) =
    if i = 0 then 0 else 1 := by
  have h : (SimplexCategory.toTopHomeo ⦋1⦌)
      (toTopObjMk (SSet.stdSimplex.const _ i _)) = stdSimplex.vertex i := by
    simpa using SimplexCategory.toTopHomeo_toTopObjMk (n := 1) (i := i)
  dsimp [toTopObjHomeoUnitInterval, stdSimplexHomeomorphUnitInterval]
  have h' := congrArg stdSimplexHomeomorphUnitInterval h
  fin_cases i
  · simpa [stdSimplexHomeomorphUnitInterval_zero] using h'
  · simpa [stdSimplexHomeomorphUnitInterval_one] using h'

/-- The homeomorphism sends the 0-vertex to 0. -/
@[simp]
lemma toTopObjHomeoUnitInterval_zero :
    toTopObjHomeoUnitInterval (toTopObjMk (SSet.stdSimplex.const _ 0 _)) = 0 := by
  simpa using (toTopObjHomeoUnitInterval_vertex 0)

/-- The homeomorphism sends the 1-vertex to 1. -/
@[simp]
lemma toTopObjHomeoUnitInterval_one :
    toTopObjHomeoUnitInterval (toTopObjMk (SSet.stdSimplex.const _ 1 _)) = 1 := by
  simpa using (toTopObjHomeoUnitInterval_vertex 1)

end SSet.stdSimplex

@[simp]
lemma toTopEquivUnitInt_apply (x : |Δ[1]|) :
    toTopEquivUnitInt x =
      ULift.up (SSet.stdSimplex.toTopObjHomeoUnitInterval x) := by
  rfl

@[simp]
lemma toTopEquivUnitInt_zero :
    toTopEquivUnitInt (toTopObjMk (SSet.stdSimplex.obj₀Equiv.symm 0)) = ULift.up 0 := by
  simp [SSet.stdSimplex.obj₀Equiv_symm_apply]

@[simp]
lemma toTopEquivUnitInt_one :
    toTopEquivUnitInt (toTopObjMk (SSet.stdSimplex.obj₀Equiv.symm 1)) = ULift.up 1 := by
  simp [SSet.stdSimplex.obj₀Equiv_symm_apply]

/- Define iota as the map induced by toTopEquivStd -/
def iota : Δ[1] ⟶ TopCat.toSSet.obj (TopCat.of (∇[1])) :=
  sSetTopAdj.homEquiv _ _ (TopCat.ofHom (toContinuousMap (toTopEquivStd 1)))

/-- The explicit map into the simplicial object of the interval,
induced by the equivalence `|Δ[1]| ≃ I`. -/
def iota_I : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I :=
  sSetTopAdj.homEquiv _ _ (TopCat.ofHom (toContinuousMap toTopEquivUnitInt))

/-- The map `X × Δ[1] ⟶ Top(X × I)` constructed via the product isomorphism
and `iota_I`. This serves as the bridge between simplicial and topological homotopies. -/
def connecting_map (X : TopCat) :
  TopCat.toSSet.obj X ⨯ Δ[1] ⟶ TopCat.toSSet.obj (X ⨯ TopCat.I) :=
  Limits.prod.map (𝟙 _) iota_I ≫ (prod_iso (X:=X) (Y:=TopCat.I)).inv

/-- iota_I maps the 0-vertex to the constant map at 0. -/
lemma iota_I_0 {X : TopCat} :
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) ≫ iota_I =
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const X (ULift.up 0))) := by
  dsimp [iota_I]
  rw [Adjunction.homEquiv_unit, ← Category.assoc, ← sSetTopAdj.unit_naturality, Category.assoc,
   ← Functor.map_comp, ← SSet.stdSimplex.obj₀Equiv_symm_apply 0]
  have : SSet.toTop.map (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) ≫
      (TopCat.ofHom (toContinuousMap toTopEquivUnitInt)) =
      sSetTopAdj.counit.app X ≫ (TopCat.ofHom (ContinuousMap.const X (ULift.up 0))) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    simp [ContinuousMap.comp_apply, toTop_map_const_apply]
  rw [this, Functor.map_comp, ← Category.assoc, Adjunction.right_triangle_components]
  simp

/-- iota_I maps the 1-vertex to the constant map at 1. -/
lemma iota_I_1 {X : TopCat} :
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1) ≫ iota_I =
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const X (ULift.up 1))) := by
  dsimp [iota_I]
  rw [Adjunction.homEquiv_unit, ← Category.assoc, ← sSetTopAdj.unit_naturality, Category.assoc,
   ← Functor.map_comp, ← SSet.stdSimplex.obj₀Equiv_symm_apply 1]
  have : SSet.toTop.map (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) ≫
      (TopCat.ofHom (toContinuousMap toTopEquivUnitInt)) =
      sSetTopAdj.counit.app X ≫ (TopCat.ofHom (ContinuousMap.const X (ULift.up 1))) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    simp [ContinuousMap.comp_apply, toTop_map_const_apply]
  rw [this, Functor.map_comp, ← Category.assoc, Adjunction.right_triangle_components]
  simp

/-- Precomposing the connecting map with `i_0` yields the map induced by `j_0`. -/
lemma i_0_comp_connecting_map (X : TopCat) :
    i_0 ≫ connecting_map X = TopCat.toSSet.map j_0 := by
  dsimp [i_0, connecting_map]
  rw [← Category.assoc, Iso.comp_inv_eq, j_0_map_comp_prod_iso]
  apply Limits.prod.hom_ext
  · simpa using (Limits.prod.lift_fst _ _).symm
  · simpa [Limits.prod.lift_snd] using iota_I_0

/-- Precomposing the connecting map with `i_1` yields the map induced by `j_1`. -/
lemma i_1_comp_connecting_map (X : TopCat) :
    i_1 ≫ connecting_map X = TopCat.toSSet.map j_1 := by
  dsimp [i_1, connecting_map]
  rw [← Category.assoc, Iso.comp_inv_eq, j_1_map_comp_prod_iso]
  apply Limits.prod.hom_ext
  · simpa using (Limits.prod.lift_fst _ _).symm
  · simpa [Limits.prod.lift_snd] using iota_I_1

def topHomotopyToSimplicialHomotopy
  {X Y : TopCat} (f g : X ⟶ Y)
  (H : ContinuousMap.Homotopy f.hom g.hom) :
  SimplicialHomotopy
    (TopCat.toSSet.map f)
    (TopCat.toSSet.map g) where
  hom := connecting_map X ≫ TopCat.toSSet.map H.toMyHomotopy.hom
  comm0 := by
    rw [← Category.assoc, i_0_comp_connecting_map, ← Functor.map_comp,
      H.toMyHomotopy.comm0]
  comm1 := by
    rw [← Category.assoc, i_1_comp_connecting_map, ← Functor.map_comp,
      H.toMyHomotopy.comm1]
