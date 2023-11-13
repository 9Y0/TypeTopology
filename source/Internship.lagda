References:

[1]: Thorsten Altenkirch, Nils Anders Danielsson, Nicolai Kraus:
     Partiality, Revisited - The Partiality Monad as a Quotient Inductive-Inductive Type.
     FoSSaCS 2017: 534-549
     https://arxiv.org/abs/1610.09254

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import MLTT.Spartan

open import UF.Base

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

open import UF.Equiv
open import UF.EquivalenceExamples

module Internship
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import Posets.Poset fe

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥 renaming (⊥ to least)

open import Categories.Category fe

\end{code}

A directed partiality algebra over A is a pointed DCPO 𝓓, together with an
inclusion A → ⟪ 𝓓 ⟫

\begin{code}

record DPartOb
        {𝓤 : Universe} -- where the type to lift lives
        (A : 𝓤 ̇ )      -- the type to lift
        (𝓦 : Universe) -- where the carrier lives
        (𝓣 : Universe) -- where the truth values live
       : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇  where
 field
  𝓓 : DCPO⊥ {𝓦} {𝓣}
  η : A → ⟪ 𝓓 ⟫

-- FIXME: Use an equivalence of types instead
DPartOb＝ : {A : 𝓤 ̇ } {X Y : DPartOb A 𝓦 𝓣}
          → let module X = DPartOb X
                module Y = DPartOb Y
         in (p : ⟪ X.𝓓 ⟫ ＝ ⟪ Y.𝓓 ⟫)
          → (λ y₁ y₂ → idtofun _ _ (p ⁻¹) y₁ ⊑⟪ X.𝓓 ⟫ idtofun _ _ (p ⁻¹) y₂) ＝ underlying-order⊥ Y.𝓓
          → idtofun _ _ p (least X.𝓓) ＝ (least Y.𝓓)
          → idtofun _ _ p ∘ X.η ＝ Y.η
          → X ＝ Y
DPartOb＝ {X = X} {Y} refl refl refl refl = γ p q
 where
  module X = DPartOb X
  module Y = DPartOb Y

  p : ⊥-is-least X.𝓓 ＝ ⊥-is-least Y.𝓓
  p = Π-is-prop fe (prop-valuedness (X.𝓓 ⁻) _) _ _

  q : axioms-of-dcpo (X.𝓓 ⁻) ＝ axioms-of-dcpo (Y.𝓓 ⁻)
  q = dcpo-axioms-is-prop (underlying-order⊥ X.𝓓) _ _

  γ : ⊥-is-least X.𝓓 ＝ ⊥-is-least Y.𝓓
    → axioms-of-dcpo (X.𝓓 ⁻) ＝ axioms-of-dcpo (Y.𝓓 ⁻)
    → _ ＝ _
  γ refl refl = refl

\end{code}

DPartOb is equivalent to the Sigma type corresponding to the one given in [1].

\begin{code}

DPartAxioms : {X : 𝓦 ̇ } (_⊑_ : X → X → 𝓣 ̇ ) (⊥ : X)
              (∐ : ({I : 𝓥 ̇ } → (Σ α ꞉ (I → X) , is-directed _⊑_ α) → X))
            → 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇ 
DPartAxioms {X = X} _⊑_ ⊥ ∐ =
 PosetAxioms.poset-axioms _⊑_ ×
 is-least _⊑_ ⊥ × 
 ({I : 𝓥 ̇ } {α : I → X} (δ : is-directed _⊑_ α) → is-sup _⊑_ (∐ (α , δ)) α)

DPartOb' : (A : 𝓤 ̇ ) (𝓦 𝓣 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
DPartOb' A 𝓦 𝓣 =
 Σ X ꞉ 𝓦 ̇ ,
 Σ _⊑_ ꞉ (X → X → 𝓣 ̇ ) ,
 Σ ⊥ ꞉ X ,
 Σ η ꞉ (A → X) ,
 Σ ∐ ꞉ ({I : 𝓥 ̇ } → (Σ α ꞉ (I → X) , is-directed _⊑_ α) → X) ,
  (DPartAxioms _⊑_ ⊥ ∐)

DPartOb≃DPartOb' : {A : 𝓤 ̇ } {𝓦 𝓣 : Universe}
                 → DPartOb A 𝓦 𝓣  ≃ DPartOb' A 𝓦 𝓣
DPartOb≃DPartOb' {A = A} {𝓦} {𝓣} = qinveq f (g , gf , fg)
 where
  f : DPartOb A 𝓦 𝓣  → DPartOb' A 𝓦 𝓣
  f X = ⟪ 𝓓 ⟫ ,
        underlying-order⊥ 𝓓 ,
        least 𝓓 ,
        η ,
        (λ (α , δ) → ∐ (𝓓 ⁻) δ) ,
        pr₁ (axioms-of-dcpo (𝓓 ⁻)) ,
        ⊥-is-least 𝓓 ,
        ∐-is-sup (𝓓 ⁻)
   where
    open DPartOb X

  g : DPartOb' A 𝓦 𝓣 → DPartOb A 𝓦 𝓣
  g (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , pa , ⊥ₓ-is-least , ∐ₓ-is-sup) =
   record { 𝓓 = 𝓓 , ⊥ₓ , ⊥ₓ-is-least ; η = ηₓ }
   where
    𝓓 : DCPO {𝓦} {𝓣}
    𝓓 = X , _⊑ₓ_ , pa , (λ I α δ → ∐ₓ (α , δ) , ∐ₓ-is-sup δ)

  gf : g ∘ f ∼ id
  gf X = DPartOb＝ refl refl refl refl

  fg : f ∘ g ∼ id
  fg _ = refl

\end{code}

A morphism of partiality algebras over A, is a strict continuous map which
preserves the inclusions of A.

\begin{code}

module _ {𝓤 : Universe} {A : 𝓤 ̇ }
         {𝓦₁ 𝓦₂ 𝓣₁ 𝓣₂ : Universe}
        where

 DPartHom : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
          →  𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦₁ ⊔ 𝓦₂ ⊔ 𝓣₁ ⊔ 𝓣₂ ̇
 DPartHom X Y =
  Σ f ꞉ DCPO⊥[ X.𝓓 , Y.𝓓 ] ,
   is-strict X.𝓓 Y.𝓓 [ X.𝓓 ⁻ , Y.𝓓 ⁻ ]⟨ f ⟩ ×
   [ X.𝓓 ⁻ , Y.𝓓 ⁻ ]⟨ f ⟩ ∘ X.η ∼ Y.η
  where
   module X = DPartOb X
   module Y = DPartOb Y

 underlying-scott-continuous-map : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                                   (f : DPartHom X Y)
                                 → let module X = DPartOb X
                                       module Y = DPartOb Y
                                in DCPO⊥[ X.𝓓 , Y.𝓓 ]
 underlying-scott-continuous-map X Y (f , _ , _) = f

 DPart[_,_]⟨_⟩ : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
               → let module X = DPartOb X
                     module Y = DPartOb Y
              in (f : DPartHom X Y) → ⟪ X.𝓓 ⟫ → ⟪ Y.𝓓 ⟫
 DPart[ X , Y ]⟨ f ⟩ =
  underlying-function (X.𝓓 ⁻) (Y.𝓓 ⁻) (underlying-scott-continuous-map X Y f)
  where
   module X = DPartOb X
   module Y = DPartOb Y

 continuity-of-DPartHom : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                          (f : DPartHom X Y)
                        → let module X = DPartOb X
                              module Y = DPartOb Y
                       in is-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) DPart[ X , Y ]⟨ f ⟩
 continuity-of-DPartHom X Y f =
  continuity-of-function (X.𝓓 ⁻) (Y.𝓓 ⁻) (underlying-scott-continuous-map X Y f)
  where
   module X = DPartOb X
   module Y = DPartOb Y

 monotonicity-of-DPartHom : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                            (f : DPartHom X Y)
                          → let module X = DPartOb X
                                module Y = DPartOb Y
                         in is-monotone (X.𝓓 ⁻) (Y.𝓓 ⁻) DPart[ X , Y ]⟨ f ⟩
 monotonicity-of-DPartHom X Y f =
  monotone-if-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) (underlying-scott-continuous-map X Y f)
  where
   module X = DPartOb X
   module Y = DPartOb Y

 strictness : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
              (f : DPartHom X Y)
            → let module X = DPartOb X
                  module Y = DPartOb Y
           in is-strict X.𝓓 Y.𝓓 DPart[ X , Y ]⟨ f ⟩
 strictness X Y (_ , s , _) = s

 η-preservation : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                  (f : DPartHom X Y)
                → let module X = DPartOb X
                      module Y = DPartOb Y
               in DPart[ X , Y ]⟨ f ⟩ ∘ X.η ∼ Y.η
 η-preservation X Y (_ , _ , h) = h

 DPartHom＝ : {X : DPartOb A 𝓦₁ 𝓣₁} {Y : DPartOb A 𝓦₂ 𝓣₂} {f g : DPartHom X Y}
            → DPart[ X , Y ]⟨ f ⟩ ＝ DPart[ X , Y ]⟨ g ⟩
            → f ＝ g
 DPartHom＝ {X} {Y} {f} {g} p =
  to-subtype-＝
   (λ f →
     ×-is-prop
      (being-strict-is-prop X.𝓓 Y.𝓓 (underlying-function (X.𝓓 ⁻) (Y.𝓓 ⁻) f))
      (Π-is-prop fe λ _ → sethood (Y.𝓓 ⁻)))
   (to-subtype-＝ (being-continuous-is-prop (X.𝓓 ⁻) (Y.𝓓 ⁻)) p)
  where
   module X = DPartOb X
   module Y = DPartOb Y

 DPartHom-is-set : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                 → is-set (DPartHom X Y)
 DPartHom-is-set X Y =
  Σ-is-set
   (Σ-is-set
    (Π-is-set fe (λ _ → sethood (Y.𝓓 ⁻)))
    (λ f → props-are-sets (being-continuous-is-prop (X.𝓓 ⁻) (Y.𝓓 ⁻) f)))
   λ f → props-are-sets (×-is-prop (being-strict-is-prop X.𝓓 Y.𝓓 (pr₁ f))
                                   (Π-is-prop fe (λ _ → sethood (Y.𝓓 ⁻))))
  where
   module X = DPartOb X
   module Y = DPartOb Y

\end{code}

DPartHom is equivalent to the Sigma type corresponding to the one given in [1].

\begin{code}

 image-is-directed-if-monotone : {I : 𝓥 ̇ } {X : 𝓦₁ ̇ } {H : 𝓦₂ ̇ } {α : I → X} {f : X → H}
                               → (_⊑ₓ_ : X → X → 𝓣₁ ̇ ) (_⊑ₕ_ : H → H → 𝓣₂ ̇ )
                               → (f⊑ : (x₁ x₂ : X) → x₁ ⊑ₓ x₂ → f x₁ ⊑ₕ f x₂)
                               → (δ : is-directed _⊑ₓ_ α)
                               → is-directed _⊑ₕ_ (f ∘ α)
 image-is-directed-if-monotone {α = α} _⊑ₓ_ _⊑ₕ_ f⊑ δ =
  inhabited-if-directed _⊑ₓ_ α δ ,
  λ i j → ∥∥-functor
           (λ (k , αᵢ⊑αₖ , αⱼ⊑αₖ) → k , f⊑ _ _ αᵢ⊑αₖ , f⊑ _ _ αⱼ⊑αₖ)
           (semidirected-if-directed _⊑ₓ_ α δ i j)

 DPartHom' : DPartOb' A 𝓦₁ 𝓣₁  → DPartOb' A 𝓦₂ 𝓣₂ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦₁ ⊔ 𝓦₂ ⊔ 𝓣₁ ⊔ 𝓣₂ ̇
 DPartHom' (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , _) (H , _⊑ₕ_ , ⊥ₕ , ηₕ , ∐ₕ , _) =
  Σ f ꞉ (X → H) ,
  Σ f⊑ ꞉ ((x₁ x₂ : X) → x₁ ⊑ₓ x₂ → f x₁ ⊑ₕ f x₂) ,
   (f ⊥ₓ ＝ ⊥ₕ) ×
   (f ∘ ηₓ ＝ ηₕ) ×
   ({I : 𝓥 ̇ } (α : I → X) (δ : is-directed _⊑ₓ_ α) →
    f (∐ₓ (α , δ)) ＝ ∐ₕ (f ∘ α , image-is-directed-if-monotone _⊑ₓ_ _⊑ₕ_ f⊑ δ))

 DPartHom≃DPartHom' : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                    → DPartHom X Y
                    ≃ DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y)
 DPartHom≃DPartHom' X Y = qinveq ψ (ϕ , ϕψ , ψϕ)
  where
   module X = DPartOb X
   module Y = DPartOb Y

   ψ : DPartHom X Y → DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y)
   ψ f = DPart[ X , Y ]⟨ f ⟩ ,
         monotone-if-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) (underlying-scott-continuous-map X Y f) ,
         strictness X Y f ,
         dfunext fe (η-preservation X Y f) ,
         γ
    where
     γ : {I : 𝓥 ̇ } (α : I → ⟪ X.𝓓 ⟫) (δ : is-Directed (X.𝓓 ⁻) α)
       → DPart[ X , Y ]⟨ f ⟩ (∐ (X.𝓓 ⁻) δ)
       ＝ ∐ (Y.𝓓 ⁻) (image-is-directed' (X.𝓓 ⁻) (Y.𝓓 ⁻) (underlying-scott-continuous-map X Y f) δ)
     γ α δ = continuous-∐-＝ (X.𝓓 ⁻) (Y.𝓓 ⁻) (underlying-scott-continuous-map X Y f) δ

   ϕ : DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y) → DPartHom X Y
   ϕ (f , f⊑ , f⊥ , fη , f∐) = (f , γ) , f⊥ , happly fη
    where
     γ : is-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) f
     γ I α δ = transport⁻¹ (λ y → is-sup (underlying-order⊥ Y.𝓓) y (f ∘ α))
                (f∐ α δ)
                (∐-is-sup (Y.𝓓 ⁻) _)

   ϕψ : ϕ ∘ ψ ∼ id
   ϕψ f = DPartHom＝ {X} {Y} refl

   ψϕ : ψ ∘ ϕ ∼ id
   ψϕ (f , f⊑ , f⊥ , fη , f∐) =
    to-subtype-＝
     (λ f →
       Σ-is-prop
        (Π₃-is-prop fe (λ x₁ x₂ x₁⊑x₂ → prop-valuedness (Y.𝓓 ⁻) (f x₁) (f x₂)))
        λ f⊑ →
         ×₃-is-prop
          (sethood (Y.𝓓 ⁻))
          (Π-is-set fe (λ a → sethood (Y.𝓓 ⁻)))
          (Π-is-prop' fe (λ I → Π₂-is-prop fe (λ α δ → sethood (Y.𝓓 ⁻)))))
     refl

\end{code}

\begin{code}

DPartId : {A : 𝓤 ̇ } (X : DPartOb A 𝓦 𝓣) → DPartHom X X
DPartId X = (id , id-is-continuous (X.𝓓 ⁻)) ,
            refl ,
            λ _ → refl
 where
  module X = DPartOb X

DPartComp : {A : 𝓤 ̇ } {𝓦₁ 𝓦₂ 𝓦₃ 𝓣₁ 𝓣₂ 𝓣₃ : Universe}
            (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂) (Z : DPartOb A 𝓦₃ 𝓣₃)
          → DPartHom X Y → DPartHom Y Z → DPartHom X Z
DPartComp X Y Z f g =
 DCPO-∘ (X.𝓓 ⁻) (Y.𝓓 ⁻) (Z.𝓓 ⁻)
  (underlying-scott-continuous-map X Y f)
  (underlying-scott-continuous-map Y Z g) ,
 (ap DPart[ Y , Z ]⟨ g ⟩ (strictness X Y f) ∙ strictness Y Z g) ,
 λ a → ap DPart[ Y , Z ]⟨ g ⟩ (η-preservation X Y f a) ∙ η-preservation Y Z g a
 where
  module X = DPartOb X
  module Y = DPartOb Y
  module Z = DPartOb Z

DPartPre : (A : 𝓤 ̇ ) (𝓦 𝓣 : Universe)
         → precategory (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺) (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓣)
DPartPre A 𝓦 𝓣 =
 make
  (DPartOb A 𝓦 𝓣 , DPartHom , DPartId , DPartComp)
  (DPartHom-is-set ,
   (λ X Y f → DPartHom＝ {X = X} {Y} refl) ,
   (λ X Y f → DPartHom＝ {X = X} {Y} refl) ,
   λ X Y Z W f g h → DPartHom＝ {X = X} {W} refl)

\end{code}

We now consider the QIIT from [1] adapted to a DCPO setting.

\begin{code}

postulate
 _⊥ : (A : 𝓤 ̇ ) → 𝓥 ⁺ ⊔ 𝓤 ̇
 Leq : (A : 𝓤 ̇ ) → A ⊥ → A ⊥ → 𝓥 ⁺ ⊔ 𝓤 ̇

syntax Leq A x y = x ⊑[ A ] y

module _ {A : 𝓤 ̇ } where
 postulate
  incl         : A → A ⊥
  bot          : A ⊥
  lub          : {I : 𝓥 ̇ } → (Σ α ꞉ (I → A ⊥) , is-directed (Leq A) α) → A ⊥
  Leq-anti-sym : (x y : A ⊥) → x ⊑[ A ] y → y ⊑[ A ] x → x ＝ y
  ⊥-is-set     : is-set (A ⊥)

  Leq-refl          : (x : A ⊥) → x ⊑[ A ] x
  Leq-trans         : (x y z : A ⊥) → x ⊑[ A ] y → y ⊑[ A ] z → x ⊑[ A ] z
  bot-leq           : (x : A ⊥) → bot ⊑[ A ] x
  lub-is-upperbound : {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-directed (Leq A) α)
                      (i : I) → α i ⊑[ A ] lub (α , δ)
  lub-is-lowerbound-of-upperbounds
                    : {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-directed (Leq A) α) (v : A ⊥)
                    → ((i : I) → α i ⊑[ A ] v)
                    → lub (α , δ) ⊑[ A ] v
  Leq-is-prop-valued : (x y : A ⊥) → is-prop (x ⊑[ A ] y)

lub-is-sup : {A : 𝓤 ̇ } {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-directed (Leq A) α)
           → is-sup (Leq A) (lub (α , δ)) α
lub-is-sup δ = lub-is-upperbound δ , lub-is-lowerbound-of-upperbounds δ

Lift-as-DCPO : (A : 𝓤 ̇ ) → DCPO
Lift-as-DCPO A = A ⊥ , Leq A , pa , γ
 where
  pa : PosetAxioms.poset-axioms (Leq A)
  pa = ⊥-is-set , Leq-is-prop-valued , Leq-refl , Leq-trans , Leq-anti-sym

  γ : is-directed-complete (Leq A)
  γ I α δ = (lub (α , δ)) , lub-is-sup δ

Lift-as-DPart : (A : 𝓤 ̇ ) → DPartOb A (𝓥 ⁺ ⊔ 𝓤) (𝓥 ⁺ ⊔ 𝓤)
Lift-as-DPart A = record { 𝓓 = Lift-as-DCPO A , bot , bot-leq ; η = incl }

postulate
 -- FIXME: We want X to be able to quanitify over 𝓦 and 𝓣. However, this now
 -- means that Lift-as-DPart A and X live in a different category, as their
 -- universe levels don't match up.
 --
 -- The reason why we want different universe levels, is because the Z we define
 -- for the induction principle, lives in a differnt universe from A⊥.
 --
 -- The elim principle of A⊥, should be thay A⊥ is the initial DPart algebra,
 -- so I'm afraid that this postulate is incorrect.
 --
 -- However, this is also what they do in [1], see
 -- https://www.cse.chalmers.se/~nad/publications/altenkirch-danielsson-kraus-partiality/Partiality-algebra.Eliminators.html#3936
 ⊥-initial : {A : 𝓤 ̇ } (X : DPartOb A 𝓦 𝓣)
           → is-singleton (DPartHom (Lift-as-DPart A) X)

-- We actually need P to be prop-valued here, as otherwise we cannot prove that
-- antisymmetry holds in the DCPO Z
⊥-induction : {A : 𝓤 ̇ } {P : A ⊥ → 𝓦 ̇ }
            → ((x : A ⊥) → is-prop (P x))
            → P bot
            → ((a : A) → P (incl a))
            → ({I : 𝓥 ̇ } (α : I → A ⊥) (δ : is-directed (Leq A) α)
              → ((i : I) → P (α i))
              → P (lub (α , δ)))
            → (x : A ⊥) → P x
⊥-induction {𝓤} {𝓦} {A} {P} P-prop-valued P-bot P-incl P-lub x =
 transport P
  (happly pr₁∘f x)
  (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ f ⟩ x))
 where
  Z : DPartOb A (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦) (𝓥 ⁺ ⊔ 𝓤)
  Z = record
   { 𝓓 = 𝓓 , (bot , P-bot) , λ (y , p) → bot-leq y
   ; η = λ a → incl a , P-incl a }
   where
    𝓓 : DCPO
    𝓓 = (Σ x ꞉ A ⊥ , P x) ,
        (λ (x₁ , _) (x₂ , _) → x₁ ⊑[ A ] x₂) ,
        (subsets-of-sets-are-sets (A ⊥) P ⊥-is-set (P-prop-valued _) ,
         (λ (x₁ , _) (x₂ , _) →  Leq-is-prop-valued x₁ x₂) ,
         (λ (x , _) → Leq-refl x) ,
         (λ (x₁ , _) (x₂ , _) (x₃ , _) → Leq-trans x₁ x₂ x₃) ,
         (λ (x₁ , _) (x₂ , _) x₁⊑x₂ x₂⊑x₁ → to-subtype-＝ P-prop-valued (Leq-anti-sym x₁ x₂ x₁⊑x₂ x₂⊑x₁))) ,
        λ I α δ →
         (lub (pr₁ ∘ α , δ) , P-lub (pr₁ ∘ α) δ (pr₂ ∘ α)) ,
         lub-is-upperbound δ ,
         λ v → lub-is-lowerbound-of-upperbounds δ (pr₁ v)

  module Z = DPartOb Z

  pr₁-as-DPartHom : DPartHom Z (Lift-as-DPart A)
  pr₁-as-DPartHom = (pr₁ , pr₁-continious) , refl , λ _ → refl
   where
    pr₁-continious : is-continuous (Z.𝓓 ⁻) (Lift-as-DCPO A) pr₁
    pr₁-continious I α δ = lub-is-sup δ

  f : DPartHom (Lift-as-DPart A) Z
  f = center (⊥-initial Z)

  pr₁∘f : pr₁ ∘ DPart[ Lift-as-DPart A , Z ]⟨ f ⟩ ＝ id
  pr₁∘f = ap (DPart[ Lift-as-DPart A , Lift-as-DPart A ]⟨_⟩) γ
   where
    γ : DPartComp (Lift-as-DPart A) Z (Lift-as-DPart A) f pr₁-as-DPartHom
     ＝ DPartId (Lift-as-DPart A)
    γ = singletons-are-props (⊥-initial (Lift-as-DPart A)) _ _

module _ {A : 𝓤 ̇ }
         (P : A ⊥ → 𝓦 ̇ )
         (Q : {x y : A ⊥} → P x → P y → x ⊑[ A ] y → 𝓦' ̇ )
        where

 _Σ⊑_ : Σ P → Σ P → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦' ̇
 (x , px) Σ⊑ (y , py) = Σ x⊑y ꞉ x ⊑[ A ] y , Q px py x⊑y

 Σ⊑-to-⊑ : {x y : Σ P} → x Σ⊑ y → pr₁ x ⊑[ A ] pr₁ y
 Σ⊑-to-⊑ = pr₁

 -- FIXME: This is in general not a prop, while the name suggests it is
 is-Q-directed : {I : 𝓥 ̇ } (α : I → A ⊥) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓦' ̇
 is-Q-directed {I} α =
  ∥ I ∥ ×
  (Σ p ꞉ ((i : I) → P (α i)),
    is-semidirected _Σ⊑_ (λ i → α i , p i))

 inhabited-if-Q-directed : {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-Q-directed α) → ∥ I ∥
 inhabited-if-Q-directed = pr₁

 P-if-Q-directed : {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-Q-directed α) (i : I) → P (α i)
 P-if-Q-directed = pr₁ ∘ pr₂

 semidirected-if-Q-directed : {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-Q-directed α)
                            → is-semidirected _Σ⊑_ (λ i → α i , P-if-Q-directed δ i)
 semidirected-if-Q-directed = pr₂ ∘ pr₂

 Q-directed-if-Σ⊑-directed : {I : 𝓥 ̇ } {α : I → Σ P} (δ : is-directed _Σ⊑_ α)
                           → is-Q-directed (pr₁ ∘ α)
 Q-directed-if-Σ⊑-directed {α = α} δ =
  inhabited-if-directed _Σ⊑_ α δ ,
  pr₂ ∘ α ,
  semidirected-if-directed _Σ⊑_ α δ

 ⊑-semidirected-if-Q-directed : {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-Q-directed α)
                              → is-semidirected (Leq A) α
 ⊑-semidirected-if-Q-directed {α = α} δ i j = ∥∥-functor γ (semidirected-if-Q-directed δ i j)
  where
   γ : Σ (λ k → (α i , P-if-Q-directed δ i) Σ⊑ (α k , P-if-Q-directed δ k) ×
                (α j , P-if-Q-directed δ j) Σ⊑ (α k , P-if-Q-directed δ k))
     → Σ (λ k → α i ⊑[ A ] α k × α j ⊑[ A ] α k)
   γ (k , iΣ⊑k , jΣ⊑k) = k , Σ⊑-to-⊑ iΣ⊑k , Σ⊑-to-⊑ jΣ⊑k

 ⊑-directed-if-Q-directed : {I : 𝓥 ̇ } {α : I → A ⊥} (δ : is-Q-directed α)
                          → is-directed (Leq A) α
 ⊑-directed-if-Q-directed δ =
  inhabited-if-Q-directed δ , ⊑-semidirected-if-Q-directed δ

 ⊑-directed-if-Σ⊑-directed : {I : 𝓥 ̇ } {α : I → Σ P} (δ : is-directed _Σ⊑_ α)
                           → is-directed (Leq A) (pr₁ ∘ α)
 ⊑-directed-if-Σ⊑-directed = ⊑-directed-if-Q-directed ∘ Q-directed-if-Σ⊑-directed

 record ElimArgs : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓦' ̇  where
  field
   P-set-valued : (x : A ⊥) → is-set (P x)
   P-bot        : P bot
   P-incl       : (a : A) → P (incl a)
   P-lub        : {I : 𝓥 ̇ } (α : I → A ⊥) (δ : is-Q-directed α)
                → P (lub (α , ⊑-directed-if-Q-directed δ))

   Q-prop-valued : {x y : A ⊥} (px : P x) (py : P y) (x⊑y : x ⊑[ A ] y)
                 → is-prop (Q px py x⊑y)
   Q-refl        : {x : A ⊥} (px : P x) → Q px px (Leq-refl x)
   Q-trans       : {x y z : A ⊥} (px : P x) (py : P y) (pz : P z)
                 → (x⊑y : x ⊑[ A ] y) (y⊑z : y ⊑[ A ] z)
                 → Q px py x⊑y
                 → Q py pz y⊑z
                 → Q px pz (Leq-trans x y z x⊑y y⊑z)
   -- FIXME: In Cubical, we probably want to use a PathOver instead of the transport
   Q-anti-sym    : {x y : A ⊥} (px : P x) (py : P y)
                 → (x⊑y : x ⊑[ A ] y) (y⊑x : y ⊑[ A ] x)
                 → Q px py x⊑y
                 → Q py px y⊑x
                 → transport P (Leq-anti-sym x y x⊑y y⊑x) px ＝ py
   Q-bot         : {x : A ⊥} → (p : P x) → Q P-bot p (bot-leq x)
   Q-upperbound  : {I : 𝓥 ̇ } (α : I → A ⊥) (δ : is-Q-directed α)
                 → (i : I) → Q (P-if-Q-directed δ i)
                               (P-lub α δ)
                               (lub-is-upperbound (⊑-directed-if-Q-directed δ) i)
   Q-lowerbound-of-upperbounds
                 : {I : 𝓥 ̇ } (α : I → A ⊥) (δ : is-Q-directed α)
                 → (v : A ⊥) (v-upper : (i : I) → α i ⊑[ A ] v) (pv : P v)
                 → Q (P-lub α δ)
                     pv
                     (lub-is-lowerbound-of-upperbounds (⊑-directed-if-Q-directed δ) v v-upper)

 record Eliminator (args : ElimArgs) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓦' ̇  where
  open ElimArgs args

  field
   ⊥-elim : (x : A ⊥) → P x
   ⊑-elim : {x y : A ⊥} (x⊑y : x ⊑[ A ] y) → Q (⊥-elim x) (⊥-elim y) x⊑y

   ⊥-elim-β-bot  : ⊥-elim bot ＝ P-bot
   ⊥-elim-β-incl : (a : A) → ⊥-elim (incl a) ＝ P-incl a
   ⊥-elim-β-lub  : {I : 𝓥 ̇ } (α : I → A ⊥) (δ : is-Q-directed α)
                 → ⊥-elim (lub (α , ⊑-directed-if-Q-directed δ)) ＝ P-lub α δ
  -- The following rule isn't needed as we already know that Q is a set.
  -- Furthermore, it probably also doesn't hold, it we do not use the REWRITE pragmas
  -- for the above computation rules.
  --  ⊥-elim-β-anti-sym : {x y : A ⊥} (px : P x) (py : P y)
  --                    → (x⊑y : x ⊑[ A ] y) (y⊑x : y ⊑[ A ] x)
  --                    → (qxy : Q px py x⊑y) (qyx : Q py px y⊑x)
  --                    → apd ⊥-elim (Leq-anti-sym x y x⊑y y⊑x)
  --                    ＝ Q-anti-sym (⊥-elim x) (⊥-elim y) x⊑y y⊑x (⊑-elim x⊑y) (⊑-elim y⊑x)

 ⊥-elim : (args : ElimArgs) → Eliminator args
 ⊥-elim args = record
  { ⊥-elim = f
  ; ⊑-elim = f-monotone
  ; ⊥-elim-β-bot = β-bot
  ; ⊥-elim-β-incl = β-incl
  ; ⊥-elim-β-lub = β-lub }
  where
   open ElimArgs args

   Σ⊑-PosetAxioms : PosetAxioms.poset-axioms _Σ⊑_
   Σ⊑-PosetAxioms =
    Σ-is-set ⊥-is-set P-set-valued ,
    (λ (x , px) (y , py) → Σ-is-prop (Leq-is-prop-valued x y) (Q-prop-valued px py)) ,
    (λ (x , px) → Leq-refl x , Q-refl px) ,
    (λ (x , px) (y , py) (z , pz) (x⊑y , qxy) (y⊑z , qyz) → Leq-trans x y z x⊑y y⊑z , Q-trans px py pz x⊑y y⊑z qxy qyz) ,
    (λ (x , px) (y , py) (x⊑y , qxy) (y⊑x , qyx) → to-Σ-＝ (Leq-anti-sym x y x⊑y y⊑x , Q-anti-sym px py x⊑y y⊑x qxy qyx))

   Σ-lub : {I : 𝓥 ̇ } {α : I → Σ P} (δ : is-directed _Σ⊑_ α) → Σ P
   Σ-lub {α = α} δ =
    lub (pr₁ ∘ α , ⊑-directed-if-Σ⊑-directed δ) ,
    P-lub (pr₁ ∘ α) (Q-directed-if-Σ⊑-directed δ)

   Σ⊑-directed-completeness : is-directed-complete _Σ⊑_
   Σ⊑-directed-completeness I α δ =
    Σ-lub δ ,
    Σ-lub-is-upperbound ,
    Σ-lub-is-lowerbound-of-upperbounds
    where
     Σ-lub-is-upperbound : is-upperbound _Σ⊑_ (Σ-lub δ) α
     Σ-lub-is-upperbound i =
      lub-is-upperbound (⊑-directed-if-Σ⊑-directed δ) i ,
      Q-upperbound (pr₁ ∘ α) (Q-directed-if-Σ⊑-directed δ) i

     Σ-lub-is-lowerbound-of-upperbounds : is-lowerbound-of-upperbounds _Σ⊑_ (Σ-lub δ) α
     Σ-lub-is-lowerbound-of-upperbounds (v , pv) v-upperbound =
      lub-is-lowerbound-of-upperbounds (⊑-directed-if-Σ⊑-directed δ) v
       (λ i → Σ⊑-to-⊑ (v-upperbound i)) ,
      Q-lowerbound-of-upperbounds (pr₁ ∘ α) (Q-directed-if-Σ⊑-directed δ)
       v (λ i → Σ⊑-to-⊑ (v-upperbound i)) pv

   𝓓 : DCPO {𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦'}
   𝓓 = Σ P , _Σ⊑_ , Σ⊑-PosetAxioms , Σ⊑-directed-completeness

   Z : DPartOb A (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦) (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦')
   Z = record { 𝓓 = 𝓓 ,
                    (bot , P-bot) ,
                    (λ (y , py) → bot-leq y , Q-bot py)
              ; η = λ a → incl a , P-incl a }     

   module Z = DPartOb Z

   pr₁-as-DPartHom : DPartHom Z (Lift-as-DPart A)
   pr₁-as-DPartHom = (pr₁ , pr₁-continious) , refl , λ _ → refl
    where
     pr₁-continious : is-continuous (Z.𝓓 ⁻) (Lift-as-DCPO A) pr₁
     pr₁-continious I α δ = lub-is-sup (⊑-directed-if-Σ⊑-directed δ)

   ! : DPartHom (Lift-as-DPart A) Z
   ! = center (⊥-initial Z)

   id' : DPartHom (Lift-as-DPart A) (Lift-as-DPart A)
   id' = DPartComp (Lift-as-DPart A) Z (Lift-as-DPart A) ! pr₁-as-DPartHom

   id'＝id : DPart[ Lift-as-DPart A , Lift-as-DPart A ]⟨ id' ⟩ ＝ id
   id'＝id = ap (DPart[ Lift-as-DPart A , Lift-as-DPart A ]⟨_⟩) γ
    where
     γ : DPartComp (Lift-as-DPart A) Z (Lift-as-DPart A) ! pr₁-as-DPartHom
      ＝ DPartId (Lift-as-DPart A)
     γ = singletons-are-props (⊥-initial (Lift-as-DPart A)) _ _

   f : (x : A ⊥) → P x
   f x = transport P (happly id'＝id x) (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x))

   f-β : {x : A ⊥} {p : P x}
       → DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x ＝ x , p
       → f x ＝ p
   f-β {x} {p} !x =
    f x
      ＝⟨ refl ⟩
    transport P (happly id'＝id x) (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x))
      ＝⟨ ap (λ q → transport P q (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x)))
          (⊥-is-set (happly id'＝id x) (ap pr₁ !x)) ⟩
    transport P (ap pr₁ !x) (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x))
      ＝⟨ from-Σ-＝' !x ⟩
    p ∎

   β-bot : f bot ＝ P-bot
   β-bot = f-β (strictness (Lift-as-DPart A) Z !)

   β-incl : (a : A) → f (incl a) ＝ P-incl a
   β-incl a = f-β (η-preservation (Lift-as-DPart A) Z ! a)

   β-lub : {I : 𝓥 ̇ } (α : I → A ⊥) (δ : is-Q-directed α)
         → f (lub (α , ⊑-directed-if-Q-directed δ)) ＝ P-lub α δ
   β-lub α δ =
    f-β (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (lub (α , ⊑-directed-if-Q-directed δ))
           ＝⟨ continuous-∐-＝ (Lift-as-DCPO A) (Z.𝓓 ⁻) (underlying-scott-continuous-map (Lift-as-DPart A) Z !) (⊑-directed-if-Q-directed δ) ⟩
         Σ-lub (image-is-directed' (Lift-as-DCPO A) (Z.𝓓 ⁻) (underlying-scott-continuous-map (Lift-as-DPart A) Z !) (⊑-directed-if-Q-directed δ))
           ＝⟨ refl ⟩
         lub ((λ i → pr₁ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (α i))) ,
              ⊑-directed-if-Σ⊑-directed (image-is-directed' (Lift-as-DCPO A) (Z.𝓓 ⁻)
               (underlying-scott-continuous-map (Lift-as-DPart A) Z !)
               (⊑-directed-if-Q-directed δ))) ,
         P-lub (λ i → pr₁ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (α i)))
               (Q-directed-if-Σ⊑-directed (image-is-directed' (Lift-as-DCPO A) (Z.𝓓 ⁻)
               (underlying-scott-continuous-map (Lift-as-DPart A) Z !)
               (⊑-directed-if-Q-directed δ)))
           ＝⟨ to-Σ-＝ (ap lub lem2 , lem3) ⟩
         lub (α , ⊑-directed-if-Q-directed δ) , P-lub α δ ∎)
    where
     lem1 : (λ i → pr₁ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (α i))) ＝ α
     lem1 = ap (_∘ α) id'＝id

     lem2 : ((λ i → pr₁ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (α i))) ,
             ⊑-directed-if-Σ⊑-directed
              (image-is-directed' (Lift-as-DCPO A) (Z.𝓓 ⁻)
                (underlying-scott-continuous-map (Lift-as-DPart A) Z !)
                (⊑-directed-if-Q-directed δ)))
          ＝ (α , ⊑-directed-if-Q-directed δ)
     lem2 = to-Σ-＝ (lem1 , being-directed-is-prop (Leq A) α _ _)

     lem3 : transport P (ap lub lem2)
             (P-lub
              (λ i → pr₁ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (α i)))
              (Q-directed-if-Σ⊑-directed
               (image-is-directed' (Lift-as-DCPO A) 𝓓
                (underlying-scott-continuous-map (Lift-as-DPart A) Z !)
                (⊑-directed-if-Q-directed δ))))
          ＝ P-lub α δ
     lem3 = transport P (ap lub lem2)
             (P-lub
              (λ i → pr₁ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (α i)))
              (Q-directed-if-Σ⊑-directed
               (image-is-directed' (Lift-as-DCPO A) 𝓓
                (underlying-scott-continuous-map (Lift-as-DPart A) Z !)
                (⊑-directed-if-Q-directed δ))))
              ＝⟨ transport-ap P lub lem2 ⁻¹ ⟩
            transport (P ∘ lub) lem2
             (P-lub
              (λ i → pr₁ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ (α i)))
              (Q-directed-if-Σ⊑-directed
               (image-is-directed' (Lift-as-DCPO A) 𝓓
                (underlying-scott-continuous-map (Lift-as-DPart A) Z !)
                (⊑-directed-if-Q-directed δ))))
              ＝⟨ {!   !} ⟩
            P-lub α δ ∎

   f-monotone : {x y : A ⊥} (x⊑y : x ⊑[ A ] y) → Q (f x) (f y) x⊑y
   f-monotone {x} {y} x⊑y = {! Q-prop-valued (f x) (f y) x⊑y ?  !}
    where
    --  test : Q (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x))
    --           (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ y))
    --           (pr₁ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y))
    --  test = pr₂ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y)

    --  test1 : Q (transport⁻¹ P (happly id'＝id x) (f x))
    --            (transport⁻¹ P (happly id'＝id y) (f y))
    --            (transport₂⁻¹ (Leq A) (happly id'＝id x) (happly id'＝id y) x⊑y)
    --  test1 = transport₃ Q (forth-and-back-transport (happly id'＝id x) ⁻¹)
    --                       (forth-and-back-transport (happly id'＝id y) ⁻¹)
    --                       (Leq-is-prop-valued _ _ _ _)
    --                       test

    --  test2 : Q {!   !}
    --            {!   !}
    --            {!   !}
    --  test2 = transport₃ Q {! happly id'＝id x  !} {!   !} {!   !} test

     Q' : (Σ xy ꞉ A ⊥ × A ⊥ , P (pr₁ xy) × P (pr₂ xy) × pr₁ xy ⊑[ A ] pr₂ xy) → 𝓦' ̇
     Q' (_ , px , py , x⊑y) = Q px py x⊑y

     term1 : Q (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x))
               (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ y))
               (pr₁ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y))
     term1 = pr₂ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y)

    --  lem = transport
    --         (λ xy → P (pr₁ xy) × P (pr₂ xy) × Leq A (pr₁ xy) (pr₂ xy))
    --         (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))
    --         ( pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x)
    --         , pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ y)
    --         , pr₁ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y))
           
    --        ＝⟨ ? ⟩
          
    --        (f x , f y , x⊑y) ∎

     term2 : Q (f x) (f y) x⊑y
     term2 = transport Q' (to-Σ-＝ (ap₂ _,_ (happly id'＝id x) (happly id'＝id y) ,
      (transport
        (λ xy → P (pr₁ xy) × P (pr₂ xy) × Leq A (pr₁ xy) (pr₂ xy))
        (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))
        (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x) ,
         pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ y) ,
         pr₁ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y))
    
      ＝⟨ transport-× (λ xy → P (pr₁ xy)) (λ xy → P (pr₂ xy) × Leq A (pr₁ xy) (pr₂ xy)) (ap₂ _,_ (happly id'＝id x) (happly id'＝id y)) ⟩

      transport (λ xy → P (pr₁ xy))
       (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))
       (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x)) ,
      transport (λ xy → P (pr₂ xy) × Leq A (pr₁ xy) (pr₂ xy))
       (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))
       (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ y) ,
        pr₁ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y))

      ＝⟨ ap₂ _,_ refl (transport-× (λ xy → P (pr₂ xy)) (λ xy → Leq A (pr₁ xy) (pr₂ xy)) (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))) ⟩

      -- transport (λ xy → P (pr₁ xy))
      --  (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))
      --  (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ x)) ,
      -- transport (λ xy → P (pr₂ xy))
      --  (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))
      --  (pr₂ (DPart[ Lift-as-DPart A , Z ]⟨ ! ⟩ y)) ,
      -- transport (λ xy → Leq A (pr₁ xy) (pr₂ xy))
      --  (ap₂ _,_ (happly id'＝id x) (happly id'＝id y))
      --  (pr₁ (monotonicity-of-DPartHom (Lift-as-DPart A) Z ! x y x⊑y))
      -- If we fill theese, Agda will loop...
      ? , ? , ?

      ＝⟨ {!   !} ⟩

      {!   !} ∎)
      )) term1

\end{code}
  