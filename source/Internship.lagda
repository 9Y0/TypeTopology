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
 ({I : 𝓥 ̇ } {α : I → X} (p : is-directed _⊑_ α) → is-sup _⊑_ (∐ (α , p)) α)

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
        (λ (α , p) → ∐ (𝓓 ⁻) p) ,
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
    𝓓 = X , _⊑ₓ_ , pa , (λ I α p → ∐ₓ (α , p) , ∐ₓ-is-sup p)

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

 -- FIXME: Perhaps not use a record here...
 record DPartHom (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
        : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦₁ ⊔ 𝓦₂ ⊔ 𝓣₁ ⊔ 𝓣₂ ̇  where
  constructor make-DPartHom
 
  module X = DPartOb X
  module Y = DPartOb Y

  field
   f : DCPO⊥[ X.𝓓 , Y.𝓓 ]
--    FIXME: Use is-strict here
   f-strict : [ X.𝓓 ⁻ , Y.𝓓 ⁻ ]⟨ f ⟩ (least X.𝓓) ＝ least Y.𝓓
--    FIXME: Perhaps require a homotopy, as we already have fun-ext
   f-η : [ X.𝓓 ⁻ , Y.𝓓 ⁻ ]⟨ f ⟩ ∘ X.η ＝ Y.η

 DPart[_,_]⟨_⟩ : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
               → let module X = DPartOb X
                     module Y = DPartOb Y
              in (f : DPartHom X Y) → ⟪ X.𝓓 ⟫ → ⟪ Y.𝓓 ⟫
 DPart[ X , Y ]⟨ f ⟩ = pr₁ f.f
  where
   module X = DPartOb X
   module Y = DPartOb Y
   module f = DPartHom f

 continuity-of-DPartHom : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                          (f : DPartHom X Y)
                        → let module X = DPartOb X
                              module Y = DPartOb Y
                       in is-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) DPart[ X , Y ]⟨ f ⟩
 continuity-of-DPartHom X Y f = continuity-of-function (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f
  where
   module X = DPartOb X
   module Y = DPartOb Y
   module f = DPartHom f

 DPartHom＝ : {X : DPartOb A 𝓦₁ 𝓣₁} {Y : DPartOb A 𝓦₂ 𝓣₂} {f g : DPartHom X Y}
            → DPart[ X , Y ]⟨ f ⟩ ＝ DPart[ X , Y ]⟨ g ⟩
            → f ＝ g
 DPartHom＝ {X} {Y} {f} {g} refl = {! apd  !}
  where
   module X = DPartOb X
   module Y = DPartOb Y
   module f = DPartHom f
   module g = DPartHom g

   p : f.f ＝ g.f
   p = to-Σ-＝
        (refl ,
         being-continuous-is-prop (X.𝓓 ⁻) (Y.𝓓 ⁻)
          (DPart[ X , Y ]⟨ f ⟩) _ _)

   q : f.f-strict ＝ g.f-strict
   q = sethood (Y.𝓓 ⁻) _ _

   r : f.f-η ＝ g.f-η
   r = Π-is-set fe (λ _ → sethood (Y.𝓓 ⁻)) _ _

   -- FIXME: Cannot match p as refl fsr
   γ : f.f ＝ g.f
     → f.f-strict ＝ g.f-strict
     → f.f-η ＝ g.f-η
     → _ ＝ _
   γ p refl refl = {! p !}

\end{code}

DPartHom is equivalent to the Sigma type corresponding to the one given in [1].
We use this to prove that DPartHom is a set.

\begin{code}

 image-is-directed-if-monotone : {I : 𝓥 ̇ } {X : 𝓦₁ ̇ } {H : 𝓦₂ ̇ } {α : I → X} {f : X → H}
                               → (_⊑ₓ_ : X → X → 𝓣₁ ̇ ) (_⊑ₕ_ : H → H → 𝓣₂ ̇ )
                               → (f⊑ : (x₁ x₂ : X) → x₁ ⊑ₓ x₂ → f x₁ ⊑ₕ f x₂)
                               → (p : is-directed _⊑ₓ_ α)
                               → is-directed _⊑ₕ_ (f ∘ α)
 image-is-directed-if-monotone {α = α} _⊑ₓ_ _⊑ₕ_ f⊑ p =
  inhabited-if-directed _⊑ₓ_ α p ,
  λ i j → ∥∥-functor
           (λ (k , αᵢ⊑αₖ , αⱼ⊑αₖ) → k , f⊑ _ _ αᵢ⊑αₖ , f⊑ _ _ αⱼ⊑αₖ)
           (semidirected-if-directed _⊑ₓ_ α p i j)

 DPartHom' : DPartOb' A 𝓦₁ 𝓣₁  → DPartOb' A 𝓦₂ 𝓣₂ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦₁ ⊔ 𝓦₂ ⊔ 𝓣₁ ⊔ 𝓣₂ ̇
 DPartHom' (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , _) (H , _⊑ₕ_ , ⊥ₕ , ηₕ , ∐ₕ , _) =
  Σ f ꞉ (X → H) ,
  Σ f⊑ ꞉ ((x₁ x₂ : X) → x₁ ⊑ₓ x₂ → f x₁ ⊑ₕ f x₂) ,
   (f ⊥ₓ ＝ ⊥ₕ) ×
   (f ∘ ηₓ ＝ ηₕ) ×
   ({I : 𝓥 ̇ } (α : I → X) (p : is-directed _⊑ₓ_ α) →
    f (∐ₓ (α , p)) ＝ ∐ₕ (f ∘ α , image-is-directed-if-monotone _⊑ₓ_ _⊑ₕ_ f⊑ p))

 DPartHom≃DPartHom' : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                    → DPartHom X Y
                    ≃ DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y)
 DPartHom≃DPartHom' X Y = qinveq ψ (ϕ , ϕψ , ψϕ)
  where
   module X = DPartOb X
   module Y = DPartOb Y

   ψ : DPartHom X Y → DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y)
   ψ f = DPart[ X , Y ]⟨ f ⟩ ,
         monotone-if-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f ,
         f.f-strict ,
         f.f-η ,
         γ
    where
     module f = DPartHom f
    
     γ : {I : 𝓥 ̇ } (α : I → ⟪ X.𝓓 ⟫) (p : is-Directed (X.𝓓 ⁻) α)
       → DPart[ X , Y ]⟨ f ⟩ (∐ (X.𝓓 ⁻) p)
       ＝ ∐ (Y.𝓓 ⁻) (image-is-directed' (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f p)
     γ α p = continuous-∐-＝ (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f p

   ϕ : DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y) → DPartHom X Y
   ϕ (f , f⊑ , f⊥ , fη , f∐) =
    record
     { f = f ,
           λ I α δ →
            transport⁻¹ (λ y → is-sup (underlying-order⊥ Y.𝓓) y (f ∘ α))
             (f∐ α δ)
             (∐-is-sup (Y.𝓓 ⁻) _)
     ; f-strict = f⊥
     ; f-η = fη }

   ϕψ : ϕ ∘ ψ ∼ id
   ϕψ f = DPartHom＝ refl
    where
     module f = DPartHom f

   ψϕ : ψ ∘ ϕ ∼ id
   ψϕ (f , f⊑ , f⊥ , fη , f∐) =
    to-subtype-＝
     (λ f →
       Σ-is-prop
        (Π₃-is-prop fe (λ x₁ x₂ x₁⊑x₂ → prop-valuedness (Y.𝓓 ⁻) (f x₁) (f x₂)))
        (λ f⊑ →
          ×₃-is-prop
           (sethood (Y.𝓓 ⁻))
           (Π-is-set fe (λ a → sethood (Y.𝓓 ⁻)))
           (Π-is-prop' fe (λ I → Π₂-is-prop fe (λ α p → sethood (Y.𝓓 ⁻))))))
     refl

 DPartHom'-is-set : (X : DPartOb' A 𝓦₁ 𝓣₁) (H : DPartOb' A 𝓦₂ 𝓣₂)
                  → is-set (DPartHom' X H)
 DPartHom'-is-set (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , paₓ , ⊥ₓ-is-least , ∐ₓ-is-sup)
                  (H , _⊑ₕ_ , ⊥ₕ , ηₕ , ∐ₕ , paₕ , ⊥ₕ-is-least , ∐ₕ-is-sup) =
  Σ-is-set
   (Π-is-set fe (λ _ → H-is-set))
   λ f →
    props-are-sets
     (Σ-is-prop
      (Π₃-is-prop fe (λ x₁ x₂ x₁⊑x₂ → pr₁ (pr₂ paₕ) (f x₁) (f x₂)))
      λ f⊑ →
       ×₃-is-prop
        H-is-set
        (Π-is-set fe (λ _ → H-is-set))
        (Π-is-prop' fe (λ _ → Π₂-is-prop fe (λ _ _ → H-is-set))))
  where
   H-is-set : is-set H
   H-is-set = pr₁ paₕ

   ⊑ₕ-prop-valued : PosetAxioms.is-prop-valued _⊑ₕ_
   ⊑ₕ-prop-valued = pr₁ (pr₂ paₕ)

 DPartHom-is-set : (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂)
                 → is-set (DPartHom X Y)
 DPartHom-is-set X Y =
  equiv-to-set
   (DPartHom≃DPartHom' X Y)
   (DPartHom'-is-set (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y))

\end{code}

\begin{code}

DPartId : {A : 𝓤 ̇ } (X : DPartOb A 𝓦 𝓣) → DPartHom X X
DPartId X =
 record
  { f = id , λ I α → ∐-is-sup (𝓓 ⁻)
  ; f-strict = refl
  ; f-η = refl }
 where
  open DPartOb X

DPartComp : {A : 𝓤 ̇ } {𝓦₁ 𝓦₂ 𝓦₃ 𝓣₁ 𝓣₂ 𝓣₃ : Universe}
            (X : DPartOb A 𝓦₁ 𝓣₁) (Y : DPartOb A 𝓦₂ 𝓣₂) (Z : DPartOb A 𝓦₃ 𝓣₃)
          → DPartHom X Y → DPartHom Y Z → DPartHom X Z
DPartComp X Y Z f g =
 record
  { f = DCPO-∘ (X.𝓓 ⁻) (Y.𝓓 ⁻) (Z.𝓓 ⁻) f.f g.f
  ; f-strict = ap DPart[ Y , Z ]⟨ g ⟩ f.f-strict ∙ g.f-strict
  ; f-η = ap (DPart[ Y , Z ]⟨ g ⟩ ∘_) f.f-η ∙ g.f-η }
 where
  module f = DPartHom f
  module g = DPartHom g
  module X = DPartOb X
  module Y = DPartOb Y
  module Z = DPartOb Z

DPartPre : (A : 𝓤 ̇ ) (𝓦 𝓣 : Universe)
         → precategory (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺) (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓣)
DPartPre A 𝓦 𝓣 =
 make
  (DPartOb A 𝓦 𝓣 , DPartHom , DPartId , DPartComp)
  (DPartHom-is-set ,
   (λ X Y f → DPartHom＝ refl) ,
   (λ X Y f → DPartHom＝ refl) ,
   λ X Y Z W f g h → DPartHom＝ refl)

\end{code}

We now consider the QIIT from [1] adapted to a DCPO setting.

\begin{code}

data _⊥ (A : 𝓤 ̇ ) : 𝓥 ⁺ ⊔ 𝓤 ̇
data Leq (A : 𝓤 ̇ ) : A ⊥ → A ⊥ → 𝓥 ⁺ ⊔ 𝓤 ̇ 

-- This definition gives a specified index k s.t. αᵢ ⊑ αₖ, αⱼ ⊑ αₖ instead of an
-- unspecified index k. Using this definition Leq A , A ⊥ become strictly
-- positive, but it's definitly not the definition we want.
wrong-is-directed : {I : 𝓥 ̇ } {X : 𝓦' ̇ } → (_⊑_ : X → X → 𝓣 ̇ ) → (I → X) → 𝓥 ⊔ 𝓣 ̇
wrong-is-directed {I = I} _⊑_ α =
 ∥ I ∥ ×
 ((i j : I) → Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k))

data _⊥ A where
 incl : A → A ⊥
 bot : A ⊥
 lub : {I : 𝓥 ̇ } → (Σ α ꞉ (I → A ⊥) , wrong-is-directed (Leq A) α) → A ⊥

postulate
 ⊥-is-set : {A : 𝓤 ̇ } → is-set (A ⊥)

data Leq A where
 Leq-refl : (x : A ⊥) → Leq A x x
 Leq-trans : (x y z : A ⊥) → Leq A x y → Leq A y z → Leq A x z
 bot-leq : (x : A ⊥) → Leq A bot x
 -- FIXME: If we figure out what to do with wrong-is-directed, it would be
 --        better to replace these two constructors with a single is-sup constr
 lub-upperbound : {I : 𝓥 ̇ } {α : I → A ⊥} (p : wrong-is-directed (Leq A) α)
                  (i : I) → Leq A (α i) (lub (α , p))
 lub-lowest : {I : 𝓥 ̇ } {α : I → A ⊥} (p : wrong-is-directed (Leq A) α) (v : A ⊥)
            → ((i : I) → Leq A (α i) v)
            → Leq A (lub (α , p)) v

-- FIXME: This is very close to the x ⊑⟨ 𝓓 ⟩ y syntax of DCPOs, probably not a good idea...
syntax Leq A x y = x ⊑[ A ] y            

postulate
 Leq-is-prop-valued : {A : 𝓤 ̇ } (x y : A ⊥) → is-prop (x ⊑[ A ] y)
 Leq-anti-sym : {A : 𝓤 ̇ } (x y : A ⊥) → x ⊑[ A ] y → y ⊑[ A ] x → x ＝ y

 -- FIXME: We cannot prove directed completeness, as we used the wrong notion
 -- of being directed.
Lift-as-DCPO : (A : 𝓤 ̇ ) → DCPO
Lift-as-DCPO A = A ⊥ , Leq A , pa , {!   !}
 where
  pa : PosetAxioms.poset-axioms (Leq A)
  pa = ⊥-is-set , Leq-is-prop-valued , Leq-refl , Leq-trans , Leq-anti-sym

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
 ⊥-elim : {A : 𝓤 ̇ } (X : DPartOb A 𝓦 𝓣)
        → is-singleton (DPartHom (Lift-as-DPart A) X)

-- Is prop valued hier nodig?
⊥-induction : {A : 𝓤 ̇ } {P : A ⊥ → 𝓦 ̇ }
            → ((x : A ⊥) → is-prop (P x))
            → P bot
            → ((a : A) → P (incl a))
            → ({I : 𝓥 ̇ } (α : I → A ⊥) (p : wrong-is-directed (Leq A) α)
              → ((i : I) → P (α i))
              → P (lub (α , p)))
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
         -- FIXME: We cannot prove these, as we used wrong-is-directed
         (lub (pr₁ ∘ α , {!   !}) , P-lub (pr₁ ∘ α) {!   !} (pr₂ ∘ α)) ,
         lub-upperbound {!   !} ,
         λ v → lub-lowest {!   !} (pr₁ v)

  module Z = DPartOb Z

  pr₁-as-DPartHom : DPartHom Z (Lift-as-DPart A)
  pr₁-as-DPartHom = record { f = pr₁ , pr₁-continious ; f-strict = refl ; f-η = refl }
   where
    -- FIXME: We cannot prove these, as we used wrong-is-directed
    pr₁-continious : is-continuous (Z.𝓓 ⁻) (Lift-as-DCPO A) pr₁
    pr₁-continious I α δ = lub-upperbound {!   !} , lub-lowest {!   !}

  f : DPartHom (Lift-as-DPart A) Z
  f = center (⊥-elim Z)

  pr₁∘f : pr₁ ∘ DPart[ Lift-as-DPart A , Z ]⟨ f ⟩ ＝ id
  pr₁∘f = ap (DPart[ Lift-as-DPart A , Lift-as-DPart A ]⟨_⟩) γ
   where
    γ : DPartComp _ _ _ f pr₁-as-DPartHom ＝ DPartId (Lift-as-DPart A)
    γ = singletons-are-props (⊥-elim (Lift-as-DPart A))
            (DPartComp _ _ _ f pr₁-as-DPartHom)
            (DPartId (Lift-as-DPart A))

\end{code}
